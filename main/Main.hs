module Main where

import Control.Monad.State
import Data.List (intercalate)
import Options.Applicative
import System.Directory
import System.FilePath
import System.Process
import Text.Read (readMaybe)

import Data.Env
import Elaborate
import Emit
import LLVM
import Parse
import Polarize

type ImportOptScreenName = String

type BuildOptInputPath = String

type BuildOptOutputPath = String

data OutputKind
  = OutputKindObject
  | OutputKindLLVM
  deriving (Show)

instance Read OutputKind where
  readsPrec _ "object" = [(OutputKindObject, [])]
  readsPrec _ "llvm" = [(OutputKindLLVM, [])]
  readsPrec _ _ = []

data Command =
  Build BuildOptInputPath (Maybe BuildOptOutputPath) OutputKind

parseBuildOpt :: Parser Command
parseBuildOpt = do
  let inputPathOpt =
        argument str $ mconcat [metavar "INPUT", help "The path of input file"]
  let outputPathOpt =
        optional $
        strOption $
        mconcat
          [ long "output"
          , short 'o'
          , metavar "OUTPUT"
          , help "The path of output file"
          ]
  let outputKindOpt =
        option kindReader $
        mconcat
          [ long "emit"
          , metavar "KIND"
          , value OutputKindObject
          , help "The type of output file"
          ]
  Build <$> inputPathOpt <*> outputPathOpt <*> outputKindOpt

kindReader :: ReadM OutputKind
kindReader = do
  s <- str
  case readMaybe s of
    Nothing -> readerError $ "unknown mode:" ++ s
    Just m -> return m

parseOpt :: Parser Command
parseOpt =
  subparser $
  command
    "build"
    (info
       (helper <*> parseBuildOpt)
       (progDesc "Usage: neut build FILENAME [OPTIONS]"))

optParser :: ParserInfo Command
optParser = info (helper <*> parseOpt) fullDesc

main :: IO ()
main = execParser optParser >>= run

run :: Command -> IO ()
run (Build inputPath moutputPath outputKind) = do
  content <- readFile inputPath
  dirPath <- expandDirPath $ takeDirectory inputPath
  resultOrErr <- evalWithEnv (process content) (initialEnv dirPath)
  let basename = takeBaseName inputPath
  outputPath <- constructOutputPath basename moutputPath outputKind
  case resultOrErr of
    Left err -> putStrLn err
    Right result -> writeResult result outputPath outputKind

constructOutputPath :: String -> Maybe FilePath -> OutputKind -> IO FilePath
constructOutputPath basename Nothing OutputKindLLVM = do
  dir <- getCurrentDirectory
  return $ dir </> (basename ++ ".ll")
constructOutputPath basename Nothing OutputKindObject = do
  dir <- getCurrentDirectory
  return $ dir </> basename
constructOutputPath _ (Just path) _ = return path

writeResult :: [String] -> FilePath -> OutputKind -> IO ()
writeResult result outputPath OutputKindLLVM = do
  let content = intercalate "\n" result
  writeFile outputPath content
writeResult result outputPath OutputKindObject = do
  let content = intercalate "\n" result
  let tmpOutputPath = outputPath ++ ".ll"
  let tmpAsmOutputPath = outputPath ++ ".s"
  writeFile tmpOutputPath content
  callProcess "llc" [tmpOutputPath, "-o=" ++ tmpAsmOutputPath]
  callProcess "clang" [tmpAsmOutputPath, "-o" ++ outputPath]
  removeFile tmpOutputPath
  removeFile tmpAsmOutputPath

expandDirPath :: FilePath -> IO FilePath
expandDirPath path = do
  current <- getCurrentDirectory
  return $ current </> path

process :: String -> WithEnv [String]
process input = do
  e <- (parse >=> elaborate) input
  p "elaborated"
  e' <- polarize e
  p "polarized"
  e'' <- toLLVM e'
  p "llvm-done"
  emit e''
   -- process input = do
   -- parse >=> elaborate >=> polarize >=> toLLVM >=> emit
