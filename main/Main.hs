{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Monad.State
import Options.Applicative
import Path
import Path.IO
import System.Exit
import System.Process
import Text.Read (readMaybe)

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import qualified Data.Text.IO as TIO

import Clarify
import Data.Env
import Elaborate
import Emit
import LLVM
import Parse

type ImportOptScreenName = String

type BuildOptInputPath = String

type BuildOptOutputPath = String

type CheckOptInputPath = String

type CheckOptEndOfEntry = String

data OutputKind
  = OutputKindObject
  | OutputKindLLVM
  deriving (Show)

instance Read OutputKind where
  readsPrec _ "object" = [(OutputKindObject, [])]
  readsPrec _ "llvm" = [(OutputKindLLVM, [])]
  readsPrec _ _ = []

data Command
  = Build BuildOptInputPath (Maybe BuildOptOutputPath) OutputKind
  | Check CheckOptInputPath (Maybe CheckOptEndOfEntry)

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

parseCheckOpt :: Parser Command
parseCheckOpt = do
  let inputPathOpt =
        argument str $ mconcat [metavar "INPUT", help "The path of input file"]
  let footerOpt =
        optional $
        strOption $
        mconcat
          [ long "end-of-entry"
          , help "String printed after each entry"
          , metavar "STRING"
          ]
  Check <$> inputPathOpt <*> footerOpt

kindReader :: ReadM OutputKind
kindReader = do
  s <- str
  case readMaybe s of
    Nothing -> readerError $ "unknown mode:" ++ s
    Just m -> return m

parseOpt :: Parser Command
parseOpt =
  subparser $
  (command
     "build"
     (info (helper <*> parseBuildOpt) (progDesc "build given file")) <>
   command
     "check"
     (info (helper <*> parseCheckOpt) (progDesc "check specified file")))

optParser :: ParserInfo Command
optParser = info (helper <*> parseOpt) fullDesc

main :: IO ()
main = execParser optParser >>= run

run :: Command -> IO ()
run (Build inputPathStr mOutputPathStr outputKind) = do
  inputPath <- resolveFile' inputPathStr
  resultOrErr <- evalWithEnv (build inputPath) (initialEnv inputPath)
  basename <- setFileExtension "" $ filename inputPath
  mOutputPath <- mapM resolveFile' mOutputPathStr
  outputPath <- constructOutputPath basename mOutputPath outputKind
  case resultOrErr of
    Left err -> seqIO err >> exitWith (ExitFailure 1)
    Right result -> writeResult result outputPath outputKind
run (Check inputPathStr mEndOfEntry) = do
  inputPath <- resolveFile' inputPathStr
  resultOrErr <- evalWithEnv (check inputPath) (initialEnv inputPath)
  case resultOrErr of
    Right _ -> return ()
    Left err ->
      case mEndOfEntry of
        Just eoe -> seqIO' eoe err >> exitWith (ExitFailure 1)
        Nothing -> seqIO err >> exitWith (ExitFailure 1)

-- printError :: String -> IO ()
-- printError err = do
--   liftIO $
--     setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
--   liftIO $ putStr "error: "
--   liftIO $ setSGR [Reset]
--   liftIO $ putStrLn $ err
constructOutputPath ::
     Path Rel File -> Maybe (Path Abs File) -> OutputKind -> IO (Path Abs File)
constructOutputPath basename Nothing OutputKindLLVM = do
  dir <- getCurrentDir
  (dir </> basename) <.> "ll"
constructOutputPath basename Nothing OutputKindObject = do
  dir <- getCurrentDir
  return $ dir </> basename
constructOutputPath _ (Just path) _ = return path

writeResult :: [B.ByteString] -> Path Abs File -> OutputKind -> IO ()
writeResult result outputPath OutputKindLLVM = do
  let content = BC.unlines result
  B.writeFile (toFilePath outputPath) content
writeResult result outputPath OutputKindObject = do
  let content = BC.unlines result
  tmpOutputPath <- liftIO $ outputPath <.> "ll"
  let tmpOutputPathStr = toFilePath tmpOutputPath
  B.writeFile tmpOutputPathStr content
  callProcess
    "clang"
    [tmpOutputPathStr, "-Wno-override-module", "-o" ++ toFilePath outputPath]
  removeFile tmpOutputPath

build :: Path Abs File -> WithEnv [B.ByteString]
build inputPath = do
  content <- liftIO $ TIO.readFile $ toFilePath inputPath
  let path = toFilePath inputPath
  parse content path >>= elaborate >>= clarify >>= toLLVM >>= emit

check :: Path Abs File -> WithEnv ()
check inputPath = do
  content <- liftIO $ TIO.readFile $ toFilePath inputPath
  _ <- parse content (toFilePath inputPath) >>= elaborate
  return ()

seqIO :: [IO ()] -> IO ()
seqIO [] = return ()
seqIO (a:as) = a >> seqIO as

seqIO' :: String -> [IO ()] -> IO ()
seqIO' _ [] = return ()
seqIO' eoe (a:as) = a >> putStrLn eoe >> seqIO' eoe as
