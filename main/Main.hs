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

type CheckOptColorize = Bool

type Line = Integer

type Column = Integer

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
  | Check CheckOptInputPath CheckOptColorize (Maybe CheckOptEndOfEntry)
  | Complete FilePath Line Column

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
  let colorizeOpt =
        flag True False $
        mconcat
          [ long "no-color"
          , help "Set this to disable colorization of the output"
          ]
  let footerOpt =
        optional $
        strOption $
        mconcat
          [ long "end-of-entry"
          , help "String printed after each entry"
          , metavar "STRING"
          ]
  Check <$> inputPathOpt <*> colorizeOpt <*> footerOpt

parseCompleteOpt :: Parser Command
parseCompleteOpt = do
  let inputPathOpt =
        argument str $ mconcat [metavar "INPUT", help "The path of input file"]
  let lineOpt = argument auto $ mconcat [help "Line number", metavar "LINE"]
  let columnOpt =
        argument auto $ mconcat [help "Column number", metavar "COLUMN"]
  Complete <$> inputPathOpt <*> lineOpt <*> columnOpt

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
     (info (helper <*> parseCheckOpt) (progDesc "check specified file")) <>
   command
     "complete"
     (info (helper <*> parseCompleteOpt) (progDesc "show completion info")))

optParser :: ParserInfo Command
optParser = info (helper <*> parseOpt) fullDesc

main :: IO ()
main = execParser optParser >>= run

run :: Command -> IO ()
run (Build inputPathStr mOutputPathStr outputKind) = do
  inputPath <- resolveFile' inputPathStr
  resultOrErr <- evalWithEnv (build inputPath) (initialEnv inputPath True)
  basename <- setFileExtension "" $ filename inputPath
  mOutputPath <- mapM resolveFile' mOutputPathStr
  outputPath <- constructOutputPath basename mOutputPath outputKind
  case resultOrErr of
    Left err -> seqIO err >> exitWith (ExitFailure 1)
    Right result -> writeResult result outputPath outputKind
run (Check inputPathStr colorizeFlag mEndOfEntry) = do
  inputPath <- resolveFile' inputPathStr
  resultOrErr <-
    evalWithEnv (check inputPath) (initialEnv inputPath colorizeFlag)
  case resultOrErr of
    Right _ -> return ()
    Left err ->
      case mEndOfEntry of
        Just eoe -> seqIO' eoe err >> exitWith (ExitFailure 1)
        Nothing -> seqIO err >> exitWith (ExitFailure 1)
run (Complete inputPathStr l c) = do
  inputPath <- resolveFile' inputPathStr
  resultOrErr <-
    evalWithEnv (complete inputPath l c) (initialEnv inputPath True)
  case resultOrErr of
    Left _ -> return () -- don't show any errors, just quit silently
    -- Left err -> seqIO err >> exitWith (ExitFailure 1)
    Right result -> mapM_ putStrLn result

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
  parse inputPath >>= elaborate >>= toSNF >>= clarify >>= toLLVM >>= emit

check :: Path Abs File -> WithEnv ()
check inputPath = do
  _ <- parse inputPath >>= elaborate
  return ()

seqIO :: [IO ()] -> IO ()
seqIO [] = return ()
seqIO (a:as) = a >> seqIO as

seqIO' :: String -> [IO ()] -> IO ()
seqIO' _ [] = return ()
seqIO' eoe (a:as) = a >> putStrLn eoe >> seqIO' eoe as
