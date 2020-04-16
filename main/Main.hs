{-# LANGUAGE OverloadedStrings #-}

module Main
  ( main
  ) where

import Data.Time.Clock.POSIX

-- import Control.Monad.State
import Options.Applicative
import Path
import Path.IO
import System.Directory (listDirectory)
import System.Exit

-- import System.Process
import Text.Read (readMaybe)

import qualified Codec.Archive.Tar as Tar
import qualified Codec.Compression.GZip as GZip
import qualified Data.ByteString.Lazy as L

import Build
import Check
import Complete
import Data.Env
import Data.Log
import Parse

type BuildOptInputPath = String

type BuildOptOutputPath = String

type CheckOptInputPath = String

type CheckOptEndOfEntry = String

type CheckOptColorize = Bool

type ArchiveOptInputPath = String

type ArchiveOptOutputPath = String

type Line = Int

type Column = Int

data OutputKind
  = OutputKindObject
  | OutputKindLLVM
  | OutputKindAsm
  deriving (Show)

instance Read OutputKind where
  readsPrec _ "object" = [(OutputKindObject, [])]
  readsPrec _ "llvm" = [(OutputKindLLVM, [])]
  readsPrec _ "asm" = [(OutputKindAsm, [])]
  readsPrec _ _ = []

data Command
  = Build BuildOptInputPath (Maybe BuildOptOutputPath) OutputKind
  | Check CheckOptInputPath CheckOptColorize CheckOptEndOfEntry
  | Archive ArchiveOptInputPath (Maybe ArchiveOptOutputPath)
  | Complete FilePath Line Column

main :: IO ()
main = execParser (info (helper <*> parseOpt) fullDesc) >>= run

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
     "archive"
     (info
        (helper <*> parseArchiveOpt)
        (progDesc "create archive from given path")) <>
   command
     "complete"
     (info (helper <*> parseCompleteOpt) (progDesc "show completion info")))

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
        strOption $
        mconcat
          [ long "end-of-entry"
          , value ""
          , help "String printed after each entry"
          , metavar "STRING"
          ]
  Check <$> inputPathOpt <*> colorizeOpt <*> footerOpt

parseArchiveOpt :: Parser Command
parseArchiveOpt = do
  let inputPathOpt =
        argument str $
        mconcat [metavar "INPUT", help "The path of input directory"]
  let outputPathOpt =
        optional $
        strOption $
        mconcat
          [ long "output"
          , short 'o'
          , metavar "OUTPUT"
          , help "The path of output"
          ]
  Archive <$> inputPathOpt <*> outputPathOpt

parseCompleteOpt :: Parser Command
parseCompleteOpt = do
  let inputPathOpt =
        argument str $ mconcat [metavar "INPUT", help "The path of input file"]
  let lineOpt = argument auto $ mconcat [help "Line number", metavar "LINE"]
  let columnOpt =
        argument auto $ mconcat [help "Column number", metavar "COLUMN"]
  Complete <$> inputPathOpt <*> lineOpt <*> columnOpt

run :: Command -> IO ()
run (Build inputPathStr mOutputPathStr outputKind) = do
  inputPath <- resolveFile' inputPathStr
  time <- round <$> getPOSIXTime
  resultOrErr <-
    evalWithEnv (runBuild inputPath) $
    initialEnv {shouldColorize = True, endOfEntry = "", timestamp = time}
  basename <- replaceExtension "" $ filename inputPath
  mOutputPath <- mapM resolveFile' mOutputPathStr
  outputPath <- constructOutputPath basename mOutputPath outputKind
  case resultOrErr of
    Left err -> seqIO (map (outputLog True "") err) >> exitWith (ExitFailure 1)
    Right pathList -> link outputPath pathList []
      -- case outputKind of
      --   OutputKindObject -> link outputPath pathList []
      --   OutputKindLLVM -> link outputPath pathList ["-emit-llvm"]
      --   OutputKindAsm -> link outputPath pathList ["-S"]
run (Check inputPathStr colorizeFlag eoe) = do
  inputPath <- resolveFile' inputPathStr
  time <- round <$> getPOSIXTime
  resultOrErr <-
    evalWithEnv (runCheck inputPath) $
    initialEnv
      { shouldColorize = colorizeFlag
      , endOfEntry = eoe
      , isCheck = True
      , timestamp = time
      }
  case resultOrErr of
    Right _ -> return ()
    Left err ->
      seqIO (map (outputLog colorizeFlag eoe) err) >> exitWith (ExitFailure 1)
run (Archive inputPathStr mOutputPathStr) = do
  inputPath <- resolveDir' inputPathStr
  contents <- listDirectory $ toFilePath inputPath
  mOutputPath <- mapM resolveFile' mOutputPathStr
  outputPath <- toFilePath <$> constructOutputArchivePath inputPath mOutputPath
  archive outputPath (toFilePath inputPath) contents
run (Complete inputPathStr l c) = do
  inputPath <- resolveFile' inputPathStr
  time <- round <$> getPOSIXTime
  resultOrErr <-
    evalWithEnv (complete inputPath l c) $ initialEnv {timestamp = time}
  case resultOrErr of
    Left _ -> return ()
    Right result -> mapM_ putStrLn result

constructOutputPath ::
     Path Rel File -> Maybe (Path Abs File) -> OutputKind -> IO (Path Abs File)
constructOutputPath basename Nothing OutputKindLLVM = do
  dir <- getCurrentDir
  addExtension ".ll" (dir </> basename)
constructOutputPath basename Nothing OutputKindAsm = do
  dir <- getCurrentDir
  addExtension ".s" (dir </> basename)
constructOutputPath basename Nothing OutputKindObject = do
  dir <- getCurrentDir
  return $ dir </> basename
constructOutputPath _ (Just path) _ = return path

constructOutputArchivePath ::
     Path Abs Dir -> Maybe (Path Abs File) -> IO (Path Abs File)
constructOutputArchivePath inputPath Nothing = do
  let baseName = fromRelDir $ dirname inputPath
  outputPath <- resolveFile' baseName
  addExtension ".tar.gz" outputPath
constructOutputArchivePath _ (Just path) = return path

runBuild :: Path Abs File -> WithEnv [Path Abs File]
runBuild inputPath = parse inputPath >>= build

runCheck :: Path Abs File -> WithEnv ()
runCheck inputPath = parse inputPath >>= check

seqIO :: [IO ()] -> IO ()
seqIO [] = return ()
seqIO (a:as) = a >> seqIO as

archive :: FilePath -> FilePath -> [FilePath] -> IO ()
archive tarPath base dir = do
  es <- Tar.pack base dir
  L.writeFile tarPath $ GZip.compress $ Tar.write es
