module Main where

import Clarify
import qualified Codec.Archive.Tar as Tar
import qualified Codec.Compression.GZip as GZip
import Complete
import Control.Monad.State.Lazy
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy as L
import Data.Env
import Data.Log
import Elaborate
import Emit
import GHC.IO.Handle
import LLVM
import Options.Applicative
import Parse
import Path
import Path.IO
import System.Directory (listDirectory)
import System.Exit
import System.Process
import Text.Read (readMaybe)

type InputPath = String

type OutputPath = String

type CheckOptEndOfEntry = String

type ShouldColorize = Bool

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
  = Build InputPath (Maybe OutputPath) OutputKind
  | Check InputPath ShouldColorize CheckOptEndOfEntry
  | Archive InputPath (Maybe OutputPath)
  | Complete InputPath Line Column

main :: IO ()
main = execParser (info (helper <*> parseOpt) fullDesc) >>= run

parseOpt :: Parser Command
parseOpt =
  subparser
    ( command
        "build"
        (info (helper <*> parseBuildOpt) (progDesc "build given file"))
        <> command
          "check"
          (info (helper <*> parseCheckOpt) (progDesc "check specified file"))
        <> command
          "archive"
          ( info
              (helper <*> parseArchiveOpt)
              (progDesc "create archive from given path")
          )
        <> command
          "complete"
          (info (helper <*> parseCompleteOpt) (progDesc "show completion info"))
    )

parseBuildOpt :: Parser Command
parseBuildOpt =
  Build
    <$> argument
      str
      ( mconcat
          [ metavar "INPUT",
            help "The path of input file"
          ]
      )
    <*> optional
      ( strOption $
          mconcat
            [ long "output",
              short 'o',
              metavar "OUTPUT",
              help "The path of output file"
            ]
      )
    <*> option
      kindReader
      ( mconcat
          [ long "emit",
            metavar "KIND",
            value OutputKindObject,
            help "The type of output file"
          ]
      )

kindReader :: ReadM OutputKind
kindReader = do
  s <- str
  case readMaybe s of
    Nothing -> readerError $ "unknown mode:" ++ s
    Just m -> return m

parseCheckOpt :: Parser Command
parseCheckOpt =
  Check
    <$> argument
      str
      ( mconcat
          [ metavar "INPUT",
            help "The path of input file"
          ]
      )
      <*> flag
        True
        False
        ( mconcat
            [ long "no-color",
              help "Set this to disable colorization of the output"
            ]
        )
      <*> strOption
        ( mconcat
            [ long "end-of-entry",
              value "",
              help "String printed after each entry",
              metavar "STRING"
            ]
        )

parseArchiveOpt :: Parser Command
parseArchiveOpt =
  Archive
    <$> argument
      str
      ( mconcat [metavar "INPUT", help "The path of input directory"]
      )
    <*> optional
      ( strOption $
          mconcat
            [ long "output",
              short 'o',
              metavar "OUTPUT",
              help "The path of output"
            ]
      )

parseCompleteOpt :: Parser Command
parseCompleteOpt =
  Complete
    <$> argument
      str
      ( mconcat
          [metavar "INPUT", help "The path of input file"]
      )
    <*> argument
      auto
      ( mconcat
          [help "Line number", metavar "LINE"]
      )
    <*> argument
      auto
      ( mconcat
          [help "Column number", metavar "COLUMN"]
      )

run :: Command -> IO ()
run cmd =
  case cmd of
    Build inputPathStr mOutputPathStr outputKind -> do
      inputPath <- resolveFile' inputPathStr
      resultOrErr <-
        evalWithEnv (runBuild inputPath) $
          initialEnv {shouldColorize = True, endOfEntry = ""}
      (basename, _) <- splitExtension $ filename inputPath
      mOutputPath <- mapM resolveFile' mOutputPathStr
      outputPath <- constructOutputPath basename mOutputPath outputKind
      case resultOrErr of
        Left (Error err) ->
          seqIO (map (outputLog True "") err) >> exitWith (ExitFailure 1)
        Right llvmIRBuilder -> do
          let llvmIR = toLazyByteString llvmIRBuilder
          case outputKind of
            OutputKindLLVM ->
              L.writeFile (toFilePath outputPath) llvmIR
            _ -> do
              let clangCmd = proc "clang" $ clangOptWith outputKind outputPath
              withCreateProcess clangCmd {std_in = CreatePipe} $ \(Just stdin) _ _ clangProcessHandler -> do
                L.hPut stdin llvmIR
                hClose stdin
                exitCode <- waitForProcess clangProcessHandler
                exitWith exitCode
    Check inputPathStr colorizeFlag eoe -> do
      inputPath <- resolveFile' inputPathStr
      resultOrErr <-
        evalWithEnv (runCheck inputPath) $
          initialEnv
            { shouldColorize = colorizeFlag,
              endOfEntry = eoe,
              isCheck = True
            }
      case resultOrErr of
        Right _ ->
          return ()
        Left (Error err) ->
          seqIO (map (outputLog colorizeFlag eoe) err) >> exitWith (ExitFailure 1)
    Archive inputPathStr mOutputPathStr -> do
      inputPath <- resolveDir' inputPathStr
      contents <- listDirectory $ toFilePath inputPath
      mOutputPath <- mapM resolveFile' mOutputPathStr
      outputPath <- toFilePath <$> constructOutputArchivePath inputPath mOutputPath
      archive outputPath (toFilePath inputPath) contents
    Complete inputPathStr l c -> do
      inputPath <- resolveFile' inputPathStr
      resultOrErr <-
        evalWithEnv (complete inputPath l c) initialEnv
      case resultOrErr of
        Left _ ->
          return ()
        Right result ->
          mapM_ putStrLn result

constructOutputPath :: Path Rel File -> Maybe (Path Abs File) -> OutputKind -> IO (Path Abs File)
constructOutputPath basename mPath kind =
  case mPath of
    Just path ->
      return path
    Nothing ->
      case kind of
        OutputKindLLVM -> do
          dir <- getCurrentDir
          addExtension ".ll" (dir </> basename)
        OutputKindAsm -> do
          dir <- getCurrentDir
          addExtension ".s" (dir </> basename)
        OutputKindObject -> do
          dir <- getCurrentDir
          return $ dir </> basename

constructOutputArchivePath :: Path Abs Dir -> Maybe (Path Abs File) -> IO (Path Abs File)
constructOutputArchivePath inputPath mPath =
  case mPath of
    Just path ->
      return path
    Nothing -> do
      let baseName = fromRelDir $ dirname inputPath
      outputPath <- resolveFile' baseName
      addExtension ".tar.gz" outputPath

runBuild :: Path Abs File -> WithEnv Builder
runBuild = parse >=> elaborate >=> clarify >=> toLLVM >=> emit

runCheck :: Path Abs File -> WithEnv ()
runCheck = parse >=> elaborate >=> \_ -> return ()

seqIO :: [IO ()] -> IO ()
seqIO = foldr (>>) (return ())

clangOptWith :: OutputKind -> Path Abs File -> [String]
clangOptWith kind outputPath =
  case kind of
    OutputKindAsm ->
      "-S" : clangBaseOpt outputPath
    _ ->
      clangBaseOpt outputPath

clangBaseOpt :: Path Abs File -> [String]
clangBaseOpt outputPath =
  [ "-xir",
    "-Wno-override-module",
    "-",
    "-o",
    toFilePath outputPath
  ]

archive :: FilePath -> FilePath -> [FilePath] -> IO ()
archive tarPath base dir = do
  es <- Tar.pack base dir
  L.writeFile tarPath $ GZip.compress $ Tar.write es
