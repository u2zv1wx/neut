module Main (main) where

import Clarify
import Control.Monad.State.Lazy
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy as L
import Data.Env
import Data.Log
import Elaborate
import Emit
import GHC.IO.Handle
import Lower
import Options.Applicative
import Parse
import Path
import Path.IO
import System.Exit
import System.Process hiding (env)
import Text.Read (readMaybe)

type InputPath =
  String

type OutputPath =
  String

type CheckOptEndOfEntry =
  String

type ShouldCancelAlloc =
  Bool

type ShouldColorize =
  Bool

data OutputKind
  = OutputKindObject
  | OutputKindLLVM
  | OutputKindAsm
  deriving (Show)

instance Read OutputKind where
  readsPrec _ "object" =
    [(OutputKindObject, [])]
  readsPrec _ "llvm" =
    [(OutputKindLLVM, [])]
  readsPrec _ "asm" =
    [(OutputKindAsm, [])]
  readsPrec _ _ =
    []

data Command
  = Build InputPath (Maybe OutputPath) OutputKind ShouldCancelAlloc
  | Check InputPath ShouldColorize CheckOptEndOfEntry
  | Archive InputPath (Maybe OutputPath)

main :: IO ()
main =
  execParser (info (helper <*> parseOpt) fullDesc) >>= run

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
    <*> flag
      True
      False
      ( mconcat
          [ long "no-alloc-cancellation",
            help "Set this to disable optimization for redundant alloc"
          ]
      )

kindReader :: ReadM OutputKind
kindReader = do
  s <- str
  case readMaybe s of
    Nothing ->
      readerError $ "unknown mode:" ++ s
    Just m ->
      return m

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

run :: Command -> IO ()
run cmd =
  case cmd of
    Build inputPathStr mOutputPathStr outputKind cancelAllocFlag -> do
      inputPath <- resolveFile' inputPathStr
      resultOrErr <- evalWithEnv (runBuild inputPath) $ initialEnv {shouldCancelAlloc = cancelAllocFlag}
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
          initialEnv {shouldColorize = colorizeFlag, endOfEntry = eoe}
      case resultOrErr of
        Right _ ->
          return ()
        Left (Error err) ->
          seqIO (map (outputLog colorizeFlag eoe) err) >> exitWith (ExitFailure 1)
    Archive inputPathStr mOutputPathStr -> do
      libDirPath <- resolveDir' inputPathStr
      let parentDirPath = parent libDirPath
      basename <- stripProperPrefix parentDirPath libDirPath
      mOutputPath <- mapM resolveFile' mOutputPathStr
      outputPath <- toFilePath <$> constructOutputArchivePath libDirPath mOutputPath
      let tarCmd = proc "tar" ["cJf", outputPath, "-C", toFilePath parentDirPath, toFilePath basename]
      (_, _, _, handler) <- createProcess tarCmd
      tarExitCode <- waitForProcess handler
      exitWith tarExitCode

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
    Nothing ->
      resolveFile' (fromRelDir $ dirname inputPath) >>= addExtension ".tar" >>= addExtension ".gz"

runBuild :: Path Abs File -> WithEnv Builder
runBuild =
  parse >=> elaborate >=> clarify >=> lower >=> emit

runCheck :: Path Abs File -> WithEnv ()
runCheck =
  parse >=> elaborate >=> \_ -> return ()

seqIO :: [IO ()] -> IO ()
seqIO =
  foldr (>>) (return ())

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
    "-O2",
    "-",
    "-o",
    toFilePath outputPath
  ]
