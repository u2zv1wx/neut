{-# LANGUAGE OverloadedStrings #-}

module Data.Env where

import Control.Monad.Except
import Control.Monad.State
import Path
import System.Info

import Data.Basic
import Data.Code
import Data.Constraint
import Data.LLVM
import Data.Log
import Data.Term
import Data.Tree
import Data.WeakTerm

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import qualified Text.Show.Pretty as Pr

type ConstraintQueue = Q.MinQueue EnrichedConstraint

type IncludeGraph = Map.HashMap (Path Abs File) [Path Abs File]

type FileInfo = [(Meta, Identifier, WeakTermPlus)]

type FileEnv = Map.HashMap (Path Abs File) FileInfo

type RuleEnv = Map.HashMap Int (Maybe [Data.WeakTerm.IdentifierPlus])

type UnivInstEnv = IntMap.IntMap (S.Set Int)

data Env =
  Env
    { count :: Int
    -- parse
    , inputText :: T.Text
    , inputLine :: Int
    , inputColumn :: Int
    , phase :: Int
    , target :: Maybe Target
    , mainFilePath :: Path Abs File
    , currentFilePath :: Path Abs File
    , includeGraph :: IncludeGraph -- to detect cyclic `include`
    , keywordEnv :: S.Set T.Text -- list of reserved keywords
    , notationEnv :: [(TreePlus, TreePlus)] -- macro transformers
    , constantEnv :: Map.HashMap T.Text Int
    , fileEnv :: FileEnv -- path ~> identifiers defined in the file at toplevel
    , enumEnv :: Map.HashMap T.Text [(T.Text, Int)] -- [("choice", [("left", 0), ("right", 1)]), ...]
    , revEnumEnv :: Map.HashMap T.Text (T.Text, Int) -- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
    , revNameEnv :: IntMap.IntMap Int -- [("foo.13", "foo"), ...] (as corresponding int)
    , formationEnv :: IntMap.IntMap (Maybe WeakTermPlus)
    , inductiveEnv :: RuleEnv -- "list" ~> (cons, Pi (A : tau). A -> list A -> list A)
    , coinductiveEnv :: RuleEnv -- "tail" ~> (head, Pi (A : tau). stream A -> A)
    -- elaborate
    , weakTypeEnv :: IntMap.IntMap (WeakTermPlus, UnivLevelPlus) -- var ~> (typeof(var), level-of-type)
    , equalityEnv :: [(UnivLevel, UnivLevel)]
    , univInstEnv :: UnivInstEnv
    , univRenameEnv :: IntMap.IntMap Int
    , typeEnv :: IntMap.IntMap (TermPlus, UnivLevelPlus)
    , constraintEnv :: [PreConstraint] -- for type inference
    , constraintQueue :: ConstraintQueue
    , levelEnv :: [LevelConstraint]
    , substEnv :: IntMap.IntMap WeakTermPlus -- metavar ~> beta-equivalent weakterm
    , zetaEnv :: IntMap.IntMap (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
    -- clarify
    , chainEnv :: IntMap.IntMap [(Meta, Identifier, TermPlus)] -- var/const ~> the closed var chain of its type
    , codeEnv :: Map.HashMap Identifier Definition -- f ~> thunk (lam (x1 ... xn) e)
    , nameSet :: S.Set Identifier
    -- LLVM
    , llvmEnv :: Map.HashMap Identifier ([Identifier], LLVM)
    , declEnv :: Map.HashMap T.Text ([LowType], LowType) -- external functions that must be declared in LLVM IR
    }

initialEnv :: Path Abs File -> Env
initialEnv path =
  Env
    { count = 0
    , inputText = T.empty
    , inputLine = 0
    , inputColumn = 0
    , phase = 0
    , target = Nothing
    , includeGraph = Map.empty
    , notationEnv = []
    , keywordEnv = S.empty
    , constantEnv = Map.empty
    , enumEnv = Map.empty
    , fileEnv = Map.empty
    , revEnumEnv = Map.empty
    , revNameEnv = IntMap.empty
    , formationEnv = IntMap.empty
    , inductiveEnv = Map.empty
    , coinductiveEnv = Map.empty
    , equalityEnv = []
    , univInstEnv = IntMap.empty
    , univRenameEnv = IntMap.empty
    , weakTypeEnv = IntMap.empty
    , typeEnv = IntMap.empty
    , chainEnv = IntMap.empty
    , codeEnv = Map.empty
    , llvmEnv = Map.empty
    , declEnv =
        Map.fromList
          [ ("malloc", ([LowTypeIntS 64], LowTypeVoidPtr))
          , ("free", ([LowTypeVoidPtr], LowTypeVoid))
          ]
    , constraintEnv = []
    , constraintQueue = Q.empty
    , levelEnv = []
    , substEnv = IntMap.empty
    , zetaEnv = IntMap.empty
    , nameSet = S.empty
    , mainFilePath = path
    , currentFilePath = path
    }

type WithEnv a = StateT Env (ExceptT [Log] IO) a

evalWithEnv :: WithEnv a -> Env -> IO (Either [Log] a)
evalWithEnv c env = do
  resultOrErr <- runExceptT (runStateT c env)
  case resultOrErr of
    Left err -> return $ Left err
    Right (result, _) -> return $ Right result
  -- throwError [TIO.putStrLn x]

-- throwError' :: T.Text -> WithEnv a
-- throwError' _ = undefined
newCount :: WithEnv Int
newCount = do
  i <- gets count
  modify (\e -> e {count = i + 1})
  if i + 1 == 0
    then raiseCritical' "counter exhausted"
    else return i

newNameWith :: Identifier -> WithEnv Identifier
newNameWith (I (s, _)) = do
  j <- newCount
  return $ I (s, j)

newNameWith' :: T.Text -> WithEnv Identifier
newNameWith' s = do
  i <- newCount
  return $ I (s, i)

newNameWith'' :: T.Text -> WithEnv Identifier
newNameWith'' s = do
  i <- newCount
  return $ I (s <> "-" <> T.pack (show i), i)

newLLVMNameWith :: Identifier -> WithEnv Identifier
newLLVMNameWith (I (s, i)) = do
  j <- newCount
  modify (\e -> e {revNameEnv = IntMap.insert j i (revNameEnv e)})
  return $ I (llvmString s, j)

newLLVMNameWith' :: T.Text -> WithEnv Identifier
newLLVMNameWith' s = do
  i <- newCount
  return $ I (llvmString s <> "-" <> T.pack (show i), i)

llvmString :: T.Text -> T.Text
llvmString "" = error "llvmString called for the empty string"
llvmString s = T.cons (llvmHeadChar $ T.head s) (T.map llvmTailChar $ T.tail s)

llvmHeadCharSet :: S.Set Char
llvmHeadCharSet =
  S.fromList $
  "-$._" <> "abcdefghijklmnopqrstuvwxyz" <> "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

llvmHeadChar :: Char -> Char
llvmHeadChar x =
  if x `S.member` llvmHeadCharSet
    then x
    else '-'

llvmTailCharSet :: S.Set Char
llvmTailCharSet =
  S.fromList $
  "-$._" <>
  "abcdefghijklmnopqrstuvwxyz" <> "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <> "0123456789"

llvmTailChar :: Char -> Char
llvmTailChar x =
  if x `S.member` llvmTailCharSet
    then x
    else '-'

getTarget :: WithEnv Target
getTarget = do
  mtarget <- gets target
  case mtarget of
    Just t -> return t
    Nothing -> do
      currentOS <- getOS
      currentArch <- getArch
      return (currentOS, currentArch)

getOS :: WithEnv OS
getOS = do
  case os of
    "linux" -> return OSLinux
    "darwin" -> return OSDarwin
    s -> raiseError' $ "unsupported target os: " <> T.pack (show s)

getArch :: WithEnv Arch
getArch = do
  case arch of
    "x86_64" -> return Arch64
    s -> raiseError' $ "unsupported target arch: " <> T.pack (show s)

newDataUpsilonWith :: T.Text -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith name = newDataUpsilonWith' name emptyMeta

newDataUpsilonWith' :: T.Text -> Meta -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith' name m = do
  x <- newNameWith' name
  return (x, (m, DataUpsilon x))

piUnivLevelsfrom ::
     [Data.WeakTerm.IdentifierPlus] -> WeakTermPlus -> WithEnv [UnivLevelPlus]
piUnivLevelsfrom xts t = do
  let ms = map fst $ map (\(_, _, z) -> z) xts ++ [t]
  ls <- mapM (const newCount) ms
  return $ map UnivLevelPlus $ zip ms ls

insTypeEnv :: Identifier -> TermPlus -> UnivLevelPlus -> WithEnv ()
insTypeEnv (I (_, i)) t ml =
  modify (\e -> e {typeEnv = IntMap.insert i (t, ml) (typeEnv e)})

insTypeEnv' :: Identifier -> TermPlus -> WithEnv ()
insTypeEnv' (I (_, i)) t = do
  l <- newCount
  let ml = UnivLevelPlus (fst t, l)
  modify (\e -> e {typeEnv = IntMap.insert i (t, ml) (typeEnv e)})

lookupTypeEnv :: Identifier -> WithEnv (Maybe (TermPlus, UnivLevelPlus))
lookupTypeEnv (I (_, i)) = do
  tenv <- gets typeEnv
  return $ IntMap.lookup i tenv

lookupTypeEnv' :: Identifier -> WithEnv TermPlus
lookupTypeEnv' (I (s, i))
  | Just _ <- asLowTypeMaybe s = do
    l <- newCount
    return (emptyMeta, TermTau l)
  | Just op <- asUnaryOpMaybe s = unaryOpToType emptyMeta op
  | Just op <- asBinaryOpMaybe s = binaryOpToType emptyMeta op
  | Just lowType <- asArrayAccessMaybe s = arrayAccessToType emptyMeta lowType
  | otherwise = do
    mt <- gets (IntMap.lookup i . typeEnv)
    case mt of
      Just (t, _) -> return t
      Nothing -> raiseCritical' $ s <> " is not found in the type environment."

lowTypeToType :: Meta -> LowType -> WithEnv TermPlus
lowTypeToType m (LowTypeIntS s) = return (m, TermEnum (EnumTypeIntS s))
lowTypeToType m (LowTypeIntU s) = return (m, TermEnum (EnumTypeIntU s))
lowTypeToType m (LowTypeFloat s) = do
  let x = "f" <> T.pack (show (sizeAsInt s))
  i <- lookupConstNum x
  return (m, TermConst (I (x, i)))
lowTypeToType _ _ = raiseCritical' "invalid argument passed to lowTypeToType"

unaryOpToType :: Meta -> UnaryOp -> WithEnv TermPlus
unaryOpToType m op = do
  let (dom, cod) = unaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x <- newNameWith' "arg"
  let xts = [(m, x, dom')]
  -- mls <- piUnivLevelsfrom xts cod'
  return (m, TermPi [] xts cod')

binaryOpToType :: Meta -> BinaryOp -> WithEnv TermPlus
binaryOpToType m op = do
  let (dom, cod) = binaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x1 <- newNameWith' "arg"
  x2 <- newNameWith' "arg"
  let xts = [(m, x1, dom'), (m, x2, dom')]
  -- mls <- piUnivLevelsfrom xts cod'
  return (m, TermPi [] xts cod')

arrayAccessToType :: Meta -> LowType -> WithEnv TermPlus
arrayAccessToType m lowType = do
  t <- lowTypeToType m lowType
  k <- lowTypeToArrayKind lowType
  x1 <- newNameWith' "arg"
  x2 <- newNameWith' "arg"
  x3 <- newNameWith' "arg"
  let u64 = (m, TermEnum (EnumTypeIntU 64))
  -- let univ = (m, TermEnum (EnumTypeIntU 64))
  let idx = (m, TermUpsilon x2)
  let arr = (m, TermArray idx k)
  let xts = [(m, x1, u64), (m, x2, u64), (m, x3, arr)]
  -- let xts = [(m, x1, univ), (m, x2, arr), (m, x3, idx)]
  x4 <- newNameWith' "arg"
  x5 <- newNameWith' "arg"
  let cod = (m, TermSigma [(m, x4, arr), (m, x5, t)])
  return (m, TermPi [] xts cod)
  -- -- l <- newCount
  -- let univ = (m, TermEnum (EnumTypeIntU 64))
  -- -- let univ = (m, TermTau l)
  -- let idx = (m, TermUpsilon x1)
  -- let arr = (m, TermArray idx k)
  -- let xts = [(m, x1, univ), (m, x2, arr), (m, x3, idx)]
  -- x4 <- newNameWith' "arg"
  -- x5 <- newNameWith' "arg"
  -- let cod = (m, TermSigma [(m, x4, arr), (m, x5, t)])
  -- -- mls <- piUnivLevelsfrom xts cod
  -- return (m, TermPi [] xts cod)

lookupConstNum :: T.Text -> WithEnv Int
lookupConstNum constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return i
    Nothing -> do
      i <- newCount
      modify (\env -> env {constantEnv = Map.insert constName i cenv})
      return i

lookupConstNum' :: T.Text -> WithEnv Int
lookupConstNum' constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return i
    Nothing -> raiseCritical' $ "no such constant: " <> constName

lookupConstantMaybe :: T.Text -> WithEnv (Maybe WeakTermPlus)
lookupConstantMaybe constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return $ Just (emptyMeta, WeakTermConst $ I (constName, i))
    Nothing
      | isConstant constName -> Just <$> lookupConstantPlus constName
      | otherwise -> return Nothing

lookupConstantPlus :: T.Text -> WithEnv WeakTermPlus
lookupConstantPlus constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return (emptyMeta, WeakTermConst $ I (constName, i))
    Nothing -> do
      i <- newCount
      let ident = I (constName, i)
      modify (\env -> env {constantEnv = Map.insert constName i cenv})
      return (emptyMeta, WeakTermConst ident)

-- f32とかi64.addとかは定数
isConstant :: T.Text -> Bool
isConstant "f16" = True
isConstant "f32" = True
isConstant "f64" = True
isConstant name
  | name == "f16" = True
  | name == "f32" = True
  | name == "f64" = True
  | Just _ <- asUnaryOpMaybe name = True
  | Just _ <- asBinaryOpMaybe name = True
  | Just _ <- asArrayAccessMaybe name = True
  | otherwise = False

-- for debug
p :: String -> WithEnv ()
p s = liftIO $ putStrLn s

p' :: (Show a) => a -> WithEnv ()
p' s = liftIO $ putStrLn $ Pr.ppShow s

pp :: WeakTermPlus -> WithEnv ()
pp e = liftIO $ TIO.putStrLn $ toText e

toStr :: (Show a) => a -> String
toStr s = Pr.ppShow s

lowTypeToArrayKind :: LowType -> WithEnv ArrayKind
lowTypeToArrayKind lowType =
  case lowTypeToArrayKindMaybe lowType of
    Just k -> return k
    Nothing -> raiseCritical' "Infer.lowTypeToArrayKind"

raiseError :: Meta -> T.Text -> WithEnv a
raiseError m text = throwError [logError (getPosInfo m) text]

raiseError' :: T.Text -> WithEnv a
raiseError' text = throwError [logError' text]

raiseCritical :: Meta -> T.Text -> WithEnv a
raiseCritical m text = throwError [logCritical (getPosInfo m) text]

raiseCritical' :: T.Text -> WithEnv a
raiseCritical' text = throwError [logCritical' text]
