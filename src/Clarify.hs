{-# LANGUAGE OverloadedStrings #-}

--
-- clarification == polarization + closure conversion + linearization (+ rename, for LLVM IR)
--
module Clarify
  ( clarify
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nubBy)

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

import Clarify.Closure
import Clarify.Sigma
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
import Data.Term
import Reduce.Term

import qualified Text.Show.Pretty as Pr

clarify :: TermPlus -> WithEnv CodePlus
clarify (m, TermTau) = do
  v <- cartesianUniv m
  return (m, CodeUpIntro v)
clarify (m, TermUpsilon x) = return (m, CodeUpIntro (m, DataUpsilon x))
clarify (m, TermPi {}) = do
  returnClosureType m
clarify lam@(m, TermPiIntro xts e) = do
  forM_ xts $ uncurry insTypeEnv
  e' <- clarify e
  fvs <- chainTermPlus lam
  retClosure Nothing fvs m xts e'
clarify (m, TermPiElim e es) = do
  e' <- clarify e
  callClosure' m e' es
clarify iter@(m, TermIter (x, t) xts e) = do
  forM_ ((x, t) : xts) $ uncurry insTypeEnv
  e' <- clarify e
  fvs <- chainTermPlus iter
  retClosure' x fvs m xts e'
clarify (m, TermConst x) = clarifyConst m x
clarify (_, TermConstDecl (x, t) e) = do
  _ <- clarify t
  insTypeEnv x t
  clarify e
clarify (m, TermIntS size l) = do
  return (m, CodeUpIntro (m, DataIntS size l))
clarify (m, TermIntU size l) = do
  return (m, CodeUpIntro (m, DataIntU size l))
clarify (m, TermFloat16 l) = do
  return (m, CodeUpIntro (m, DataFloat16 l))
clarify (m, TermFloat32 l) = do
  return (m, CodeUpIntro (m, DataFloat32 l))
clarify (m, TermFloat64 l) = do
  return (m, CodeUpIntro (m, DataFloat64 l))
clarify (m, TermEnum _) = do
  v <- cartesianImmediate m
  return (m, CodeUpIntro v)
clarify (m, TermEnumIntro l) = do
  return (m, CodeUpIntro (m, DataEnumIntro l))
clarify (m, TermEnumElim e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM clarify es
  (yName, e', y) <- clarifyPlus e
  return $ bindLet [(yName, e')] (m, CodeEnumElim y (zip cs es'))
clarify (m, TermArray {}) = do
  returnArrayType m
clarify (m, TermArrayIntro k es) = do
  retImmType <- returnCartesianImmediate
  -- arrayType = Sigma{k} [_ : IMMEDIATE, ..., _ : IMMEDIATE]
  name <- newNameWith "array"
  let ts = map Left $ replicate (length es) retImmType
  arrayType <- cartesianSigma name m k ts
  (zs, es', xs) <- unzip3 <$> mapM clarifyPlus es
  return $
    bindLet (zip zs es') $
    ( m
    , CodeUpIntro $
      (m, DataSigmaIntro arrVoidPtr [arrayType, (m, DataSigmaIntro k xs)]))
clarify (m, TermArrayElim k xts e1 e2) = do
  e1' <- clarify e1
  forM_ xts $ uncurry insTypeEnv
  let (xs, ts) = unzip xts
  (arrVarName, arrVar) <- newDataUpsilonWith "arr"
  (arrTypeVarName, arrTypeVar) <- newDataUpsilonWith "arr-type"
  let retArrTypeVar = (m, CodeUpIntro arrTypeVar)
  (arrInnerVarName, arrInnerVar) <- newDataUpsilonWith "arr-inner"
  affVarName <- newNameWith "aff"
  relVarName <- newNameWith "rel"
  retUnivType <- returnCartesianUniv
  retImmType <- returnCartesianImmediate
  ts' <- mapM clarify ts
  let xts' = zip xs ts'
  e2' <- clarify e2
  return $
    bindLet [(arrVarName, e1')] $
    ( m
    , CodeSigmaElim
        arrVoidPtr
        [(arrTypeVarName, retUnivType), (arrInnerVarName, retArrTypeVar)]
        arrVar
        ( m
        , CodeSigmaElim
            arrVoidPtr
            [(affVarName, retImmType), (relVarName, retImmType)]
            arrTypeVar
            (m, CodeSigmaElim k xts' arrInnerVar e2')))
clarify (m, TermStruct ks) = do
  t <- cartesianStruct m ks
  return (m, CodeUpIntro t)
clarify (m, TermStructIntro eks) = do
  let (es, ks) = unzip eks
  (xs, es', vs) <- unzip3 <$> mapM clarifyPlus es
  return $
    bindLet (zip xs es') $ (m, CodeUpIntro (m, DataStructIntro (zip vs ks)))
clarify (m, TermStructElim xks e1 e2) = do
  e1' <- clarify e1
  let (xs, ks) = unzip xks
  let ts = map inferKind ks
  forM_ (zip xs ts) $ uncurry insTypeEnv
  e2' <- clarify e2
  (structVarName, structVar) <- newDataUpsilonWith "struct"
  return $ bindLet [(structVarName, e1')] (m, CodeStructElim xks structVar e2')

clarifyPlus :: TermPlus -> WithEnv (Identifier, CodePlus, DataPlus)
clarifyPlus e@(m, _) = do
  e' <- clarify e
  (varName, var) <- newDataUpsilonWith' "var" m
  return (varName, e', var)

clarifyConst :: Meta -> Identifier -> WithEnv CodePlus
clarifyConst m name
  | Just (lowType, op) <- asUnaryOpMaybe name = clarifyUnaryOp name op lowType m
clarifyConst m name
  | Just (lowType, op) <- asBinaryOpMaybe name =
    clarifyBinaryOp name op lowType m
clarifyConst m name
  | Just (sysCall, len) <- asSysCallMaybe name =
    clarifySysCall name sysCall len m
clarifyConst m name
  | Just _ <- asLowTypeMaybe name = clarify (m, TermEnum $ EnumTypeLabel "top")
clarifyConst m "is-enum" = clarifyIsEnum m
clarifyConst m "file-descriptor" = clarify (m, TermConst "i64")
clarifyConst m "stdin" = clarify (m, TermIntS 64 0)
clarifyConst m "stdout" = clarify (m, TermIntS 64 1)
clarifyConst m "stderr" = clarify (m, TermIntS 64 2)
clarifyConst m name = do
  mx <- asEnumConstant name
  case mx of
    Just i ->
      clarify (m, TermIntU 64 i) -- enum.top ~> 1, enum.choice ~> 2, etc.
    Nothing -> do
      cenv <- gets constantEnv
      if name `elem` cenv
        then return (m, CodeUpIntro (m, DataTheta name))
        else throwError $ "clarify.theta: " <> name

clarifyUnaryOp :: Identifier -> UnaryOp -> LowType -> Meta -> WithEnv CodePlus
clarifyUnaryOp name op lowType m = do
  t <- lookupTypeEnv name
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx)] _) -> do
      let varX = toDataUpsilon (x, emptyMeta)
      zts <- complementaryChainOf xts
      -- p "one-time closure (unary)"
      retClosure
        (Just name)
        zts
        m
        [(x, tx)]
        (m, CodeTheta (ThetaUnaryOp op lowType varX))
    _ -> throwError $ "the arity of " <> name <> " is wrong"

clarifyBinaryOp :: Identifier -> BinaryOp -> LowType -> Meta -> WithEnv CodePlus
clarifyBinaryOp name op lowType m = do
  t <- lookupTypeEnv name
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx), (y, ty)] _) -> do
      let varX = toDataUpsilon (x, emptyMeta)
      let varY = toDataUpsilon (y, emptyMeta)
      zts <- complementaryChainOf xts
      -- p "one-time closure (binary)"
      retClosure
        (Just name)
        zts
        m
        [(x, tx), (y, ty)]
        (m, CodeTheta (ThetaBinaryOp op lowType varX varY))
    _ -> throwError $ "the arity of " <> name <> " is wrong"

clarifyIsEnum :: Meta -> WithEnv CodePlus
clarifyIsEnum m = do
  t <- lookupTypeEnv "is-enum"
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx)] _) -> do
      v <- cartesianImmediate m
      let varX = toDataUpsilon (x, emptyMeta)
      aff <- newNameWith "aff"
      rel <- newNameWith "rel"
      retImmType <- returnCartesianImmediate
      zts <- complementaryChainOf xts
      -- p "one-time closure (is-enum)"
      retClosure
        (Just "is-enum")
        zts
        m
        [(x, tx)]
        ( m
        , CodeSigmaElim
            arrVoidPtr
            [(aff, retImmType), (rel, retImmType)]
            varX
            (m, CodeUpIntro v))
    _ ->
      throwError $ "the type of is-enum is wrong. t :\n" <> T.pack (Pr.ppShow t)

clarifySysCall ::
     Identifier -- the name of theta
  -> SysCall -- the kind of system call
  -> [Arg] -- the length of the arguments of the theta
  -> Meta -- the meta of the theta
  -> WithEnv CodePlus
clarifySysCall name sysCall args m = do
  sysCallType <- lookupTypeEnv name
  sysCallType' <- reduceTermPlus sysCallType
  case sysCallType' of
    (_, TermPi xts cod)
      | length xts == length args -> do
        zts <- complementaryChainOf xts
        let xtas = zip xts args
        (xss, dss, headerList) <-
          unzip3 <$> mapM (\((x, t), a) -> toHeaderInfo m x t a) xtas
        let ds = concat dss
        let xs = concat xss
        callThenReturn <- toSysCallTail m cod sysCall ds xs
        let body = iterativeApp headerList callThenReturn
        os <- getOS
        case (sysCall, os) of
          (SysCallFork, OSDarwin) -> do
            name' <- newNameWith "fork"
            retClosure (Just name') zts m xts body
          _ -> retClosure (Just name) zts m xts body
    _ -> throwError $ "the type of " <> name <> " is wrong"

iterativeApp :: [a -> a] -> a -> a
iterativeApp [] x = x
iterativeApp (f:fs) x = f (iterativeApp fs x)

complementaryChainOf ::
     [(Identifier, TermPlus)] -> WithEnv [(Identifier, TermPlus)]
complementaryChainOf xts = do
  zts <- chainTermPlus'' xts []
  return $ nubBy (\(x, _) (y, _) -> x == y) zts

toVar :: Identifier -> DataPlus
toVar x = (emptyMeta, DataUpsilon x)

clarifyBinder :: [(Identifier, TermPlus)] -> WithEnv [(Identifier, CodePlus)]
clarifyBinder [] = return []
clarifyBinder ((x, t):xts) = do
  t' <- clarify t
  xts' <- clarifyBinder xts
  return $ (x, t') : xts'

retClosure ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
retClosure mName fvs m xts e = do
  cls <- makeClosure' mName fvs m xts e
  return (m, CodeUpIntro cls)

retClosure' ::
     Identifier -- the name of newly created closure
  -> [(Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
retClosure' x fvs m xts e = do
  modify (\env -> env {nameEnv = Map.insert x x (nameEnv env)})
  cls <- makeClosure' (Just x) fvs m xts e
  knot x cls
  return (m, CodeUpIntro cls)

makeClosure' ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv DataPlus
makeClosure' mName fvs m xts e = do
  fvs' <- clarifyBinder fvs
  xts' <- clarifyBinder xts
  makeClosure mName fvs' m xts' e

callClosure' :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure' m e es = do
  tmp <- mapM (clarifyPlus) es
  callClosure m e tmp

knot :: Identifier -> DataPlus -> WithEnv ()
knot z cls = do
  cenv <- gets codeEnv
  case pop z cenv of
    Nothing -> throwError "knot"
    Just ((args, body), cenv') -> do
      let body' = substCodePlus [(z, cls)] body
      let cenv'' = Map.insert z (args, body') cenv'
      modify (\env -> env {codeEnv = cenv''})

-- lookup and remove the matching element from the given assoc list
pop ::
     Identifier
  -> Map.HashMap Identifier b
  -> Maybe (b, Map.HashMap Identifier b)
pop x mp = do
  v <- Map.lookup x mp
  return (v, Map.delete x mp)

asSysCallMaybe :: Identifier -> Maybe (SysCall, [Arg])
asSysCallMaybe "write" =
  Just (SysCallWrite, [ArgUnused, ArgImmediate, ArgArray, ArgImmediate])
asSysCallMaybe "read" =
  Just (SysCallRead, [ArgUnused, ArgImmediate, ArgArray, ArgImmediate])
asSysCallMaybe "exit" = Just (SysCallExit, [ArgImmediate])
asSysCallMaybe "open" =
  Just (SysCallOpen, [ArgUnused, ArgArray, ArgImmediate, ArgImmediate])
asSysCallMaybe "close" = Just (SysCallClose, [ArgImmediate])
asSysCallMaybe "fork" = Just (SysCallFork, [])
asSysCallMaybe _ = Nothing

data Arg
  = ArgImmediate
  | ArgArray
  | ArgStruct
  | ArgUnused
  deriving (Show)

toHeaderInfo ::
     Meta
  -> Identifier -- argument
  -> TermPlus -- the type of argument
  -> Arg -- the way of use of argument (specifically)
  -> WithEnv ([Identifier], [DataPlus], CodePlus -> CodePlus) -- ([borrow], arg-to-syscall, ADD_HEADER_TO_CONTINUATION)
toHeaderInfo _ x _ ArgImmediate = return ([], [toVar x], id)
toHeaderInfo _ _ _ ArgUnused = return ([], [], id)
toHeaderInfo m x t ArgStruct = do
  (structVarName, structVar) <- newDataUpsilonWith "struct"
  insTypeEnv structVarName t
  return
    ( [structVarName]
    , [structVar]
    , \cont -> (m, CodeUpElim structVarName (m, CodeUpIntro (toVar x)) cont))
toHeaderInfo m x t ArgArray = do
  arrayVarName <- newNameWith "array"
  insTypeEnv arrayVarName t
  (arrayTypeName, arrayType) <- newDataUpsilonWith "array-type"
  (arrayInnerName, arrayInner) <- newDataUpsilonWith "array-inner"
  (arrayInnerTmpName, arrayInnerTmp) <- newDataUpsilonWith "array-tmp"
  retUnivType <- returnCartesianUniv
  return
    ( [arrayVarName]
    , [arrayInnerTmp]
    , \cont ->
        ( m
        , CodeSigmaElim
            arrVoidPtr
            [ (arrayTypeName, retUnivType)
            , (arrayInnerName, (m, CodeUpIntro arrayType))
            ]
            (toVar x)
            ( m
            , CodeUpElim
                arrayInnerTmpName
                (m, CodeUpIntro arrayInner)
                ( m
                , CodeUpElim
                    arrayVarName
                    ( m
                    , CodeUpIntro
                        ( m
                        , DataSigmaIntro arrVoidPtr [arrayType, arrayInnerTmp]))
                    cont))))

toSysCallTail ::
     Meta
  -> TermPlus -- cod type
  -> SysCall -- read, write, open, etc
  -> [DataPlus] -- args of syscall
  -> [Identifier] -- borrowed variables
  -> WithEnv CodePlus
toSysCallTail m cod syscall args xs = do
  resultVarName <- newNameWith "result"
  result <- retWithBorrowedVars m cod xs resultVarName
  os <- getOS
  case (syscall, os) of
    (SysCallFork, OSDarwin) -> do
      return
        ( m
        , CodeUpElim
            resultVarName
            (m, CodePiElimDownElim (m, DataTheta "fork") args)
            result)
    _ ->
      return
        ( m
        , CodeUpElim
            resultVarName
            (m, CodeTheta (ThetaSysCall syscall args))
            result)

retWithBorrowedVars ::
     Meta -> TermPlus -> [Identifier] -> Identifier -> WithEnv CodePlus
retWithBorrowedVars m _ [] resultVarName =
  return (m, CodeUpIntro (m, DataUpsilon resultVarName))
retWithBorrowedVars m cod xs resultVarName
  | (_, TermPi [c, (funName, funType@(_, TermPi xts _))] _) <- cod
  , length xts >= 1 = do
    let resultType = snd $ last xts
    let vs = map (\x -> (m, TermUpsilon x)) $ xs ++ [resultVarName]
    insTypeEnv resultVarName resultType
    clarify
      ( m
      , TermPiIntro
          [c, (funName, funType)]
          (m, TermPiElim (m, TermUpsilon funName) vs))
  | otherwise = throwError "retWithBorrowedVars"

inferKind :: ArrayKind -> TermPlus
inferKind (ArrayKindIntS i) = (emptyMeta, TermConst $ "i" <> T.pack (show i))
inferKind (ArrayKindIntU i) = (emptyMeta, TermConst $ "u" <> T.pack (show i))
inferKind (ArrayKindFloat size) =
  (emptyMeta, TermConst $ "f" <> T.pack (show (sizeAsInt size)))
inferKind _ = error "inferKind for void-pointer"
