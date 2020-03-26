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

import Clarify.Linearize
import Clarify.Sigma
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
import Data.Term
import Reduce.Term

clarify :: TermPlus -> WithEnv CodePlus
clarify (m, TermTau _) = returnCartesianImmediate m
clarify (m, TermUpsilon x) = return (m, CodeUpIntro (m, DataUpsilon x))
clarify (m, TermPi {}) = returnClosureType m
clarify (m, TermPiPlus {}) = returnClosureType m
clarify lam@(m, TermPiIntro mxts e) = do
  forM_ mxts insTypeEnv'
  fvs <- chainTermPlus lam
  e' <- clarify e
  retClosure Nothing fvs m mxts e'
clarify lam@(m, TermPiIntroNoReduce mxts e) = do
  forM_ mxts insTypeEnv'
  fvs <- chainTermPlus lam
  e' <- clarify e
  retClosure Nothing fvs m mxts e'
clarify (m, TermPiIntroPlus _ (name, args) mxts e) = do
  forM_ mxts insTypeEnv'
  case varTermPlus (m, TermPiIntro args $ termZero m) of
    [] -> do
      name' <- lookupLLVMEnumEnv m name
      e' <- clarify e
      retClosure (Just name') args m mxts e'
    _ -> do
      raiseError m $
        "couldn't normalize the type of the inductive closure at compile time"
clarify (m, TermPiElim e es) = do
  es' <- mapM clarifyPlus es
  e' <- clarify e
  callClosure m e' es'
clarify (m, TermSigma _) = returnClosureType m -- vaild since Sigma is translated into Pi
clarify (m, TermSigmaIntro t es) = do
  (zu, kp@(mk, k, _)) <- sigToPi m $ reduceTermPlus t
  clarify (m, TermPiIntro [zu, kp] (m, TermPiElim (mk, TermUpsilon k) es))
clarify (m, TermSigmaElim t xts e1 e2) =
  clarify (m, TermPiElim e1 [t, (m, TermPiIntro xts e2)])
clarify iter@(m, TermIter mxt@(_, x, _) mxts e) = do
  forM_ (mxt : mxts) insTypeEnv'
  e' <- clarify e
  fvs <- chainTermPlus iter
  retClosure' x fvs m mxts e'
clarify (m, TermConst x) = clarifyConst m x
clarify (m, TermFloat16 l) = return (m, CodeUpIntro (m, DataFloat16 l))
clarify (m, TermFloat32 l) = return (m, CodeUpIntro (m, DataFloat32 l))
clarify (m, TermFloat64 l) = return (m, CodeUpIntro (m, DataFloat64 l))
clarify (m, TermEnum _) = returnCartesianImmediate m
clarify (m, TermEnumIntro l) = return (m, CodeUpIntro (m, DataEnumIntro l))
clarify (m, TermEnumElim (e, _) bs) = do
  let (cs, es) = unzip bs
  tenv <- gets typeEnv
  fvs <- constructEnumFVS tenv es
  es' <- (mapM clarify >=> alignFVS m fvs) es
  let sub = map (\(mx, x, _) -> (x, (mx, DataUpsilon x))) fvs
  (y, e', yVar) <- clarifyPlus e
  return $ bindLet [(y, e')] (m, CodeEnumElim sub yVar (zip (map snd cs) es'))
clarify (m, TermArray {}) = returnArrayType m
clarify (m, TermArrayIntro k es) = do
  retImmType <- returnCartesianImmediate m
  -- arrayType = Sigma{k} [_ : IMMEDIATE, ..., _ : IMMEDIATE]
  name <- newNameWith' "array"
  let ts = map Left $ replicate (length es) retImmType
  arrayType <- cartesianSigma name m k ts
  (zs, es', xs) <- unzip3 <$> mapM clarifyPlus es
  return $
    bindLet (zip zs es') $
    (m, CodeUpIntro $ (m, sigmaIntro [arrayType, (m, DataSigmaIntro k xs)]))
clarify (m, TermArrayElim k mxts e1 e2) = do
  e1' <- clarify e1
  forM_ mxts insTypeEnv'
  (arr, arrVar) <- newDataUpsilonWith m "arr"
  arrType <- newNameWith' "arr-type"
  (content, contentVar) <- newDataUpsilonWith m "arr-content"
  e2' <- clarify e2
  let (_, xs, _) = unzip3 mxts
  return $
    bindLet [(arr, e1')] $
    ( m
    , sigmaElim [arrType, content] arrVar (m, CodeSigmaElim k xs contentVar e2'))
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
  let (ms, xs, ks) = unzip3 xks
  ts <- mapM (inferKind m) ks
  forM_ (zip3 ms xs ts) insTypeEnv'
  e2' <- clarify e2
  (struct, structVar) <- newDataUpsilonWith m "struct"
  return $ bindLet [(struct, e1')] (m, CodeStructElim (zip xs ks) structVar e2')
clarify (m, TermCase (e, _) cxtes) = do
  e' <- clarify e
  (cls, clsVar) <- newDataUpsilonWith m "case-closure"
  res <- newNameWith' "case-res"
  env <- newNameWith' "case-env"
  lam <- newNameWith' "label"
  cxtes' <- clarifyCase m cxtes res env lam
  return $ bindLet [(cls, e')] (m, sigmaElim [res, env, lam] clsVar cxtes')

clarifyPlus :: TermPlus -> WithEnv (Identifier, CodePlus, DataPlus)
clarifyPlus e@(m, _) = do
  e' <- clarify e
  (varName, var) <- newDataUpsilonWith m "var"
  return (varName, e', var)

constructEnumFVS :: TypeEnv -> [TermPlus] -> WithEnv [IdentifierPlus]
constructEnumFVS tenv es = nubFVS <$> concat <$> mapM (chainTermPlus' tenv) es

alignFVS :: Meta -> [IdentifierPlus] -> [CodePlus] -> WithEnv [CodePlus]
alignFVS m fvs es = do
  es' <- mapM (retClosure Nothing fvs m []) es
  mapM (\cls -> callClosure m cls []) es'

type Clause = (((Meta, Identifier), [IdentifierPlus]), TermPlus)

clarifyCase ::
     Meta
  -> [Clause]
  -> Identifier
  -> Identifier
  -> Identifier
  -> WithEnv CodePlus
clarifyCase m cxtes typeVarName envVarName lamVarName = do
  fvs <- constructCaseFVS cxtes m typeVarName envVarName
  es <- (mapM (clarifyCase' m envVarName) >=> alignFVS m fvs) cxtes
  (y, e', yVar) <- clarifyPlus (m, TermUpsilon lamVarName)
  let sub = map (\(mx, x, _) -> (x, (mx, DataUpsilon x))) fvs
  let cs = map (\cxte -> fst $ fst cxte) cxtes
  return $ bindLet [(y, e')] (m, CodeCase sub yVar (zip cs es))

constructCaseFVS ::
     [Clause] -> Meta -> Identifier -> Identifier -> WithEnv [IdentifierPlus]
constructCaseFVS cxtes m typeVarName envVarName = do
  fvss <- mapM chainCaseClause cxtes
  let fvs = nubFVS $ concat fvss
  return $
    (m, typeVarName, (m, TermTau 0)) :
    (m, envVarName, (m, TermUpsilon typeVarName)) : fvs

chainCaseClause :: Clause -> WithEnv [IdentifierPlus]
chainCaseClause (((m, _), xts), body) = chainTermPlus (m, TermPiIntro xts body)

nubFVS :: [IdentifierPlus] -> [IdentifierPlus]
nubFVS fvs = nubBy (\(_, x, _) (_, y, _) -> x == y) fvs

clarifyCase' :: Meta -> Identifier -> Clause -> WithEnv CodePlus
clarifyCase' m envVarName ((_, xts), e) = do
  xts' <- clarifyBinder xts
  e' <- clarify e >>= linearize (dropFst xts')
  let xs = map (\(_, x, _) -> x) xts
  return (m, sigmaElim xs (m, DataUpsilon envVarName) e')

clarifyConst :: Meta -> Identifier -> WithEnv CodePlus
clarifyConst m name@(I (x, _))
  | Just op <- asUnaryOpMaybe x = clarifyUnaryOp name op m
  | Just op <- asBinaryOpMaybe x = clarifyBinaryOp name op m
  | Just _ <- asLowTypeMaybe x = clarify (m, TermEnum $ EnumTypeLabel "top")
  | Just lowType <- asArrayAccessMaybe x = clarifyArrayAccess m name lowType
  | x == "os:file-descriptor" = clarify (m, TermEnum $ EnumTypeLabel "top")
  | x == "os:stdin" = clarify (m, TermEnumIntro (EnumValueIntS 64 0))
  | x == "os:stdout" = clarify (m, TermEnumIntro (EnumValueIntS 64 1))
  | x == "os:stderr" = clarify (m, TermEnumIntro (EnumValueIntS 64 2))
  | x == "unsafe:cast" = clarifyCast m
  | otherwise = do
    os <- getOS
    case asSysCallMaybe os x of
      Just (syscall, argInfo) -> clarifySysCall name syscall argInfo m
      Nothing -> return (m, CodeUpIntro (m, DataTheta $ asText'' name))

clarifyCast :: Meta -> WithEnv CodePlus
clarifyCast m = do
  a <- newNameWith' "t1"
  b <- newNameWith' "t2"
  z <- newNameWith' "z"
  let varA = (m, TermUpsilon a)
  let u = (m, TermTau 0)
  clarify
    (m, TermPiIntro [(m, a, u), (m, b, u), (m, z, varA)] (m, TermUpsilon z))

clarifyUnaryOp :: Identifier -> UnaryOp -> Meta -> WithEnv CodePlus
clarifyUnaryOp name op m = do
  t <- lookupTypeEnv' m name
  let t' = reduceTermPlus t
  case t' of
    (_, TermPi _ xts@[(mx, x, tx)] _) -> do
      let varX = (mx, DataUpsilon x)
      zts <- complementaryChainOf xts
      retClosure
        (Just $ asText'' name)
        zts
        m
        [(mx, x, tx)]
        (m, CodeTheta (ThetaUnaryOp op varX))
    _ -> raiseCritical m $ "the arity of " <> asText name <> " is wrong"

clarifyBinaryOp :: Identifier -> BinaryOp -> Meta -> WithEnv CodePlus
clarifyBinaryOp name op m = do
  t <- lookupTypeEnv' m name
  let t' = reduceTermPlus t
  case t' of
    (_, TermPi _ xts@[(mx, x, tx), (my, y, ty)] _) -> do
      let varX = (mx, DataUpsilon x)
      let varY = (my, DataUpsilon y)
      zts <- complementaryChainOf xts
      retClosure
        (Just $ asText'' name)
        zts
        m
        [(mx, x, tx), (my, y, ty)]
        (m, CodeTheta (ThetaBinaryOp op varX varY))
    _ -> raiseCritical m $ "the arity of " <> asText name <> " is wrong"

clarifyArrayAccess :: Meta -> Identifier -> LowType -> WithEnv CodePlus
clarifyArrayAccess m name lowType = do
  arrayAccessType <- lookupTypeEnv' m name
  let arrayAccessType' = reduceTermPlus arrayAccessType
  case arrayAccessType' of
    (_, TermPi _ xts cod)
      | length xts == 3 -> do
        (xs, ds, headerList) <-
          computeHeader m xts [ArgImm, ArgUnused, ArgArray]
        case ds of
          [index, arr] -> do
            zts <- complementaryChainOf xts
            callThenReturn <- toArrayAccessTail m lowType cod arr index xs
            let body = iterativeApp headerList callThenReturn
            retClosure (Just $ asText'' name) zts m xts body
          _ -> raiseCritical m $ "the type of array-access is wrong"
    _ -> raiseCritical m $ "the type of array-access is wrong"

clarifySysCall ::
     Identifier -- the name of theta
  -> Syscall
  -> [Arg] -- the length of the arguments of the theta
  -> Meta -- the meta of the theta
  -> WithEnv CodePlus
clarifySysCall name syscall args m = do
  sysCallType <- lookupTypeEnv' m name
  let sysCallType' = reduceTermPlus sysCallType
  case sysCallType' of
    (_, TermPi _ xts cod)
      | length xts == length args -> do
        zts <- complementaryChainOf xts
        (xs, ds, headerList) <- computeHeader m xts args
        forM_ xts insTypeEnv'
        callThenReturn <- toSysCallTail m cod syscall ds xs
        let body = iterativeApp headerList callThenReturn
        retClosure (Just $ asText'' name) zts m xts body
    _ -> raiseCritical m $ "the type of " <> asText name <> " is wrong"

iterativeApp :: [a -> a] -> a -> a
iterativeApp [] x = x
iterativeApp (f:fs) x = f (iterativeApp fs x)

complementaryChainOf :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
complementaryChainOf xts = do
  tenv <- gets typeEnv
  nubFVS <$> chainTermPlus'' tenv xts []

clarifyBinder :: [IdentifierPlus] -> WithEnv [(Meta, Identifier, CodePlus)]
clarifyBinder [] = return []
clarifyBinder ((m, x, t):xts) = do
  t' <- clarify t
  xts' <- clarifyBinder xts
  return $ (m, x, t') : xts'

knot :: Meta -> Identifier -> DataPlus -> WithEnv ()
knot m z cls = do
  cenv <- gets codeEnv
  case Map.lookup (asText'' z) cenv of
    Nothing -> raiseCritical m "knot"
    Just (Definition _ args body) -> do
      let body' = substCodePlus [(z, cls)] body
      let def' = Definition (IsFixed True) args body'
      modify (\env -> env {codeEnv = Map.insert (asText'' z) def' cenv})

asSysCallMaybe :: OS -> T.Text -> Maybe (Syscall, [Arg])
asSysCallMaybe OSLinux name = do
  case name of
    "os:read" ->
      return (Right ("read", 0), [ArgUnused, ArgImm, ArgArray, ArgImm])
    "os:write" ->
      return (Right ("write", 1), [ArgUnused, ArgImm, ArgArray, ArgImm])
    "os:open" ->
      return (Right ("open", 2), [ArgUnused, ArgArray, ArgImm, ArgImm])
    "os:close" -> return (Right ("close", 3), [ArgImm])
    "os:socket" -> return (Right ("socket", 41), [ArgImm, ArgImm, ArgImm])
    "os:connect" -> return (Right ("connect", 42), [ArgImm, ArgStruct, ArgImm])
    "os:accept" -> return (Right ("accept", 43), [ArgImm, ArgStruct, ArgArray])
    "os:bind" -> return (Right ("bind", 49), [ArgImm, ArgStruct, ArgImm])
    "os:listen" -> return (Right ("listen", 50), [ArgImm, ArgImm])
    "os:fork" -> return (Right ("fork", 57), [])
    "os:exit" -> return (Right ("exit", 60), [ArgUnused, ArgImm])
    "os:wait4" ->
      return (Right ("wait4", 61), [ArgImm, ArgArray, ArgImm, ArgStruct])
    _ -> Nothing
asSysCallMaybe OSDarwin name =
  case name of
    "os:exit" -> return (Left "exit", [ArgUnused, ArgImm]) -- 0x2000001
    "os:fork" -> return (Left "fork", []) -- 0x2000002
    "os:read" -> return (Left "read", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000003
    "os:write" -> return (Left "write", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000004
    "os:open" -> return (Left "open", [ArgUnused, ArgArray, ArgImm, ArgImm]) -- 0x2000005
    "os:close" -> return (Left "close", [ArgImm]) -- 0x2000006
    "os:wait4" -> return (Left "wait4", [ArgImm, ArgArray, ArgImm, ArgStruct]) -- 0x2000007
    "os:accept" -> return (Left "accept", [ArgImm, ArgStruct, ArgArray]) -- 0x2000030
    "os:socket" -> return (Left "socket", [ArgImm, ArgImm, ArgImm]) -- 0x2000097
    "os:connect" -> return (Left "connect", [ArgImm, ArgStruct, ArgImm]) -- 0x2000098
    "os:bind" -> return (Left "bind", [ArgImm, ArgStruct, ArgImm]) -- 0x2000104
    "os:listen" -> return (Left "listen", [ArgImm, ArgImm]) -- 0x2000106
    _ -> Nothing

data Arg
  = ArgImm
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
toHeaderInfo m x _ ArgImm = return ([], [(m, DataUpsilon x)], id)
toHeaderInfo _ _ _ ArgUnused = return ([], [], id)
toHeaderInfo m x t ArgStruct = do
  (structVarName, structVar) <- newDataUpsilonWith m "struct"
  insTypeEnv' (m, structVarName, t)
  return
    ( [structVarName]
    , [structVar]
    , \cont ->
        (m, CodeUpElim structVarName (m, CodeUpIntro (m, DataUpsilon x)) cont))
toHeaderInfo m x t ArgArray = do
  arrayVarName <- newNameWith' "array"
  insTypeEnv' (m, arrayVarName, t)
  (arrayTypeName, arrayType) <- newDataUpsilonWith m "array-type"
  (arrayInnerName, arrayInner) <- newDataUpsilonWith m "array-inner"
  (arrayInnerTmpName, arrayInnerTmp) <- newDataUpsilonWith m "array-tmp"
  return
    ( [arrayVarName]
    , [arrayInnerTmp]
    , \cont ->
        ( m
        , sigmaElim
            [arrayTypeName, arrayInnerName]
            (m, DataUpsilon x)
            ( m
            , CodeUpElim
                arrayInnerTmpName
                (m, CodeUpIntroNoReduce arrayInner)
                ( m
                , CodeUpElim
                    arrayVarName
                    (m, CodeUpIntro (m, sigmaIntro [arrayType, arrayInnerTmp]))
                    cont))))

computeHeader ::
     Meta
  -> [IdentifierPlus]
  -> [Arg]
  -> WithEnv ([Identifier], [DataPlus], [CodePlus -> CodePlus])
computeHeader m xts argInfoList = do
  let xtas = zip xts argInfoList
  (xss, dss, headerList) <-
    unzip3 <$> mapM (\((_, x, t), a) -> toHeaderInfo m x t a) xtas
  return (concat xss, concat dss, headerList)

toSysCallTail ::
     Meta
  -> TermPlus -- cod type
  -> Syscall -- read, write, open, etc
  -> [DataPlus] -- args of syscall
  -> [Identifier] -- borrowed variables
  -> WithEnv CodePlus
toSysCallTail m cod syscall args xs = do
  resultVarName <- newNameWith' "result"
  result <- retWithBorrowedVars m cod xs resultVarName
  return
    ( m
    , CodeUpElim resultVarName (m, CodeTheta (ThetaSysCall syscall args)) result)

toArrayAccessTail ::
     Meta
  -> LowType
  -> TermPlus -- cod type
  -> DataPlus -- array (inner)
  -> DataPlus -- index
  -> [Identifier] -- borrowed variables
  -> WithEnv CodePlus
toArrayAccessTail m lowType cod arr index xs = do
  resultVarName <- newNameWith' "result"
  result <- retWithBorrowedVars m cod xs resultVarName
  return
    ( m
    , CodeUpElim
        resultVarName
        (m, CodeTheta (ThetaArrayAccess lowType arr index))
        result)

retWithBorrowedVars ::
     Meta -> TermPlus -> [Identifier] -> Identifier -> WithEnv CodePlus
retWithBorrowedVars m _ [] resultVarName =
  return (m, CodeUpIntro (m, DataUpsilon resultVarName))
retWithBorrowedVars m cod xs resultVarName = do
  (zu, kp@(mk, k, sigArgs)) <- sigToPi m cod
  -- sigArgs = [BORRORED, ..., BORROWED, ACTUAL_RESULT]
  (mResult, resultType) <- rightmostOf sigArgs
  let vs = map (\x -> (m, TermUpsilon x)) $ xs ++ [resultVarName]
  insTypeEnv' (mResult, resultVarName, resultType)
  clarify (m, TermPiIntro [zu, kp] (m, TermPiElim (mk, TermUpsilon k) vs))

inferKind :: Meta -> ArrayKind -> WithEnv TermPlus
inferKind m (ArrayKindIntS i) = return (m, TermEnum (EnumTypeIntS i))
inferKind m (ArrayKindIntU i) = return (m, TermEnum (EnumTypeIntU i))
inferKind m (ArrayKindFloat size) = do
  let constName = "f" <> T.pack (show (sizeAsInt size))
  i <- lookupConstNum' m constName
  return (m, TermConst (I (constName, i)))
inferKind m _ = raiseCritical m "inferKind for void-pointer"

rightmostOf :: TermPlus -> WithEnv (Meta, TermPlus)
rightmostOf (_, TermPi _ xts _)
  | length xts >= 1 = do
    let (m, _, t) = last xts
    return (m, t)
rightmostOf (m, _) = raiseCritical m "rightmost"

sigToPi :: Meta -> TermPlus -> WithEnv (IdentifierPlus, IdentifierPlus)
sigToPi m sig = do
  case sig of
    (mSig, TermSigma xts) -> do
      tPi <- sigToPi' mSig xts
      case tPi of
        (_, TermPi _ [zu, kp] _) -> return (zu, kp)
        _ -> raiseCritical m "the type of sigma-intro is wrong"
    _ -> raiseCritical m "the type of sigma-intro is wrong"

sigToPi' :: Meta -> [IdentifierPlus] -> WithEnv TermPlus
sigToPi' m xts = do
  z <- newNameWith' "sigma"
  let zv = toTermUpsilon m z
  k <- newNameWith' "sig"
  return
    (m, TermPi [] [(m, z, (m, TermTau 0)), (m, k, (m, TermPi [] xts zv))] zv)

makeClosure ::
     Maybe T.Text -- the name of newly created closure
  -> [(Meta, Identifier, CodePlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Meta, Identifier, CodePlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv DataPlus
makeClosure mName mxts2 m mxts1 e = do
  let xts1 = dropFst mxts1
  let xts2 = dropFst mxts2
  expName <- newNameWith' "exp"
  envExp <- cartesianSigma expName m arrVoidPtr $ map Right xts2
  name <- nameFromMaybe mName
  registerIfNecessary m name xts1 xts2 e
  let vs = map (\(mx, x, _) -> (mx, DataUpsilon x)) mxts2
  let fvEnv = (m, sigmaIntro vs)
  return (m, sigmaIntro [envExp, fvEnv, (m, DataTheta name)])

registerIfNecessary ::
     Meta
  -> T.Text
  -> [(Identifier, CodePlus)]
  -> [(Identifier, CodePlus)]
  -> CodePlus
  -> WithEnv ()
registerIfNecessary m name xts1 xts2 e = do
  cenv <- gets codeEnv
  when (name `notElem` Map.keys cenv) $ do
    e' <- linearize (xts2 ++ xts1) e
    (envVarName, envVar) <- newDataUpsilonWith m "env"
    let args = map fst xts1 ++ [envVarName]
    let body = (m, sigmaElim (map fst xts2) envVar e')
    insCodeEnv name args body

makeClosure' ::
     Maybe T.Text -- the name of newly created closure
  -> [IdentifierPlus] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [IdentifierPlus] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv DataPlus
makeClosure' mName fvs m xts e = do
  fvs' <- clarifyBinder fvs
  xts' <- clarifyBinder xts
  makeClosure mName fvs' m xts' e

retClosure ::
     Maybe T.Text -- the name of newly created closure
  -> [IdentifierPlus] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [IdentifierPlus] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
retClosure mName fvs m xts e = do
  cls <- makeClosure' mName fvs m xts e
  return (m, CodeUpIntro cls)

retClosure' ::
     Identifier -- the name of newly created closure
  -> [IdentifierPlus] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [IdentifierPlus] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
retClosure' x fvs m xts e = do
  cls <- makeClosure' (Just $ asText'' x) fvs m xts e
  knot m x cls
  return (m, CodeUpIntro cls)

callClosure ::
     Meta -> CodePlus -> [(Identifier, CodePlus, DataPlus)] -> WithEnv CodePlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  (clsVarName, clsVar) <- newDataUpsilonWith m "closure"
  typeVarName <- newNameWith' "exp"
  (envVarName, envVar) <- newDataUpsilonWith m "env"
  (lamVarName, lamVar) <- newDataUpsilonWith m "thunk"
  return $
    bindLet
      ((clsVarName, e) : zip zs es')
      ( m
      , sigmaElim
          [typeVarName, envVarName, lamVarName]
          clsVar
          (m, CodePiElimDownElim lamVar (xs ++ [envVar])))

nameFromMaybe :: Maybe T.Text -> WithEnv T.Text
nameFromMaybe mName =
  case mName of
    Just lamThetaName -> return lamThetaName
    Nothing -> asText' <$> newNameWith' "thunk"

chainTermPlus :: TermPlus -> WithEnv [IdentifierPlus]
chainTermPlus e = do
  tenv <- gets typeEnv
  tmp <- chainTermPlus' tenv e
  return $ nubBy (\(_, x, _) (_, y, _) -> x == y) tmp

chainTermPlus' :: TypeEnv -> TermPlus -> WithEnv [IdentifierPlus]
chainTermPlus' _ (_, TermTau _) = return []
chainTermPlus' tenv (m, TermUpsilon x) = do
  t <- lookupTypeEnv'' m x tenv
  xts <- chainTermPlus' tenv t
  return $ xts ++ [(m, x, t)]
chainTermPlus' tenv (_, TermPi _ xts t) = chainTermPlus'' tenv xts [t]
chainTermPlus' tenv (_, TermPiPlus _ _ xts t) = chainTermPlus'' tenv xts [t]
chainTermPlus' tenv (_, TermPiIntro xts e) = chainTermPlus'' tenv xts [e]
chainTermPlus' tenv (_, TermPiIntroNoReduce xts e) =
  chainTermPlus'' tenv xts [e]
chainTermPlus' tenv (_, TermPiIntroPlus _ _ xts e) =
  chainTermPlus'' tenv xts [e]
chainTermPlus' tenv (_, TermPiElim e es) = do
  xs1 <- chainTermPlus' tenv e
  xs2 <- concat <$> mapM (chainTermPlus' tenv) es
  return $ xs1 ++ xs2
chainTermPlus' tenv (_, TermSigma xts) = chainTermPlus'' tenv xts []
chainTermPlus' tenv (_, TermSigmaIntro t es) = do
  xs1 <- chainTermPlus' tenv t
  xs2 <- concat <$> mapM (chainTermPlus' tenv) es
  return $ xs1 ++ xs2
chainTermPlus' tenv (_, TermSigmaElim t xts e1 e2) = do
  xs <- chainTermPlus' tenv t
  ys <- chainTermPlus' tenv e1
  zs <- chainTermPlus'' tenv xts [e2]
  return $ xs ++ ys ++ zs
chainTermPlus' tenv (_, TermIter (_, x, t) xts e) = do
  xs1 <- chainTermPlus' tenv t
  xs2 <- chainTermPlus'' (insTypeEnv'' x t tenv) xts [e]
  return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2
chainTermPlus' tenv (m, TermConst x) = do
  t <- lookupTypeEnv'' m x tenv
  chainTermPlus' tenv t
chainTermPlus' _ (_, TermFloat16 _) = return []
chainTermPlus' _ (_, TermFloat32 _) = return []
chainTermPlus' _ (_, TermFloat64 _) = return []
chainTermPlus' _ (_, TermEnum _) = return []
chainTermPlus' _ (_, TermEnumIntro _) = return []
chainTermPlus' tenv (_, TermEnumElim (e, t) les) = do
  xs0 <- chainTermPlus' tenv t
  xs1 <- chainTermPlus' tenv e
  let es = map snd les
  xs2 <- concat <$> mapM (chainTermPlus' tenv) es
  return $ xs0 ++ xs1 ++ xs2
chainTermPlus' tenv (_, TermArray dom _) = chainTermPlus' tenv dom
chainTermPlus' tenv (_, TermArrayIntro _ es) = do
  concat <$> mapM (chainTermPlus' tenv) es
chainTermPlus' tenv (_, TermArrayElim _ xts e1 e2) = do
  xs1 <- chainTermPlus' tenv e1
  xs2 <- chainTermPlus'' tenv xts [e2]
  return $ xs1 ++ xs2
chainTermPlus' _ (_, TermStruct _) = return []
chainTermPlus' tenv (_, TermStructIntro eks) =
  concat <$> mapM (chainTermPlus' tenv . fst) eks
chainTermPlus' tenv (_, TermStructElim xks e1 e2) = do
  xs1 <- chainTermPlus' tenv e1
  xs2 <- chainTermPlus' tenv e2
  let xs = map (\(_, y, _) -> y) xks
  return $ xs1 ++ filter (\(_, y, _) -> y `notElem` xs) xs2
chainTermPlus' tenv (_, TermCase (e, t) cxtes) = do
  xs <- chainTermPlus' tenv e
  ys <- chainTermPlus' tenv t
  zs <-
    concat <$> mapM (\((_, xts), body) -> chainTermPlus'' tenv xts [body]) cxtes
  return $ xs ++ ys ++ zs

chainTermPlus'' ::
     TypeEnv -> [IdentifierPlus] -> [TermPlus] -> WithEnv [IdentifierPlus]
chainTermPlus'' tenv [] es = concat <$> mapM (chainTermPlus' tenv) es
chainTermPlus'' tenv ((_, x, t):xts) es = do
  xs1 <- chainTermPlus' tenv t
  xs2 <- chainTermPlus'' (insTypeEnv'' x t tenv) xts es
  return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2

dropFst :: [(a, b, c)] -> [(b, c)]
dropFst xyzs = do
  let (_, ys, zs) = unzip3 xyzs
  zip ys zs
