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
import Clarify.Linearize
import Clarify.Sigma
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
import Data.Term
import Reduce.Term

clarify :: TermPlus -> WithEnv CodePlus
clarify (m, TermTau _) = do
  v <- cartesianImmediate m
  return (m, CodeUpIntro v)
clarify (m, TermUpsilon x) = return (m, CodeUpIntro (m, DataUpsilon x))
clarify (m, TermPi {}) = do
  returnClosureType m
clarify (m, TermPiPlus {}) = do
  returnClosureType m
clarify lam@(m, TermPiIntro mxts e) = do
  let (_, xs, ts) = unzip3 mxts
  let xts = zip xs ts
  forM_ xts $ uncurry insTypeEnv'
  e' <- clarify e
  fvs <- chainTermPlus lam
  retClosure Nothing fvs m mxts e'
clarify lam@(m, TermPiIntroNoReduce mxts e) = do
  let (_, xs, ts) = unzip3 mxts
  let xts = zip xs ts
  forM_ xts $ uncurry insTypeEnv'
  e' <- clarify e
  fvs <- chainTermPlus lam
  retClosure Nothing fvs m mxts e'
clarify (m, TermPiIntroPlus _ (name, args) mxts e) = do
  let (_, xs, ts) = unzip3 mxts
  let xts = zip xs ts
  forM_ xts $ uncurry insTypeEnv'
  e' <- clarify e
  case varTermPlus (m, TermPiIntro args termZero) of
    [] -> retClosure (Just name) args m mxts e'
    _ ->
      raiseError m $
      "couldn't normalize the type of the inductive closure at compile time"
clarify (m, TermPiElim e es) = do
  es' <- mapM clarifyPlus es
  e' <- clarify e
  callClosure m e' es'
clarify (m, TermSigma _) = returnClosureType m -- Sigma is translated into Pi
clarify (m, TermSigmaIntro t es) = do
  let t' = reduceTermPlus t
  case t' of
    (mSig, TermSigma xts)
      | length xts == length es -> do
        tPi <- sigToPi mSig xts
        case tPi of
          (_, TermPi _ [zu, kp@(_, k, (_, TermPi _ yts _))] _) -- i.e. Sigma yts
            | length yts == length es -> do
              let xvs = map (\(_, x, _) -> toTermUpsilon x) yts
              let kv = toTermUpsilon k
              -- eager product
              let bindArgsThen = \e -> (m, TermPiElim (m, TermPiIntro yts e) es)
              clarify $
                bindArgsThen (m, TermPiIntro [zu, kp] (m, TermPiElim kv xvs))
          _ -> raiseCritical m "the type of sigma-intro is wrong"
    _ -> raiseCritical m "the type of sigma-intro is wrong"
clarify (m, TermSigmaElim t xts e1 e2) = do
  clarify (m, TermPiElim e1 [t, (emptyMeta, TermPiIntro xts e2)])
clarify iter@(m, TermIter (_, x, t) mxts e) = do
  let (_, xs, ts) = unzip3 mxts
  let xts = zip xs ts
  forM_ ((x, t) : xts) $ uncurry insTypeEnv'
  e' <- clarify e
  fvs <- chainTermPlus iter
  retClosure' x fvs m mxts e'
clarify (m, TermConst x) = clarifyConst m x
clarify (_, TermConstDecl (_, x, t) e) = do
  _ <- clarify t
  insTypeEnv' x t
  clarify e
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
clarify (m, TermEnumElim (e, _) bs) = do
  let (cs, es) = unzip bs
  fvss <- mapM chainTermPlus' es
  let fvs = nubBy (\(_, x, _) (_, y, _) -> x == y) $ concat fvss
  es' <- mapM clarify es
  clarifyEnumElim m fvs e $ zip cs es'
clarify (m, TermArray {}) = do
  returnArrayType m
clarify (m, TermArrayIntro k es) = do
  retImmType <- returnCartesianImmediate
  -- arrayType = Sigma{k} [_ : IMMEDIATE, ..., _ : IMMEDIATE]
  name <- newNameWith' "array"
  let ts = map Left $ replicate (length es) retImmType
  arrayType <- cartesianSigma name m k ts
  (zs, es', xs) <- unzip3 <$> mapM clarifyPlus es
  return $
    bindLet (zip zs es') $
    ( m
    , CodeUpIntro $
      (m, DataSigmaIntro arrVoidPtr [arrayType, (m, DataSigmaIntro k xs)]))
clarify (m, TermArrayElim k mxts e1 e2) = do
  e1' <- clarify e1
  let (_, xs, ts) = unzip3 mxts
  let xts = zip xs ts
  forM_ xts $ uncurry insTypeEnv'
  (arrVarName, arrVar) <- newDataUpsilonWith "arr"
  (arrTypeVarName, _) <- newDataUpsilonWith "arr-type"
  (arrInnerVarName, arrInnerVar) <- newDataUpsilonWith "arr-inner"
  e2' <- clarify e2
  return $
    bindLet [(arrVarName, e1')] $
    ( m
    , CodeSigmaElim
        arrVoidPtr
        [arrTypeVarName, arrInnerVarName]
        arrVar
        (m, CodeSigmaElim k xs arrInnerVar e2'))
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
  let (_, xs, ks) = unzip3 xks
  ts <- mapM inferKind ks
  forM_ (zip xs ts) $ uncurry insTypeEnv'
  e2' <- clarify e2
  (structVarName, structVar) <- newDataUpsilonWith "struct"
  return $
    bindLet [(structVarName, e1')] (m, CodeStructElim (zip xs ks) structVar e2')
clarify (m, TermCase (e, _) cxtes) = do
  e' <- clarify e
  (clsVarName, clsVar) <- newDataUpsilonWith "case-closure"
  (typeVarName, _) <- newDataUpsilonWith "case-exp"
  (envVarName, _) <- newDataUpsilonWith "case-env"
  (lamVarName, _) <- newDataUpsilonWith "thunk"
  cxtes' <- clarifyCase m cxtes typeVarName envVarName lamVarName
  return $
    bindLet
      [(clsVarName, e')]
      ( m
      , CodeSigmaElim
          arrVoidPtr
          [typeVarName, envVarName, lamVarName]
          clsVar
          cxtes')

clarifyPlus :: TermPlus -> WithEnv (Identifier, CodePlus, DataPlus)
clarifyPlus e@(m, _) = do
  e' <- clarify e
  (varName, var) <- newDataUpsilonWith' "var" m
  return (varName, e', var)

clarifyEnumElim ::
     Meta
  -> [(Meta, Identifier, TermPlus)]
  -> TermPlus
  -> [(Case, CodePlus)]
  -> WithEnv CodePlus
clarifyEnumElim m fvs e bs = do
  let (cs, es) = unzip bs
  es' <- mapM (retClosure Nothing fvs m []) es
  es'' <- mapM (\cls -> callClosure m cls []) es'
  (yName, e', y) <- clarifyPlus e
  let varInfo = map (\(mx, x, _) -> (x, toDataUpsilon (x, mx))) fvs
  return $ bindLet [(yName, e')] (m, CodeEnumElim varInfo y (zip cs es''))

clarifyCase ::
     Meta
  -> [((Identifier, [(Meta, Identifier, TermPlus)]), TermPlus)]
  -> Identifier
  -> Identifier
  -> Identifier
  -> WithEnv CodePlus
clarifyCase m cxtes typeVarName envVarName lamVarName = do
  let cs = map (\((c, _), _) -> c) cxtes
  es <- mapM (\cxte -> clarifyCase' m cxte envVarName) cxtes
  let lamVar = toTermUpsilon lamVarName
  fvss <- mapM chainCaseClause cxtes
  let fvs = nubBy (\(_, x, _) (_, y, _) -> x == y) $ concat fvss
  let typeVarPlus = (m, typeVarName, (m, TermTau 0))
  let typeVar = (m, TermUpsilon typeVarName)
  let envVarPlus = (m, envVarName, typeVar)
  let fvs' = [typeVarPlus, envVarPlus] ++ fvs
  es' <- mapM (retClosure Nothing fvs' m []) es
  es'' <- mapM (\cls -> callClosure m cls []) es'
  (yName, e', y) <- clarifyPlus lamVar
  let varInfo = map (\(mx, x, _) -> (x, toDataUpsilon (x, mx))) fvs'
  return $
    bindLet [(yName, e')] (m, CodeCase varInfo y (zip (map asText cs) es''))

chainCaseClause ::
     ((Identifier, [(Meta, Identifier, TermPlus)]), TermPlus)
  -> WithEnv [(Meta, Identifier, TermPlus)]
chainCaseClause ((_, xts), body) = do
  let (_, xs, ts) = unzip3 xts
  forM_ (zip xs ts) $ uncurry insTypeEnv'
  fvs <- chainTermPlus' body
  return $ filter (\(_, y, _) -> y `notElem` xs) fvs

clarifyCase' ::
     Meta
  -> ((Identifier, [(Meta, Identifier, TermPlus)]), TermPlus)
  -> Identifier
  -> WithEnv CodePlus
clarifyCase' m ((_, xts), e) envVarName = do
  e' <- clarify e
  xts' <- mapM clarifyArgs xts
  e'' <- linearize xts' e'
  let xs = map (\(_, x, _) -> x) xts
  return (m, CodeSigmaElim arrVoidPtr xs (toDataUpsilon' envVarName) e'')

clarifyArgs :: (Meta, Identifier, TermPlus) -> WithEnv (Identifier, CodePlus)
clarifyArgs (_, x, t) = do
  t' <- clarify t
  return (x, t')

clarifyConst :: Meta -> Identifier -> WithEnv CodePlus
clarifyConst m name@(I (x, _))
  | Just op <- asUnaryOpMaybe x = clarifyUnaryOp name op m
clarifyConst m name@(I (x, _))
  | Just op <- asBinaryOpMaybe x = clarifyBinaryOp name op m
clarifyConst m (I (x, _))
  | Just _ <- asLowTypeMaybe x = clarify (m, TermEnum $ EnumTypeLabel "top")
clarifyConst m name@(I (x, _))
  | Just lowType <- asArrayAccessMaybe x = clarifyArrayAccess m name lowType
clarifyConst m (I ("file-descriptor", _)) = do
  i <- lookupConstNum "i64"
  clarify (m, TermConst (I ("i64", i)))
clarifyConst m (I ("stdin", _)) =
  clarify (m, TermEnumIntro (EnumValueIntS 64 0))
clarifyConst m (I ("stdout", _)) =
  clarify (m, TermEnumIntro (EnumValueIntS 64 1))
clarifyConst m (I ("stderr", _)) =
  clarify (m, TermEnumIntro (EnumValueIntS 64 2))
clarifyConst m (I ("unsafe-cast", _))
  -- unsafe-cast : Pi (A : tau, B : tau, _ : A). B
  -- ~> (lam ((A tau) (B tau) (x A)) x)
  -- (note that we're treating the `x` in the function body as if of type B)
 = do
  a <- newNameWith' "t1"
  b <- newNameWith' "t2"
  x <- newNameWith' "x"
  l <- newCount
  let varA = (m, TermUpsilon a)
  let u = (m, TermTau l)
  clarify
    (m, TermPiIntro [(m, a, u), (m, b, u), (m, x, varA)] (m, TermUpsilon x))
clarifyConst m name@(I (x, _)) = do
  os <- getOS
  case asSysCallMaybe os x of
    Just (syscall, argInfo) -> clarifySysCall name syscall argInfo m
    Nothing -> return (m, CodeUpIntro (m, DataTheta $ asText' name))

clarifyUnaryOp :: Identifier -> UnaryOp -> Meta -> WithEnv CodePlus
clarifyUnaryOp name op m = do
  t <- lookupTypeEnv' name
  let t' = reduceTermPlus t
  case t' of
    (_, TermPi _ xts@[(mx, x, tx)] _) -> do
      let varX = toDataUpsilon (x, mx)
      zts <- complementaryChainOf xts
      retClosure
        (Just $ asText' name)
        zts
        m
        [(mx, x, tx)]
        (m, CodeTheta (ThetaUnaryOp op varX))
    _ -> raiseCritical m $ "the arity of " <> asText name <> " is wrong"

clarifyBinaryOp :: Identifier -> BinaryOp -> Meta -> WithEnv CodePlus
clarifyBinaryOp name op m = do
  t <- lookupTypeEnv' name
  let t' = reduceTermPlus t
  case t' of
    (_, TermPi _ xts@[(mx, x, tx), (my, y, ty)] _) -> do
      let varX = toDataUpsilon (x, mx)
      let varY = toDataUpsilon (y, my)
      zts <- complementaryChainOf xts
      retClosure
        (Just $ asText' name)
        zts
        m
        [(mx, x, tx), (my, y, ty)]
        (m, CodeTheta (ThetaBinaryOp op varX varY))
    _ -> raiseCritical m $ "the arity of " <> asText name <> " is wrong"

clarifyArrayAccess :: Meta -> Identifier -> LowType -> WithEnv CodePlus
clarifyArrayAccess m name lowType = do
  arrayAccessType <- lookupTypeEnv' name
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
            retClosure (Just $ asText' name) zts m xts body
          _ -> raiseCritical m $ "the type of array-access is wrong"
    _ -> raiseCritical m $ "the type of array-access is wrong"

clarifySysCall ::
     Identifier -- the name of theta
  -> Syscall
  -> [Arg] -- the length of the arguments of the theta
  -> Meta -- the meta of the theta
  -> WithEnv CodePlus
clarifySysCall name syscall args m = do
  sysCallType <- lookupTypeEnv' name
  let sysCallType' = reduceTermPlus sysCallType
  case sysCallType' of
    (_, TermPi _ xts cod)
      | length xts == length args -> do
        zts <- complementaryChainOf xts
        (xs, ds, headerList) <- computeHeader m xts args
        callThenReturn <- toSysCallTail m cod syscall ds xs
        let body = iterativeApp headerList callThenReturn
        retClosure (Just $ asText' name) zts m xts body
    _ -> raiseCritical m $ "the type of " <> asText name <> " is wrong"

iterativeApp :: [a -> a] -> a -> a
iterativeApp [] x = x
iterativeApp (f:fs) x = f (iterativeApp fs x)

complementaryChainOf ::
     [(Meta, Identifier, TermPlus)] -> WithEnv [(Meta, Identifier, TermPlus)]
complementaryChainOf xts = do
  zts <- chainTermPlus'' xts []
  return $ nubBy (\(_, x, _) (_, y, _) -> x == y) zts

toVar :: Identifier -> DataPlus
toVar x = (emptyMeta, DataUpsilon x)

clarifyBinder ::
     [(Meta, Identifier, TermPlus)] -> WithEnv [(Meta, Identifier, CodePlus)]
clarifyBinder [] = return []
clarifyBinder ((m, x, t):xts) = do
  t' <- clarify t
  xts' <- clarifyBinder xts
  return $ (m, x, t') : xts'

retClosure ::
     Maybe T.Text -- the name of newly created closure
  -> [(Meta, Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Meta, Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
retClosure mName fvs m xts e = do
  cls <- makeClosure' mName fvs m xts e
  return (m, CodeUpIntro cls)

retClosure' ::
     Identifier -- the name of newly created closure
  -> [(Meta, Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Meta, Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
retClosure' x fvs m xts e = do
  cls <- makeClosure' (Just $ asText' x) fvs m xts e
  knot x cls
  return (m, CodeUpIntro cls)

makeClosure' ::
     Maybe T.Text -- the name of newly created closure
  -> [(Meta, Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Meta, Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv DataPlus
makeClosure' mName fvs m xts e = do
  fvs' <- clarifyBinder fvs
  xts' <- clarifyBinder xts
  makeClosure mName fvs' m xts' e

knot :: Identifier -> DataPlus -> WithEnv ()
knot z cls = do
  cenv <- gets codeEnv
  case Map.lookup (asText' z) cenv of
    Nothing -> raiseCritical' "knot"
    Just (Definition _ args body) -> do
      let body' = substCodePlus [(z, cls)] body
      let def' = Definition (IsFixed True) args body'
      modify (\env -> env {codeEnv = Map.insert (asText' z) def' cenv})

asSysCallMaybe :: OS -> T.Text -> Maybe (Syscall, [Arg])
asSysCallMaybe OSLinux name =
  case name of
    "read" -> return (Right (name, 0), [ArgUnused, ArgImm, ArgArray, ArgImm])
    "write" -> return (Right (name, 1), [ArgUnused, ArgImm, ArgArray, ArgImm])
    "open" -> return (Right (name, 2), [ArgUnused, ArgArray, ArgImm, ArgImm])
    "close" -> return (Right (name, 3), [ArgImm])
    "socket" -> return (Right (name, 41), [ArgImm, ArgImm, ArgImm])
    "connect" -> return (Right (name, 42), [ArgImm, ArgStruct, ArgImm])
    "accept" -> return (Right (name, 43), [ArgImm, ArgStruct, ArgArray])
    "bind" -> return (Right (name, 49), [ArgImm, ArgStruct, ArgImm])
    "listen" -> return (Right (name, 50), [ArgImm, ArgImm])
    "fork" -> return (Right (name, 57), [])
    "exit" -> return (Right (name, 60), [ArgImm])
    "wait4" -> return (Right (name, 61), [ArgImm, ArgArray, ArgImm, ArgStruct])
    _ -> Nothing
asSysCallMaybe OSDarwin name =
  case name of
    "exit" -> return (Left name, [ArgImm]) -- 0x2000001
    "fork" -> return (Left name, []) -- 0x2000002
    "read" -> return (Left name, [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000003
    "write" -> return (Left name, [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000004
    "open" -> return (Left name, [ArgUnused, ArgArray, ArgImm, ArgImm]) -- 0x2000005
    "close" -> return (Left name, [ArgImm]) -- 0x2000006
    "wait4" -> return (Left name, [ArgImm, ArgArray, ArgImm, ArgStruct]) -- 0x2000007
    "accept" -> return (Left name, [ArgImm, ArgStruct, ArgArray]) -- 0x2000030
    "socket" -> return (Left name, [ArgImm, ArgImm, ArgImm]) -- 0x2000097
    "connect" -> return (Left name, [ArgImm, ArgStruct, ArgImm]) -- 0x2000098
    "bind" -> return (Left name, [ArgImm, ArgStruct, ArgImm]) -- 0x2000104
    "listen" -> return (Left name, [ArgImm, ArgImm]) -- 0x2000106
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
toHeaderInfo _ x _ ArgImm = return ([], [toVar x], id)
toHeaderInfo _ _ _ ArgUnused = return ([], [], id)
toHeaderInfo m x t ArgStruct = do
  (structVarName, structVar) <- newDataUpsilonWith "struct"
  insTypeEnv' structVarName t
  return
    ( [structVarName]
    , [structVar]
    , \cont -> (m, CodeUpElim structVarName (m, CodeUpIntro (toVar x)) cont))
toHeaderInfo m x t ArgArray = do
  arrayVarName <- newNameWith' "array"
  insTypeEnv' arrayVarName t
  (arrayTypeName, arrayType) <- newDataUpsilonWith "array-type"
  (arrayInnerName, arrayInner) <- newDataUpsilonWith "array-inner"
  (arrayInnerTmpName, arrayInnerTmp) <- newDataUpsilonWith "array-tmp"
  return
    ( [arrayVarName]
    , [arrayInnerTmp]
    , \cont ->
        ( m
        , CodeSigmaElim
            arrVoidPtr
            [arrayTypeName, arrayInnerName]
            (toVar x)
            ( m
            , CodeUpElim
                arrayInnerTmpName
                (m, CodeUpIntroNoReduce arrayInner)
                ( m
                , CodeUpElim
                    arrayVarName
                    ( m
                    , CodeUpIntro
                        ( m
                        , DataSigmaIntro arrVoidPtr [arrayType, arrayInnerTmp]))
                    cont -- contの中でarrayInnerTmpを使用することで配列を利用
                 ))))

computeHeader ::
     Meta
  -> [(Meta, Identifier, TermPlus)]
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
retWithBorrowedVars m cod xs resultVarName
  | (mSig, TermSigma yts) <- cod
  , length yts >= 1 = do
    tPi <- sigToPi mSig yts
    case tPi of
      (_, TermPi _ [c, (mFun, funName, funType@(_, TermPi _ xts _))] _) -> do
        let (_, _, resultType) = last xts
        let vs = map (\x -> (m, TermUpsilon x)) $ xs ++ [resultVarName]
        insTypeEnv' resultVarName resultType
        clarify
          ( m
          , TermPiIntro
              [c, (mFun, funName, funType)]
              (m, TermPiElim (m, TermUpsilon funName) vs))
      _ -> raiseCritical m "retWithBorrowedVars (sig)"
  | otherwise = raiseCritical m "retWithBorrowedVars"

inferKind :: ArrayKind -> WithEnv TermPlus
inferKind (ArrayKindIntS i) = return (emptyMeta, TermEnum (EnumTypeIntS i))
inferKind (ArrayKindIntU i) = return (emptyMeta, TermEnum (EnumTypeIntU i))
inferKind (ArrayKindFloat size) = do
  let constName = "f" <> T.pack (show (sizeAsInt size))
  i <- lookupConstNum' constName
  return (emptyMeta, TermConst (I (constName, i)))
inferKind _ = raiseCritical' "inferKind for void-pointer"

sigToPi :: Meta -> [Data.Term.IdentifierPlus] -> WithEnv TermPlus
sigToPi m xts = do
  z <- newNameWith' "sigma"
  let zv = toTermUpsilon z
  k <- newNameWith' "sig"
  -- Sigma [x1 : A1, ..., xn : An] = Pi (z : Type, _ : Pi [x1 : A1, ..., xn : An]. z). z
  l <- newCount
  -- don't care the level since they're discarded immediately
  -- (i.e. this translated term is not used as an argument of `weaken`)
  return
    (m, TermPi [] [(m, z, (m, TermTau l)), (m, k, (m, TermPi [] xts zv))] zv)
