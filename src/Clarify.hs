--
-- clarification == polarization + closure conversion + linearization
--
module Clarify
  ( clarify,
  )
where

import Clarify.Linearize
import Clarify.Sigma
import Clarify.Utility
import Control.Monad.State.Lazy
import Data.Basic
import Data.Code
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.List (nubBy)
import Data.Term
import qualified Data.Text as T
import Reduce.Term

clarify :: Stmt -> WithEnv CodePlus
clarify =
  clarifyStmt IntMap.empty

clarifyStmt :: SubstTerm -> Stmt -> WithEnv CodePlus
clarifyStmt sub stmt =
  case stmt of
    StmtReturn m ->
      return (m, CodeUpIntro (m, DataEnumIntro (EnumValueInt 64 0)))
    StmtLet m (_, x, t) e cont -> do
      tenv <- gets typeEnv
      e' <- clarify' tenv $ substTermPlus sub e
      t' <- clarify' tenv $ substTermPlus sub t
      constName <- newNameWith x
      let sub' = IntMap.insert (asInt x) (m, TermBoxElim constName) sub
      cont' <- clarifyStmt sub' cont
      h <- newNameWith'' "_"
      cont'' <- withHeaderAffine h t' cont' -- free the result of e'
      insCodeEnv (asText'' constName) [] e' -- box-introduction
      return (m, CodeUpElim h e' cont'')

clarify' :: TypeEnv -> TermPlus -> WithEnv CodePlus
clarify' tenv term =
  case term of
    (m, TermTau) ->
      returnCartesianImmediate m
    (m, TermUpsilon x) ->
      return (m, CodeUpIntro (m, DataUpsilon x))
    (m, TermPi {}) ->
      returnClosureType m
    (m, TermPiIntro Nothing mxts e) -> do
      fvs <- nubFVS <$> chainTermPlus tenv term
      e' <- clarify' (insTypeEnv1 mxts tenv) e
      retClosure tenv Nothing fvs (m {metaIsReducible = True}) mxts e'
    (m, TermPiIntro (Just (_, name, args)) mxts e) -> do
      e' <- clarify' (insTypeEnv1 mxts tenv) e
      let name' = showInHex name
      retClosure tenv (Just name') args (m {metaIsReducible = True}) mxts e'
    (m, TermPiElim e es) -> do
      es' <- mapM (clarifyPlus tenv) es
      e' <- clarify' tenv e
      callClosure m e' es'
    (m, TermIter (_, x, t) mxts e) -> do
      let tenv' = insTypeEnv' (asInt x) t tenv
      e' <- clarify' (insTypeEnv1 mxts tenv') e
      fvs <- nubFVS <$> chainTermPlus tenv term
      retClosureFix tenv x fvs m mxts e'
    (m, TermConst x) ->
      clarifyConst tenv m x
    (m, TermBoxElim x) ->
      return (m, CodePiElimDownElim (m, DataConst $ asText'' x) []) -- box-elimination
    (m, TermFloat size l) ->
      return (m, CodeUpIntro (m, DataFloat size l))
    (m, TermEnum _) ->
      returnCartesianImmediate m
    (m, TermEnumIntro l) ->
      return (m, CodeUpIntro (m, DataEnumIntro l))
    (m, TermEnumElim (e, _) bs) -> do
      let (cs, es) = unzip bs
      fvs <- constructEnumFVS tenv es
      es' <- (mapM (clarify' tenv) >=> alignFVS tenv m fvs) es
      let sub = IntMap.fromList $ map (\(mx, x, _) -> (asInt x, (mx, DataUpsilon x))) fvs
      (y, e', yVar) <- clarifyPlus tenv e
      return $ bindLet [(y, e')] (m, CodeEnumElim sub yVar (zip (map snd cs) es'))
    (m, TermArray {}) ->
      returnArrayType m
    (m, TermArrayIntro k es) -> do
      retImmType <- returnCartesianImmediate m
      -- arrayType = Sigma{k} [_ : IMMEDIATE, ..., _ : IMMEDIATE]
      let ts = map Left $ replicate (length es) retImmType
      arrayType <- cartesianSigma Nothing m k ts
      (zs, es', xs) <- unzip3 <$> mapM (clarifyPlus tenv) es
      return $
        bindLet
          (zip zs es')
          (m, CodeUpIntro (m, sigmaIntro [arrayType, (m, DataSigmaIntro k xs)]))
    (m, TermArrayElim k mxts e1 e2) -> do
      e1' <- clarify' tenv e1
      (arr, arrVar) <- newDataUpsilonWith m "arr"
      arrType <- newNameWith' "arr-type"
      (content, contentVar) <- newDataUpsilonWith m "arr-content"
      e2' <- clarify' (insTypeEnv1 mxts tenv) e2
      let (_, xs, _) = unzip3 mxts
      return $
        bindLet
          [(arr, e1')]
          ( m,
            sigmaElim [arrType, content] arrVar (m, CodeSigmaElim k xs contentVar e2')
          )
    (m, TermStruct ks) -> do
      t <- cartesianStruct m ks
      return (m, CodeUpIntro t)
    (m, TermStructIntro eks) -> do
      let (es, ks) = unzip eks
      (xs, es', vs) <- unzip3 <$> mapM (clarifyPlus tenv) es
      return $
        bindLet
          (zip xs es')
          (m, CodeUpIntro (m, DataStructIntro (zip vs ks)))
    (m, TermStructElim xks e1 e2) -> do
      e1' <- clarify' tenv e1
      let (ms, xs, ks) = unzip3 xks
      ts <- mapM (inferKind m) ks
      e2' <- clarify' (insTypeEnv1 (zip3 ms xs ts) tenv) e2
      (struct, structVar) <- newDataUpsilonWith m "struct"
      return $ bindLet [(struct, e1')] (m, CodeStructElim (zip xs ks) structVar e2')
    (m, TermCase _ e cxtes) -> do
      e' <- clarify' tenv e
      (cls, clsVar) <- newDataUpsilonWith m "case-closure"
      res <- newNameWith' "case-res"
      env <- newNameWith' "case-env"
      lam <- newNameWith' "label"
      cxtes' <- clarifyCase tenv m cxtes res env lam
      return $ bindLet [(cls, e')] (m, sigmaElim [res, env, lam] clsVar cxtes')

clarifyPlus :: TypeEnv -> TermPlus -> WithEnv (Ident, CodePlus, DataPlus)
clarifyPlus tenv e@(m, _) = do
  e' <- clarify' tenv e
  (varName, var) <- newDataUpsilonWith m "var"
  return (varName, e', var)

constructEnumFVS :: TypeEnv -> [TermPlus] -> WithEnv [IdentPlus]
constructEnumFVS tenv es =
  nubFVS <$> concat <$> mapM (chainTermPlus tenv) es

alignFVS :: TypeEnv -> Meta -> [IdentPlus] -> [CodePlus] -> WithEnv [CodePlus]
alignFVS tenv m fvs es = do
  es' <- mapM (retClosure tenv Nothing fvs m []) es
  mapM (\cls -> callClosure m cls []) es'

clarifyCase ::
  TypeEnv ->
  Meta ->
  [Clause] ->
  Ident ->
  Ident ->
  Ident ->
  WithEnv CodePlus
clarifyCase tenv m cxtes typeVarName envVarName lamVarName = do
  fvs <- constructCaseFVS tenv cxtes m typeVarName envVarName
  es <- (mapM (clarifyCase' tenv m envVarName) >=> alignFVS tenv m fvs) cxtes
  (y, e', yVar) <- clarifyPlus tenv (m, TermUpsilon lamVarName)
  let sub = IntMap.fromList $ map (\(mx, x, _) -> (asInt x, (mx, DataUpsilon x))) fvs
  let cs = map (\(((mc, c), _), _) -> (mc, showInHex $ asText c)) cxtes
  return $ bindLet [(y, e')] (m, CodeCase sub yVar (zip cs es))

constructCaseFVS ::
  TypeEnv ->
  [Clause] ->
  Meta ->
  Ident ->
  Ident ->
  WithEnv [IdentPlus]
constructCaseFVS tenv cxtes m typeVarName envVarName = do
  fvss <- mapM (chainCaseClause tenv) cxtes
  let fvs = nubFVS $ concat fvss
  return $
    (m, typeVarName, (m, TermTau))
      : (m, envVarName, (m, TermUpsilon typeVarName))
      : fvs

chainCaseClause :: TypeEnv -> Clause -> WithEnv [IdentPlus]
chainCaseClause tenv (((m, _), xts), body) =
  chainTermPlus tenv (m, termPiIntro xts body)

nubFVS :: [IdentPlus] -> [IdentPlus]
nubFVS =
  nubBy (\(_, x, _) (_, y, _) -> x == y)

clarifyCase' :: TypeEnv -> Meta -> Ident -> Clause -> WithEnv CodePlus
clarifyCase' tenv m envVarName ((_, xts), e) = do
  xts' <- clarifyBinder tenv xts
  e' <- clarify' tenv e >>= linearize (dropFst xts')
  let xs = map (\(_, x, _) -> x) xts
  return (m, sigmaElim xs (m, DataUpsilon envVarName) e')

clarifyConst :: TypeEnv -> Meta -> T.Text -> WithEnv CodePlus
clarifyConst tenv m x
  | Just op <- asUnaryOpMaybe x =
    clarifyUnaryOp tenv x op m
  | Just op <- asBinaryOpMaybe x =
    clarifyBinaryOp tenv x op m
  | Just _ <- asLowTypeMaybe x =
    clarify' tenv $ immType m
  | Just lowType <- asArrayAccessMaybe x =
    clarifyArrayAccess tenv m x lowType
  | x == "os:file-descriptor" =
    clarify' tenv $ immType m
  | x == "os:stdin" =
    clarify' tenv (m, TermEnumIntro (EnumValueInt 64 0))
  | x == "os:stdout" =
    clarify' tenv (m, TermEnumIntro (EnumValueInt 64 1))
  | x == "os:stderr" =
    clarify' tenv (m, TermEnumIntro (EnumValueInt 64 2))
  | x == "unsafe:cast" =
    clarifyCast tenv m
  | otherwise = do
    os <- getOS
    case asSysCallMaybe os x of
      Just (syscall, argInfo) ->
        clarifySysCall tenv x syscall argInfo m
      _ ->
        return (m, CodeUpIntro (m, DataConst x)) -- external constant

immType :: Meta -> TermPlus
immType m =
  (m, TermEnum (EnumTypeInt 64))

clarifyCast :: TypeEnv -> Meta -> WithEnv CodePlus
clarifyCast tenv m = do
  a <- newNameWith' "t1"
  b <- newNameWith' "t2"
  z <- newNameWith' "z"
  let varA = (m, TermUpsilon a)
  let u = (m, TermTau)
  clarify'
    tenv
    (m, termPiIntro [(m, a, u), (m, b, u), (m, z, varA)] (m, TermUpsilon z))

clarifyUnaryOp :: TypeEnv -> T.Text -> UnaryOp -> Meta -> WithEnv CodePlus
clarifyUnaryOp tenv name op m = do
  t <- lookupConstTypeEnv m name
  let t' = reduceTermPlus t
  case t' of
    (_, TermPi _ [(mx, x, tx)] _) -> do
      let varX = (mx, DataUpsilon x)
      retClosure
        tenv
        Nothing
        []
        m
        [(mx, x, tx)]
        (m, CodeConst (ConstUnaryOp op varX))
    _ ->
      raiseCritical m $ "the arity of " <> name <> " is wrong"

clarifyBinaryOp :: TypeEnv -> T.Text -> BinaryOp -> Meta -> WithEnv CodePlus
clarifyBinaryOp tenv name op m = do
  t <- lookupConstTypeEnv m name
  let t' = reduceTermPlus t
  case t' of
    (_, TermPi _ [(mx, x, tx), (my, y, ty)] _) -> do
      let varX = (mx, DataUpsilon x)
      let varY = (my, DataUpsilon y)
      retClosure
        tenv
        Nothing
        []
        m
        [(mx, x, tx), (my, y, ty)]
        (m, CodeConst (ConstBinaryOp op varX varY))
    _ ->
      raiseCritical m $ "the arity of " <> name <> " is wrong"

clarifyArrayAccess :: TypeEnv -> Meta -> T.Text -> LowType -> WithEnv CodePlus
clarifyArrayAccess tenv m name lowType = do
  arrayAccessType <- lookupConstTypeEnv m name
  let arrayAccessType' = reduceTermPlus arrayAccessType
  case arrayAccessType' of
    (_, TermPi _ xts cod)
      | length xts == 3 -> do
        (xs, ds, headerList) <- computeHeader m xts [ArgImm, ArgUnused, ArgArray]
        case ds of
          [index, arr] -> do
            let tenv' = insTypeEnv1 xts tenv
            callThenReturn <- toArrayAccessTail tenv' m lowType cod arr index xs
            let body = iterativeApp headerList callThenReturn
            retClosure tenv Nothing [] m xts body
          _ ->
            raiseCritical m "the type of array-access is wrong"
    _ ->
      raiseCritical m "the type of array-access is wrong"

-- ここでclsをつくる計算は省略できる (tryCache的に)
clarifySysCall ::
  TypeEnv ->
  T.Text -> -- the name of theta
  Syscall ->
  [Arg] -> -- the length of the arguments of the theta
  Meta -> -- the meta of the theta
  WithEnv CodePlus
clarifySysCall tenv name syscall args m = do
  sysCallType <- lookupConstTypeEnv m name
  let sysCallType' = reduceTermPlus sysCallType
  case sysCallType' of
    (_, TermPi _ xts cod)
      | length xts == length args -> do
        (xs, ds, headerList) <- computeHeader m xts args
        let tenv' = insTypeEnv1 xts tenv
        callThenReturn <- toSysCallTail tenv' m cod syscall ds xs
        let body = iterativeApp headerList callThenReturn
        retClosure tenv Nothing [] m xts body
    _ ->
      raiseCritical m $ "the type of " <> name <> " is wrong"

iterativeApp :: [a -> a] -> a -> a
iterativeApp functionList x =
  case functionList of
    [] ->
      x
    f : fs ->
      f (iterativeApp fs x)

clarifyBinder :: TypeEnv -> [IdentPlus] -> WithEnv [(Meta, Ident, CodePlus)]
clarifyBinder tenv binder =
  case binder of
    [] ->
      return []
    ((m, x, t) : xts) -> do
      t' <- clarify' tenv t
      xts' <- clarifyBinder (insTypeEnv' (asInt x) t tenv) xts
      return $ (m, x, t') : xts'

knot :: Meta -> Ident -> DataPlus -> WithEnv ()
knot m z cls = do
  cenv <- gets codeEnv
  case Map.lookup (asText'' z) cenv of
    Nothing ->
      raiseCritical m "knot"
    Just (Definition _ args body) -> do
      let body' = substCodePlus (IntMap.fromList [(asInt z, cls)]) body
      let def' = Definition (IsFixed True) args body'
      modify (\env -> env {codeEnv = Map.insert (asText'' z) def' cenv})

asSysCallMaybe :: OS -> T.Text -> Maybe (Syscall, [Arg])
asSysCallMaybe os name =
  case os of
    OSLinux ->
      case name of
        "os:read" ->
          return (Right ("read", 0), [ArgUnused, ArgImm, ArgArray, ArgImm])
        "os:write" ->
          return (Right ("write", 1), [ArgUnused, ArgImm, ArgArray, ArgImm])
        "os:open" ->
          return (Right ("open", 2), [ArgUnused, ArgArray, ArgImm, ArgImm])
        "os:close" ->
          return (Right ("close", 3), [ArgImm])
        "os:socket" ->
          return (Right ("socket", 41), [ArgImm, ArgImm, ArgImm])
        "os:connect" ->
          return (Right ("connect", 42), [ArgImm, ArgStruct, ArgImm])
        "os:accept" ->
          return (Right ("accept", 43), [ArgImm, ArgStruct, ArgArray])
        "os:bind" ->
          return (Right ("bind", 49), [ArgImm, ArgStruct, ArgImm])
        "os:listen" ->
          return (Right ("listen", 50), [ArgImm, ArgImm])
        "os:fork" ->
          return (Right ("fork", 57), [])
        "os:exit" ->
          return (Right ("exit", 60), [ArgUnused, ArgImm])
        "os:wait4" ->
          return (Right ("wait4", 61), [ArgImm, ArgArray, ArgImm, ArgStruct])
        _ ->
          Nothing
    OSDarwin ->
      case name of
        "os:exit" ->
          return (Left "exit", [ArgUnused, ArgImm]) -- 0x2000001
        "os:fork" ->
          return (Left "fork", []) -- 0x2000002
        "os:read" ->
          return (Left "read", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000003
        "os:write" ->
          return (Left "write", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000004
        "os:open" ->
          return (Left "open", [ArgUnused, ArgArray, ArgImm, ArgImm]) -- 0x2000005
        "os:close" ->
          return (Left "close", [ArgImm]) -- 0x2000006
        "os:wait4" ->
          return (Left "wait4", [ArgImm, ArgArray, ArgImm, ArgStruct]) -- 0x2000007
        "os:accept" ->
          return (Left "accept", [ArgImm, ArgStruct, ArgArray]) -- 0x2000030
        "os:socket" ->
          return (Left "socket", [ArgImm, ArgImm, ArgImm]) -- 0x2000097
        "os:connect" ->
          return (Left "connect", [ArgImm, ArgStruct, ArgImm]) -- 0x2000098
        "os:bind" ->
          return (Left "bind", [ArgImm, ArgStruct, ArgImm]) -- 0x2000104
        "os:listen" ->
          return (Left "listen", [ArgImm, ArgImm]) -- 0x2000106
        _ ->
          Nothing

data Arg
  = ArgImm
  | ArgArray
  | ArgStruct
  | ArgUnused
  deriving (Show)

toHeaderInfo ::
  Meta ->
  Ident -> -- argument
  TermPlus -> -- the type of argument
  Arg -> -- the way of use of argument (specifically)
  WithEnv ([IdentPlus], [DataPlus], CodePlus -> CodePlus) -- ([borrow], arg-to-syscall, ADD_HEADER_TO_CONTINUATION)
toHeaderInfo m x t argKind =
  case argKind of
    ArgImm ->
      return ([], [(m, DataUpsilon x)], id)
    ArgUnused ->
      return ([], [], id)
    ArgStruct -> do
      (structVarName, structVar) <- newDataUpsilonWith m "struct"
      return
        ( [(m, structVarName, t)],
          [structVar],
          \cont ->
            (m, CodeUpElim structVarName (m, CodeUpIntro (m, DataUpsilon x)) cont)
        )
    ArgArray -> do
      arrayVarName <- newNameWith' "array"
      (arrayTypeName, arrayType) <- newDataUpsilonWith m "array-type"
      (arrayInnerName, arrayInner) <- newDataUpsilonWith m "array-inner"
      (arrayInnerTmpName, arrayInnerTmp) <- newDataUpsilonWith m "array-tmp"
      return
        ( [(m, arrayVarName, t)],
          [arrayInnerTmp],
          \cont ->
            ( m,
              sigmaElim
                [arrayTypeName, arrayInnerName]
                (m, DataUpsilon x)
                ( m,
                  CodeUpElim
                    arrayInnerTmpName
                    (m {metaIsReducible = False}, CodeUpIntro arrayInner)
                    ( m,
                      CodeUpElim
                        arrayVarName
                        (m, CodeUpIntro (m, sigmaIntro [arrayType, arrayInnerTmp]))
                        cont
                    )
                )
            )
        )

computeHeader ::
  Meta ->
  [IdentPlus] ->
  [Arg] ->
  WithEnv ([IdentPlus], [DataPlus], [CodePlus -> CodePlus])
computeHeader m xts argInfoList = do
  let xtas = zip xts argInfoList
  (xss, dss, headerList) <-
    unzip3 <$> mapM (\((_, x, t), a) -> toHeaderInfo m x t a) xtas
  return (concat xss, concat dss, headerList)

toSysCallTail ::
  TypeEnv ->
  Meta ->
  TermPlus -> -- cod type
  Syscall -> -- read, write, open, etc
  [DataPlus] -> -- args of syscall
  [IdentPlus] -> -- borrowed variables
  WithEnv CodePlus
toSysCallTail tenv m cod syscall args xs = do
  resultVarName <- newNameWith' "result"
  result <- retWithBorrowedVars tenv m cod xs resultVarName
  return
    ( m,
      CodeUpElim resultVarName (m, CodeConst (ConstSysCall syscall args)) result
    )

toArrayAccessTail ::
  TypeEnv ->
  Meta ->
  LowType ->
  TermPlus -> -- cod type
  DataPlus -> -- array (inner)
  DataPlus -> -- index
  [IdentPlus] -> -- borrowed variables
  WithEnv CodePlus
toArrayAccessTail tenv m lowType cod arr index xts = do
  resultVarName <- newNameWith' "result"
  result <- retWithBorrowedVars tenv m cod xts resultVarName
  return
    ( m,
      CodeUpElim
        resultVarName
        (m, CodeConst (ConstArrayAccess lowType arr index))
        result
    )

retWithBorrowedVars ::
  TypeEnv ->
  Meta ->
  TermPlus ->
  [IdentPlus] ->
  Ident ->
  WithEnv CodePlus
retWithBorrowedVars tenv m cod xts resultVarName =
  if null xts
    then return (m, CodeUpIntro (m, DataUpsilon resultVarName))
    else do
      (zu, kp@(mk, k, sigArgs)) <- sigToPi m cod
      (_, resultType) <- rightmostOf sigArgs
      let xs = map (\(_, x, _) -> x) xts
      let vs = map (\x -> (m, TermUpsilon x)) $ xs ++ [resultVarName]
      -- resultの型の情報はkpの型の中にあるが。
      let tenv' = insTypeEnv1 (xts ++ [(m, resultVarName, resultType)]) tenv
      clarify'
        tenv'
        (m, termPiIntro [zu, kp] (m, TermPiElim (mk, TermUpsilon k) vs))

inferKind :: Meta -> ArrayKind -> WithEnv TermPlus
inferKind m arrayKind =
  case arrayKind of
    ArrayKindInt i ->
      return (m, TermEnum (EnumTypeInt i))
    ArrayKindFloat size -> do
      let constName = "f" <> T.pack (show (sizeAsInt size))
      return (m, TermConst constName)
    _ ->
      raiseCritical m "inferKind for void-pointer"

rightmostOf :: TermPlus -> WithEnv (Meta, TermPlus)
rightmostOf term =
  case term of
    (_, TermPi _ xts _)
      | length xts >= 1 -> do
        let (m, _, t) = last xts
        return (m, t)
    _ ->
      raiseCritical (fst term) "rightmost"

sigToPi :: Meta -> TermPlus -> WithEnv (IdentPlus, IdentPlus)
sigToPi m tPi =
  case tPi of
    (_, TermPi _ [zu, kp] _) ->
      return (zu, kp)
    _ ->
      raiseCritical m "the type of sigma-intro is wrong"

makeClosure ::
  Maybe T.Text ->
  [(Meta, Ident, CodePlus)] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Meta -> -- meta of lambda
  [(Meta, Ident, CodePlus)] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CodePlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv DataPlus
makeClosure mName mxts2 m mxts1 e = do
  let xts1 = dropFst mxts1
  let xts2 = dropFst mxts2
  envExp <- cartesianSigma Nothing m arrVoidPtr $ map Right xts2
  let vs = map (\(mx, x, _) -> (mx, DataUpsilon x)) mxts2
  let fvEnv = (m, sigmaIntro vs)
  name <- toName mName
  registerIfNecessary m name xts1 xts2 e
  return (m, sigmaIntro [envExp, fvEnv, (m, DataConst name)])

toName :: Maybe T.Text -> WithEnv T.Text
toName mName =
  case mName of
    Just name ->
      return name
    Nothing -> do
      i <- newCount
      return $ "thunk-" <> T.pack (show i)

registerIfNecessary ::
  Meta ->
  T.Text ->
  [(Ident, CodePlus)] ->
  [(Ident, CodePlus)] ->
  CodePlus ->
  WithEnv ()
registerIfNecessary m name xts1 xts2 e = do
  cenv <- gets codeEnv
  when (not $ name `Map.member` cenv) $ do
    (args, body) <- toLamInfo m xts1 xts2 e
    insCodeEnv name args body

toLamInfo ::
  Meta ->
  [(Ident, CodePlus)] ->
  [(Ident, CodePlus)] ->
  CodePlus ->
  WithEnv ([Ident], CodePlus)
toLamInfo m xts1 xts2 e = do
  e' <- linearize (xts2 ++ xts1) e
  (envVarName, envVar) <- newDataUpsilonWith m "env"
  let args = map fst xts1 ++ [envVarName]
  let body = (m, sigmaElim (map fst xts2) envVar e')
  return (args, body)

makeClosure' ::
  TypeEnv ->
  Maybe T.Text -> -- the name of newly created closure
  [IdentPlus] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Meta -> -- meta of lambda
  [IdentPlus] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CodePlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv DataPlus
makeClosure' tenv mName fvs m xts e = do
  fvs' <- clarifyBinder tenv fvs
  xts' <- clarifyBinder tenv xts
  makeClosure mName fvs' m xts' e

retClosure ::
  TypeEnv ->
  Maybe T.Text -> -- the name of newly created closure
  [IdentPlus] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Meta -> -- meta of lambda
  [IdentPlus] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CodePlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv CodePlus
retClosure tenv mName fvs m xts e = do
  cls <- makeClosure' tenv mName fvs m xts e
  return (m, CodeUpIntro cls)

retClosureFix ::
  TypeEnv ->
  Ident -> -- the name of newly created closure
  [IdentPlus] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Meta -> -- meta of lambda
  [IdentPlus] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CodePlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv CodePlus
retClosureFix tenv x fvs m xts e = do
  cls <- makeClosure' tenv (Just $ asText'' x) fvs m xts e
  knot m x cls
  return (m, CodeUpIntro cls)

callClosure ::
  Meta -> CodePlus -> [(Ident, CodePlus, DataPlus)] -> WithEnv CodePlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  (clsVarName, clsVar) <- newDataUpsilonWith m "closure"
  typeVarName <- newNameWith' "exp"
  (envVarName, envVar) <- newDataUpsilonWith m "env"
  (lamVarName, lamVar) <- newDataUpsilonWith m "thunk"
  return $
    bindLet
      ((clsVarName, e) : zip zs es')
      ( m,
        sigmaElim
          [typeVarName, envVarName, lamVarName]
          clsVar
          (m, CodePiElimDownElim lamVar (xs ++ [envVar]))
      )

chainTermPlus :: TypeEnv -> TermPlus -> WithEnv [IdentPlus]
chainTermPlus tenv term =
  case term of
    (_, TermTau) ->
      return []
    (m, TermUpsilon x) ->
      obtainChain m x tenv
    (_, TermPi _ xts t) ->
      chainTermPlus' tenv xts [t]
    (_, TermPiIntro _ xts e) ->
      chainTermPlus' tenv xts [e]
    (_, TermPiElim e es) -> do
      xs1 <- chainTermPlus tenv e
      xs2 <- concat <$> mapM (chainTermPlus tenv) es
      return $ xs1 ++ xs2
    (_, TermIter (_, x, t) xts e) -> do
      xs1 <- chainTermPlus tenv t
      xs2 <- chainTermPlus' (insTypeEnv' (asInt x) t tenv) xts [e]
      return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2
    (_, TermConst _) ->
      return []
    (_, TermBoxElim _) ->
      return []
    (_, TermFloat _ _) ->
      return []
    (_, TermEnum _) ->
      return []
    (_, TermEnumIntro _) ->
      return []
    (_, TermEnumElim (e, t) les) -> do
      xs0 <- chainTermPlus tenv t
      xs1 <- chainTermPlus tenv e
      let es = map snd les
      xs2 <- concat <$> mapM (chainTermPlus tenv) es
      return $ xs0 ++ xs1 ++ xs2
    (_, TermArray dom _) ->
      chainTermPlus tenv dom
    (_, TermArrayIntro _ es) ->
      concat <$> mapM (chainTermPlus tenv) es
    (_, TermArrayElim _ xts e1 e2) -> do
      xs1 <- chainTermPlus tenv e1
      xs2 <- chainTermPlus' tenv xts [e2]
      return $ xs1 ++ xs2
    (_, TermStruct _) ->
      return []
    (_, TermStructIntro eks) ->
      concat <$> mapM (chainTermPlus tenv . fst) eks
    (_, TermStructElim xks e1 e2) -> do
      xs1 <- chainTermPlus tenv e1
      xs2 <- chainTermPlus tenv e2
      let xs = map (\(_, y, _) -> y) xks
      return $ xs1 ++ filter (\(_, y, _) -> y `notElem` xs) xs2
    (_, TermCase _ e cxtes) -> do
      xs <- chainTermPlus tenv e
      ys <- concat <$> mapM (\((_, xts), body) -> chainTermPlus' tenv xts [body]) cxtes
      return $ xs ++ ys

chainTermPlus' :: TypeEnv -> [IdentPlus] -> [TermPlus] -> WithEnv [IdentPlus]
chainTermPlus' tenv binder es =
  case binder of
    [] ->
      concat <$> mapM (chainTermPlus tenv) es
    (_, x, t) : xts -> do
      xs1 <- chainTermPlus tenv t
      xs2 <- chainTermPlus' (insTypeEnv' (asInt x) t tenv) xts es
      return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2

dropFst :: [(a, b, c)] -> [(b, c)]
dropFst xyzs = do
  let (_, ys, zs) = unzip3 xyzs
  zip ys zs

insTypeEnv1 :: [IdentPlus] -> TypeEnv -> TypeEnv
insTypeEnv1 xts tenv =
  case xts of
    [] ->
      tenv
    (_, x, t) : rest ->
      insTypeEnv' (asInt x) t $ insTypeEnv1 rest tenv

obtainChain :: Meta -> Ident -> TypeEnv -> WithEnv [IdentPlus]
obtainChain m x tenv = do
  cenv <- gets chainEnv
  case IntMap.lookup (asInt x) cenv of
    Just xtst ->
      return xtst
    Nothing -> do
      t <- lookupTypeEnv' m x tenv
      xts <- chainTermPlus tenv t
      let chain = xts ++ [(m, x, t)]
      modify (\env -> env {chainEnv = IntMap.insert (asInt x) chain cenv})
      return chain
