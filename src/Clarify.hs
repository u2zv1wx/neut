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
import Data.Comp
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.List (nubBy)
import Data.Log
import Data.LowType
import Data.Maybe (catMaybes, maybeToList)
import qualified Data.Set as S
import Data.Term
import qualified Data.Text as T
import Reduce.Comp

data ClosureName
  = ClosureNameAnonymous
  | ClosureNameFix Ident
  | ClosureNameConstructor T.Text

clarify :: [Stmt] -> WithEnv CompPlus
clarify ss = do
  e <- clarifyStmt IntMap.empty ss
  reduceCompPlus e

clarifyStmt :: TypeEnv -> [Stmt] -> WithEnv CompPlus
clarifyStmt tenv ss =
  case ss of
    [] -> do
      m <- newHint 1 1 <$> getCurrentFilePath
      return (m, CompUpIntro (m, ValueInt 64 0))
    StmtDef m (mx, x, t) e : cont -> do
      e' <- clarifyTerm tenv e >>= reduceCompPlus
      insCompEnv (toGlobalVarName x) False [] e'
      cont' <- clarifyStmt (insTypeEnv [(mx, x, t)] tenv) cont
      holeVarName <- newIdentFromText "hole"
      let app = (m, CompPiElimDownElim (m, ValueConst (toGlobalVarName x)) [])
      return (m, CompUpElim holeVarName app cont')
    StmtResourceType m name discarder copier : cont -> do
      discarder' <- toSwitcherBranch m tenv discarder
      copier' <- toSwitcherBranch m tenv copier
      registerSwitcher m name discarder' copier'
      clarifyStmt tenv cont

clarifyTerm :: TypeEnv -> TermPlus -> WithEnv CompPlus
clarifyTerm tenv term =
  case term of
    (m, TermTau) ->
      returnImmediateS4 m
    (m, TermVar x) -> do
      senv <- gets substEnv
      oenv <- gets opaqueEnv
      if (not $ IntMap.member (asInt x) senv) && (not (S.member x oenv))
        then return (m, CompUpIntro (m, ValueVar x))
        else return (m, CompPiElimDownElim (m, ValueConst (toGlobalVarName x)) [])
    (m, TermPi {}) ->
      returnClosureS4 m
    (m, TermPiIntro mName mxts e) -> do
      e' <- clarifyTerm (insTypeEnv mxts tenv) e
      fvs <- nubFreeVariables <$> chainOf tenv term
      case mName of
        Nothing ->
          retClosure tenv ClosureNameAnonymous fvs m mxts e'
        Just (_, consName) ->
          retClosure tenv (ClosureNameConstructor consName) fvs m mxts e'
    (m, TermPiElim e es) -> do
      es' <- mapM (clarifyPlus tenv) es
      e' <- clarifyTerm tenv e
      callClosure m e' es'
    (m, TermFix (mx, x, t) mxts e) -> do
      e' <- clarifyTerm (insTypeEnv ((mx, x, t) : mxts) tenv) e
      fvs <- nubFreeVariables <$> chainOf tenv term
      if S.member x (varComp e')
        then retClosure tenv (ClosureNameFix x) fvs m mxts e'
        else retClosure tenv ClosureNameAnonymous fvs m mxts e'
    (m, TermConst x) ->
      clarifyConst tenv m x
    (m, TermInt size l) ->
      return (m, CompUpIntro (m, ValueInt size l))
    (m, TermFloat size l) ->
      return (m, CompUpIntro (m, ValueFloat size l))
    (m, TermEnum _) ->
      returnImmediateS4 m
    (m, TermEnumIntro l) ->
      return (m, CompUpIntro (m, ValueEnumIntro l))
    (m, TermEnumElim (e, _) bs) -> do
      let (cs, es) = unzip bs
      fvs <- chainFromTermList tenv es
      es' <- (mapM (clarifyTerm tenv) >=> alignFreeVariables tenv m fvs) es
      (y, e', yVar) <- clarifyPlus tenv e
      return $ bindLet [(y, e')] (m, CompEnumElim yVar (zip (map snd cs) es'))
    (m, TermTensor {}) ->
      returnImmediateS4 m -- `tensor`s must be used linearly
    (m, TermTensorIntro es) -> do
      (zs, es', xs) <- unzip3 <$> mapM (clarifyPlus tenv) es
      return $ bindLet (zip zs es') (m, CompUpIntro (m, ValueSigmaIntro xs))
    (m, TermTensorElim xts e1 e2) -> do
      (zName, e1', z) <- clarifyPlus tenv e1
      e2' <- clarifyTerm (insTypeEnv xts tenv) e2
      let (_, xs, _) = unzip3 xts
      return $ bindLet [(zName, e1')] (m, CompSigmaElim xs z e2')
    (m, TermDerangement expKind resultType ekts) -> do
      case (expKind, ekts) of
        (DerangementNop, [(e, _, _)]) ->
          clarifyTerm tenv e
        _ -> do
          let (es, ks, ts) = unzip3 ekts
          (xs, es', xsAsVars) <- unzip3 <$> mapM (clarifyPlus tenv) es
          let xts = zipWith (\x t -> (fst t, x, t)) xs ts
          let borrowedVarList = catMaybes $ map takeIffLinear (zip xts ks)
          resultVarName <- newIdentFromText "result"
          tuple <- constructResultTuple tenv m borrowedVarList (m, resultVarName, resultType)
          let lamBody = bindLet (zip xs es') (m, CompUpElim resultVarName (m, CompPrimitive (PrimitiveDerangement expKind xsAsVars)) tuple)
          h <- newIdentFromText "der"
          fvs <- nubFreeVariables <$> chainOf' tenv xts es
          cls <- retClosure tenv (ClosureNameFix h) fvs m [] lamBody -- cls shouldn't be reduced since it can be effectful
          callClosure m cls []
    (m, TermCase resultType mSubject (e, _) patList) -> do
      -- let (tvar, env, tag) := e in
      -- case tag of
      --   0 ->
      --     NIL_INTERNAL  @ (result-type, clause-closure-for-nil, null,  env)
      --   1 ->
      --     CONS_INTERNAL @ (result-type, null, clause-closure-for-cons, env)
      case mSubject of
        -- case
        Nothing -> do
          fvs <- chainFromTermList tenv $ map (caseClauseToLambda m) patList
          resultType' <- clarifyPlus tenv resultType
          ((closureVarName, closureVar), typeVarName, (tagVarName, tagVar), (envVarName, envVar)) <- newClosureNames m
          branchList <- forM (zip patList [0 ..]) $ \(((constructorName, xts), body), i) -> do
            body' <- clarifyTerm tenv body
            clauseClosure <- retClosure tenv ClosureNameAnonymous fvs m xts body'
            -- baseArgs == [null, ..., null, clauseClosure, null, ..., null]
            --              0          i-1   i              i+1        (length patList - 1)
            baseArgs <- constructArguments clauseClosure i $ length patList - 1
            let (argVarNameList, argList, argVarList) = unzip3 (resultType' : baseArgs)
            return $
              ( EnumCaseInt i,
                bindLet
                  (zip argVarNameList argList)
                  ( m,
                    CompPiElimDownElim
                      (m, ValueConst (toConstructorLabelName constructorName))
                      (argVarList ++ [envVar]) -- argVarList ++ [envVar] == [resultType, null, ..., null, clauseClosure, null, ..., null, env]
                  )
              )
          closure <- clarifyTerm tenv e
          return $
            bindLet
              [(closureVarName, closure)]
              ( m,
                CompSigmaElim
                  [typeVarName, envVarName, tagVarName]
                  closureVar
                  (m, CompEnumElim tagVar branchList)
              )
        -- case-noetic
        Just _ ->
          undefined

newClosureNames :: Hint -> WithEnv ((Ident, ValuePlus), Ident, (Ident, ValuePlus), (Ident, ValuePlus))
newClosureNames m = do
  closureVarInfo <- newValueVarWith m "closure"
  typeVarName <- newIdentFromText "exp"
  envVarInfo <- newValueVarWith m "env"
  lamVarInfo <- newValueVarWith m "thunk"
  return (closureVarInfo, typeVarName, envVarInfo, lamVarInfo)

-- (closureVarName, closureVar) <- newValueVarWith m "closure"
-- typeVarName <- newIdentFromText "exp"
-- (envVarName, envVar) <- newValueVarWith m "env"
-- (lamVarName, lamVar) <- newValueVarWith m "thunk"
-- return ()

caseClauseToLambda :: Hint -> (Pattern, TermPlus) -> TermPlus
caseClauseToLambda m pat =
  case pat of
    ((_, xts), body) ->
      (m, TermPiIntro Nothing xts body)

constructArguments :: CompPlus -> Int -> Int -> WithEnv [(Ident, CompPlus, ValuePlus)]
constructArguments cls clsIndex upperBound = do
  (innerClsVarName, innerClsVar) <- newValueVarWith (fst cls) "var"
  constructArguments' (innerClsVarName, cls, innerClsVar) clsIndex 0 upperBound

constructArguments' :: (Ident, CompPlus, ValuePlus) -> Int -> Int -> Int -> WithEnv [(Ident, CompPlus, ValuePlus)]
constructArguments' clsInfo clsIndex cursor upperBound = do
  if cursor == upperBound
    then return []
    else do
      rest <- constructArguments' clsInfo clsIndex (cursor + 1) upperBound
      if cursor == clsIndex
        then return $ clsInfo : rest
        else do
          let (_, (m, _), _) = clsInfo
          (argVarName, argVar) <- newValueVarWith m "arg"
          return $ (argVarName, (m, CompUpIntro (m, ValueSigmaIntro [])), argVar) : rest

clarifyPlus :: TypeEnv -> TermPlus -> WithEnv (Ident, CompPlus, ValuePlus)
clarifyPlus tenv e@(m, _) = do
  e' <- clarifyTerm tenv e
  (varName, var) <- newValueVarWith m "var"
  return (varName, e', var)

clarifyBinder :: TypeEnv -> [IdentPlus] -> WithEnv [(Hint, Ident, CompPlus)]
clarifyBinder tenv binder =
  case binder of
    [] ->
      return []
    ((m, x, t) : xts) -> do
      t' <- clarifyTerm tenv t
      xts' <- clarifyBinder (IntMap.insert (asInt x) t tenv) xts
      return $ (m, x, t') : xts'

chainFromTermList :: TypeEnv -> [TermPlus] -> WithEnv [IdentPlus]
chainFromTermList tenv es =
  nubFreeVariables <$> concat <$> mapM (chainOf tenv) es

-- alignFreeVariable :: TypeEnv -> Hint -> [IdentPlus] -> CompPlus -> WithEnv CompPlus
-- alignFreeVariable tenv m fvs e = do
--   e' <- retClosure tenv ClosureNameAnonymous fvs m [] e
--   callClosure m e' []

alignFreeVariables :: TypeEnv -> Hint -> [IdentPlus] -> [CompPlus] -> WithEnv [CompPlus]
alignFreeVariables tenv m fvs es = do
  es' <- mapM (retClosure tenv ClosureNameAnonymous fvs m []) es
  mapM (\cls -> callClosure m cls []) es'

nubFreeVariables :: [IdentPlus] -> [IdentPlus]
nubFreeVariables =
  nubBy (\(_, x, _) (_, y, _) -> x == y)

clarifyConst :: TypeEnv -> Hint -> T.Text -> WithEnv CompPlus
clarifyConst tenv m constName
  | Just op <- asPrimOp constName =
    clarifyPrimOp tenv op m
  | Just _ <- asLowTypeMaybe constName =
    returnImmediateS4 m
  | otherwise = do
    cenv <- gets codeEnv
    if Map.member constName cenv
      then return (m, CompUpIntro (m, ValueConst constName))
      else raiseError m $ "undefined constant: " <> constName

clarifyPrimOp :: TypeEnv -> PrimOp -> Hint -> WithEnv CompPlus
clarifyPrimOp tenv op@(PrimOp _ domList _) m = do
  argTypeList <- mapM (lowTypeToType m) domList
  (xs, varList) <- unzip <$> mapM (const (newValueVarWith m "prim")) domList
  let mxts = zipWith (\x t -> (m, x, t)) xs argTypeList
  retClosure tenv ClosureNameAnonymous [] m mxts (m, CompPrimitive (PrimitivePrimOp op varList))

takeIffLinear :: (IdentPlus, DerangementArg) -> Maybe IdentPlus
takeIffLinear (xt, k) =
  case k of
    DerangementArgAffine ->
      Nothing
    DerangementArgLinear ->
      Just xt

-- generate tuple like (borrowed-1, ..., borrowed-n, result)
constructResultTuple ::
  TypeEnv ->
  Hint ->
  [IdentPlus] ->
  IdentPlus ->
  WithEnv CompPlus
constructResultTuple tenv m borrowedVarTypeList result@(_, resultVarName, _) =
  if null borrowedVarTypeList
    then return (m, CompUpIntro (m, ValueVar resultVarName))
    else do
      let tupleTypeInfo = borrowedVarTypeList ++ [result]
      tuple <- termSigmaIntro m tupleTypeInfo
      let tenv' = insTypeEnv tupleTypeInfo tenv
      clarifyTerm tenv' tuple

makeClosure ::
  ClosureName ->
  [(Hint, Ident, CompPlus)] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Hint -> -- meta of lambda
  [(Hint, Ident, CompPlus)] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CompPlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv ValuePlus
makeClosure mName mxts2 m mxts1 e = do
  let xts1 = dropFst mxts1
  let xts2 = dropFst mxts2
  envExp <- sigmaS4 Nothing m $ map Right xts2
  let vs = map (\(mx, x, _) -> (mx, ValueVar x)) mxts2
  let fvEnv = (m, ValueSigmaIntro vs)
  case mName of
    ClosureNameAnonymous -> do
      i <- newCount
      let name = "thunk-" <> T.pack (show i)
      registerIfNecessary m name False xts1 xts2 e
      return (m, ValueSigmaIntro [envExp, fvEnv, (m, ValueConst name)])
    ClosureNameFix name -> do
      let cls = (m, ValueSigmaIntro [envExp, fvEnv, (m, ValueConst (toGlobalVarName name))])
      e' <- substCompPlus (IntMap.fromList [(asInt name, cls)]) IntMap.empty e
      registerIfNecessary m (toGlobalVarName name) True xts1 xts2 e'
      return cls
    ClosureNameConstructor name -> do
      cenv <- gets constructorEnv
      case Map.lookup name cenv of
        Just (_, k) -> do
          let cls = (m, ValueSigmaIntro [envExp, fvEnv, (m, ValueInt 64 (toInteger k))])
          registerIfNecessary m (wrapWithQuote name) True xts1 xts2 e
          return cls
        Nothing ->
          raiseCritical m $ "no such constructor is registered: `" <> name <> "`"

registerIfNecessary ::
  Hint ->
  T.Text ->
  Bool ->
  [(Ident, CompPlus)] ->
  [(Ident, CompPlus)] ->
  CompPlus ->
  WithEnv ()
registerIfNecessary m name isFixed xts1 xts2 e = do
  cenv <- gets codeEnv
  when (not $ name `Map.member` cenv) $ do
    e' <- linearize (xts2 ++ xts1) e
    (envVarName, envVar) <- newValueVarWith m "env"
    let args = map fst xts1 ++ [envVarName]
    body <- reduceCompPlus (m, CompSigmaElim (map fst xts2) envVar e')
    insCompEnv name isFixed args body

retClosure ::
  TypeEnv ->
  ClosureName -> -- the name of newly created closure
  [IdentPlus] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Hint -> -- meta of lambda
  [IdentPlus] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CompPlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv CompPlus
retClosure tenv mName fvs m xts e = do
  fvs' <- clarifyBinder tenv fvs
  xts' <- clarifyBinder tenv xts
  cls <- makeClosure mName fvs' m xts' e
  return (m, CompUpIntro cls)

callClosure :: Hint -> CompPlus -> [(Ident, CompPlus, ValuePlus)] -> WithEnv CompPlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  ((closureVarName, closureVar), typeVarName, (envVarName, envVar), (lamVarName, lamVar)) <- newClosureNames m
  return $
    bindLet
      ((closureVarName, e) : zip zs es')
      ( m,
        CompSigmaElim
          [typeVarName, envVarName, lamVarName]
          closureVar
          (m, CompPiElimDownElim lamVar (xs ++ [envVar]))
      )

chainOf :: TypeEnv -> TermPlus -> WithEnv [IdentPlus]
chainOf tenv term =
  case term of
    (_, TermTau) ->
      return []
    (m, TermVar x) -> do
      t <- lookupTypeEnv m x tenv
      xts <- chainOf tenv t
      senv <- gets substEnv
      oenv <- gets opaqueEnv
      if (not $ IntMap.member (asInt x) senv) && (not (S.member x oenv))
        then return $ xts ++ [(m, x, t)]
        else return $ xts
    (_, TermPi {}) ->
      return []
    (_, TermPiIntro _ xts e) ->
      chainOf' tenv xts [e]
    (_, TermPiElim e es) -> do
      xs1 <- chainOf tenv e
      xs2 <- concat <$> mapM (chainOf tenv) es
      return $ xs1 ++ xs2
    (_, TermFix (_, x, t) xts e) -> do
      xs1 <- chainOf tenv t
      xs2 <- chainOf' (IntMap.insert (asInt x) t tenv) xts [e]
      return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2
    (_, TermConst _) ->
      return []
    (_, TermInt _ _) ->
      return []
    (_, TermFloat _ _) ->
      return []
    (_, TermEnum _) ->
      return []
    (_, TermEnumIntro _) ->
      return []
    (_, TermEnumElim (e, t) les) -> do
      xs0 <- chainOf tenv t
      xs1 <- chainOf tenv e
      let es = map snd les
      xs2 <- concat <$> mapM (chainOf tenv) es
      return $ xs0 ++ xs1 ++ xs2
    (_, TermTensor ts) ->
      concat <$> mapM (chainOf tenv) ts
    (_, TermTensorIntro es) ->
      concat <$> mapM (chainOf tenv) es
    (_, TermTensorElim xts e1 e2) -> do
      xs1 <- chainOf tenv e1
      xs2 <- chainOf' tenv xts [e2]
      return $ xs1 ++ xs2
    (_, TermDerangement _ _ ekts) -> do
      let (es, _, ts) = unzip3 ekts
      concat <$> mapM (chainOf tenv) (es ++ ts)
    (_, TermCase _ mSubject (e, _) patList) -> do
      xs1 <- concat <$> (mapM (chainOf tenv) $ maybeToList mSubject)
      xs2 <- chainOf tenv e
      xs3 <- concat <$> (forM patList $ \((_, xts), body) -> chainOf' tenv xts [body])
      return $ xs1 ++ xs2 ++ xs3

chainOf' :: TypeEnv -> [IdentPlus] -> [TermPlus] -> WithEnv [IdentPlus]
chainOf' tenv binder es =
  case binder of
    [] ->
      concat <$> mapM (chainOf tenv) es
    (_, x, t) : xts -> do
      xs1 <- chainOf tenv t
      xs2 <- chainOf' (IntMap.insert (asInt x) t tenv) xts es
      return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2

dropFst :: [(a, b, c)] -> [(b, c)]
dropFst xyzs = do
  let (_, ys, zs) = unzip3 xyzs
  zip ys zs

insTypeEnv :: [IdentPlus] -> TypeEnv -> TypeEnv
insTypeEnv xts tenv =
  case xts of
    [] ->
      tenv
    (_, x, t) : rest ->
      insTypeEnv rest $ IntMap.insert (asInt x) t tenv

lookupTypeEnv :: Hint -> Ident -> TypeEnv -> WithEnv TermPlus
lookupTypeEnv m (I (name, x)) tenv =
  case IntMap.lookup x tenv of
    Just t ->
      return t
    Nothing ->
      raiseCritical m $
        "the variable `" <> name <> "` is not found in the type environment."

termSigmaIntro :: Hint -> [IdentPlus] -> WithEnv TermPlus
termSigmaIntro m xts = do
  z <- newIdentFromText "internal.sigma-tau-tuple"
  let vz = (m, TermVar z)
  k <- newIdentFromText "sigma"
  let args = map (\(mx, x, _) -> (mx, TermVar x)) xts
  return
    ( m,
      TermPiIntro
        Nothing
        [ (m, z, (m, TermTau)),
          (m, k, (m, TermPi xts vz))
        ]
        (m, TermPiElim (m, TermVar k) args)
    )

toSwitcherBranch :: Hint -> TypeEnv -> TermPlus -> WithEnv (ValuePlus -> WithEnv CompPlus)
toSwitcherBranch m tenv d = do
  d' <- clarifyTerm tenv d
  (varName, var) <- newValueVarWith m "res"
  return $ \val -> callClosure m d' [(varName, (m, CompUpIntro val), var)] >>= reduceCompPlus
