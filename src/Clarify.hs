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
import Data.Maybe (catMaybes, isJust, maybeToList)
import qualified Data.Set as S
import Data.Term
import qualified Data.Text as T
import Reduce.Comp

clarify :: [Stmt] -> Compiler CompPlus
clarify =
  clarifyStmt IntMap.empty >=> reduceCompPlus

clarifyStmt :: TypeEnv -> [Stmt] -> Compiler CompPlus
clarifyStmt tenv ss =
  case ss of
    [] -> do
      m <- newHint 1 1 <$> getCurrentFilePath
      return (m, CompUpIntro (m, ValueInt 64 0))
    StmtDef m mx t e : cont -> do
      case mx of
        Just x -> do
          e' <- clarifyTerm tenv e >>= reduceCompPlus
          insDefEnv (toGlobalVarName x) True [] e' -- implicit S4 box introduction
          clarifyStmt (insTypeEnv [(m, x, t)] tenv) cont
        Nothing -> do
          e' <- clarifyTerm tenv e
          result <- newIdentFromText "result"
          cont' <- clarifyStmt tenv cont
          t' <- clarifyTerm tenv t
          discardResult <- toAffineApp m result t'
          hole <- newIdentFromText "unit"
          return (m, CompUpElim result e' (m, CompUpElim hole discardResult cont'))

clarifyTerm :: TypeEnv -> TermPlus -> Compiler CompPlus
clarifyTerm tenv term =
  case term of
    (m, TermTau) ->
      returnImmediateS4 m
    (m, TermVar kind x) -> do
      case kind of
        VarKindLocal ->
          return (m, CompUpIntro (m, ValueVarLocal x))
        _ ->
          return (m, CompPiElimDownElim (m, ValueVarGlobal (toGlobalVarName x)) []) -- implicit S4 box elimination
    (m, TermPi {}) ->
      returnClosureS4 m
    (m, TermPiIntro opacity kind mxts e) -> do
      e' <- clarifyTerm (insTypeEnv (catMaybes [fromLamKind kind] ++ mxts) tenv) e
      let fvs = nubFreeVariables $ chainOf tenv term
      case (opacity, kind) of
        (OpacityTranslucent, LamKindFix (_, x, _))
          | not (S.member x (varComp e')) ->
            returnClosure tenv True LamKindNormal fvs m mxts e'
        _ ->
          returnClosure tenv (isTransparent opacity) kind fvs m mxts e'
    (m, TermPiElim e es) -> do
      es' <- mapM (clarifyPlus tenv) es
      e' <- clarifyTerm tenv e
      callClosure m e' es'
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
      let fvs = chainFromTermList tenv es
      es' <- (mapM (clarifyTerm tenv) >=> alignFreeVariables tenv m fvs) es
      (y, e', yVar) <- clarifyPlus tenv e
      return $ bindLet [(y, e')] (m, CompEnumElim yVar (zip (map snd cs) es'))
    (m, TermDerangement expKind es) -> do
      case (expKind, es) of
        (DerangementNop, [e]) ->
          clarifyTerm tenv e
        _ -> do
          (xs, es', xsAsVars) <- unzip3 <$> mapM (clarifyPlus tenv) es
          return $ bindLet (zip xs es') (m, CompPrimitive (PrimitiveDerangement expKind xsAsVars))
    (m, TermCase resultType mSubject (e, _) patList) -> do
      let fvs = chainFromTermList tenv $ map (caseClauseToLambda m) patList
      resultArg <- clarifyPlus tenv resultType
      closure <- clarifyTerm tenv e
      ((closureVarName, closureVar), typeVarName, (envVarName, envVar), (tagVarName, tagVar)) <- newClosureNames m
      branchList <- forM (zip patList [0 ..]) $ \(((constructorName, xts), body), i) -> do
        body' <- clarifyTerm (insTypeEnv xts tenv) body
        clauseClosure <- returnClosure tenv True LamKindNormal fvs m xts body'
        closureArgs <- constructClauseArguments clauseClosure i $ length patList
        let (argVarNameList, argList, argVarList) = unzip3 (resultArg : closureArgs)
        let consName = wrapWithQuote $ if isJust mSubject then asText constructorName <> ";noetic" else asText constructorName
        return $
          ( EnumCaseInt i,
            bindLet
              (zip argVarNameList argList)
              ( m,
                CompPiElimDownElim
                  (m, ValueVarGlobal consName)
                  (argVarList ++ [envVar])
              )
          )
      return $
        ( m,
          CompUpElim
            closureVarName
            closure
            ( m,
              CompSigmaElim
                (isJust mSubject)
                [typeVarName, envVarName, tagVarName]
                closureVar
                (m, CompEnumElim tagVar branchList)
            )
        )

newClosureNames :: Hint -> Compiler ((Ident, ValuePlus), Ident, (Ident, ValuePlus), (Ident, ValuePlus))
newClosureNames m = do
  closureVarInfo <- newValueVarLocalWith m "closure"
  typeVarName <- newIdentFromText "exp"
  envVarInfo <- newValueVarLocalWith m "env"
  lamVarInfo <- newValueVarLocalWith m "thunk"
  return (closureVarInfo, typeVarName, envVarInfo, lamVarInfo)

caseClauseToLambda :: Hint -> (Pattern, TermPlus) -> TermPlus
caseClauseToLambda m pat =
  case pat of
    ((_, xts), body) ->
      (m, TermPiIntro OpacityTransparent LamKindNormal xts body)

constructClauseArguments :: CompPlus -> Int -> Int -> Compiler [(Ident, CompPlus, ValuePlus)]
constructClauseArguments cls clsIndex upperBound = do
  (innerClsVarName, innerClsVar) <- newValueVarLocalWith (fst cls) "var"
  constructClauseArguments' (innerClsVarName, cls, innerClsVar) clsIndex 0 upperBound

constructClauseArguments' :: (Ident, CompPlus, ValuePlus) -> Int -> Int -> Int -> Compiler [(Ident, CompPlus, ValuePlus)]
constructClauseArguments' clsInfo clsIndex cursor upperBound = do
  if cursor == upperBound
    then return []
    else do
      rest <- constructClauseArguments' clsInfo clsIndex (cursor + 1) upperBound
      if cursor == clsIndex
        then return $ clsInfo : rest
        else do
          let (_, (m, _), _) = clsInfo
          (argVarName, argVar) <- newValueVarLocalWith m "arg"
          fakeClosure <- makeFakeClosure m
          return $ (argVarName, (m, CompUpIntro fakeClosure), argVar) : rest

makeFakeClosure :: Hint -> Compiler ValuePlus
makeFakeClosure m = do
  imm <- immediateS4 m
  return (m, ValueSigmaIntro [imm, (m, ValueInt 64 0), (m, ValueInt 64 0)])

clarifyPlus :: TypeEnv -> TermPlus -> Compiler (Ident, CompPlus, ValuePlus)
clarifyPlus tenv e@(m, _) = do
  e' <- clarifyTerm tenv e
  (varName, var) <- newValueVarLocalWith m "var"
  return (varName, e', var)

clarifyBinder :: TypeEnv -> [IdentPlus] -> Compiler [(Hint, Ident, CompPlus)]
clarifyBinder tenv binder =
  case binder of
    [] ->
      return []
    ((m, x, t) : xts) -> do
      t' <- clarifyTerm tenv t
      xts' <- clarifyBinder (IntMap.insert (asInt x) t tenv) xts
      return $ (m, x, t') : xts'

chainFromTermList :: TypeEnv -> [TermPlus] -> [IdentPlus]
chainFromTermList tenv es =
  nubFreeVariables $ concat $ map (chainOf tenv) es

alignFreeVariables :: TypeEnv -> Hint -> [IdentPlus] -> [CompPlus] -> Compiler [CompPlus]
alignFreeVariables tenv m fvs es = do
  es' <- mapM (returnClosure tenv True LamKindNormal fvs m []) es
  mapM (\cls -> callClosure m cls []) es'

nubFreeVariables :: [IdentPlus] -> [IdentPlus]
nubFreeVariables =
  nubBy (\(_, x, _) (_, y, _) -> x == y)

clarifyConst :: TypeEnv -> Hint -> T.Text -> Compiler CompPlus
clarifyConst tenv m constName
  | Just op <- asPrimOp constName =
    clarifyPrimOp tenv op m
  | Just _ <- asLowTypeMaybe constName =
    returnImmediateS4 m
  | otherwise = do
    raiseCritical m $ "undefined constant: " <> constName

clarifyPrimOp :: TypeEnv -> PrimOp -> Hint -> Compiler CompPlus
clarifyPrimOp tenv op@(PrimOp _ domList _) m = do
  argTypeList <- mapM (lowTypeToType m) domList
  (xs, varList) <- unzip <$> mapM (const (newValueVarLocalWith m "prim")) domList
  let mxts = zipWith (\x t -> (m, x, t)) xs argTypeList
  returnClosure tenv True LamKindNormal [] m mxts (m, CompPrimitive (PrimitivePrimOp op varList))

returnClosure ::
  TypeEnv ->
  Bool -> -- whether the closure is reducible
  LamKind IdentPlus -> -- the name of newly created closure
  [IdentPlus] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Hint -> -- meta of lambda
  [IdentPlus] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CompPlus -> -- the `e` in `lam (x1, ..., xn). e`
  Compiler CompPlus
returnClosure tenv isReducible kind fvs m xts e = do
  fvs' <- clarifyBinder tenv fvs
  xts' <- clarifyBinder tenv xts
  let xts'' = dropFst xts'
  let fvs'' = dropFst fvs'
  fvEnvSigma <- sigmaS4 Nothing m $ map Right fvs''
  let fvEnv = (m, ValueSigmaIntro (map (\(mx, x, _) -> (mx, ValueVarLocal x)) fvs'))
  case kind of
    LamKindNormal -> do
      i <- newCount
      let name = "thunk-" <> T.pack (show i)
      registerIfNecessary m name isReducible False xts'' fvs'' e
      return (m, CompUpIntro (m, ValueSigmaIntro [fvEnvSigma, fvEnv, (m, ValueVarGlobal (wrapWithQuote name))]))
    LamKindCons _ consName -> do
      cenv <- gets constructorEnv
      case Map.lookup consName cenv of
        Just (_, constructorNumber) -> do
          registerIfNecessary m consName isReducible True xts'' fvs'' e
          return (m, CompUpIntro (m, ValueSigmaIntro [fvEnvSigma, fvEnv, (m, ValueInt 64 (toInteger constructorNumber))]))
        Nothing ->
          raiseCritical m $ "no such constructor is registered: `" <> consName <> "`"
    LamKindFix (_, name, _) -> do
      let name' = asText' name
      let cls = (m, ValueSigmaIntro [fvEnvSigma, fvEnv, (m, ValueVarGlobal (wrapWithQuote name'))])
      e' <- substCompPlus (IntMap.fromList [(asInt name, cls)]) IntMap.empty e
      registerIfNecessary m name' False False xts'' fvs'' e'
      return (m, CompUpIntro cls)
    LamKindResourceHandler -> do
      when (not (null fvs'')) $
        raiseError m "this resource-lambda is not closed"
      e' <- linearize xts'' e >>= reduceCompPlus
      i <- newCount
      let name = "resource-handler-" <> T.pack (show i)
      insDefEnv (wrapWithQuote name) isReducible (map fst xts'') e'
      return (m, CompUpIntro (m, ValueVarGlobal (wrapWithQuote name)))

registerIfNecessary ::
  Hint ->
  T.Text ->
  Bool ->
  Bool ->
  [(Ident, CompPlus)] ->
  [(Ident, CompPlus)] ->
  CompPlus ->
  Compiler ()
registerIfNecessary m name isReducible isNoetic xts1 xts2 e = do
  denv <- gets defEnv
  when (not $ name `Map.member` denv) $ do
    e' <- linearize (xts2 ++ xts1) e
    (envVarName, envVar) <- newValueVarLocalWith m "env"
    let args = map fst xts1 ++ [envVarName]
    body <- reduceCompPlus (m, CompSigmaElim False (map fst xts2) envVar e')
    insDefEnv (wrapWithQuote name) isReducible args body
    when isNoetic $ do
      bodyNoetic <- reduceCompPlus (m, CompSigmaElim True (map fst xts2) envVar e')
      insDefEnv (wrapWithQuote $ name <> ";noetic") isReducible args bodyNoetic

callClosure :: Hint -> CompPlus -> [(Ident, CompPlus, ValuePlus)] -> Compiler CompPlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  ((closureVarName, closureVar), typeVarName, (envVarName, envVar), (lamVarName, lamVar)) <- newClosureNames m
  return $
    bindLet
      ((closureVarName, e) : zip zs es')
      ( m,
        CompSigmaElim
          False
          [typeVarName, envVarName, lamVarName]
          closureVar
          (m, CompPiElimDownElim lamVar (xs ++ [envVar]))
      )

chainOf :: TypeEnv -> TermPlus -> [IdentPlus]
chainOf tenv term =
  case term of
    (_, TermTau) ->
      []
    (m, TermVar opacity x) -> do
      case opacity of
        VarKindLocal -> do
          let t = (IntMap.!) tenv (asInt x)
          let xts = chainOf tenv t
          xts ++ [(m, x, t)]
        _ ->
          []
    (_, TermPi {}) ->
      []
    (_, TermPiIntro _ kind xts e) ->
      chainOf' tenv (catMaybes [fromLamKind kind] ++ xts) [e]
    (_, TermPiElim e es) -> do
      let xs1 = chainOf tenv e
      let xs2 = concat $ map (chainOf tenv) es
      xs1 ++ xs2
    (_, TermConst _) ->
      []
    (_, TermInt _ _) ->
      []
    (_, TermFloat _ _) ->
      []
    (_, TermEnum _) ->
      []
    (_, TermEnumIntro _) ->
      []
    (_, TermEnumElim (e, t) les) -> do
      let xs0 = chainOf tenv t
      let xs1 = chainOf tenv e
      let es = map snd les
      let xs2 = concat $ map (chainOf tenv) es
      xs0 ++ xs1 ++ xs2
    (_, TermDerangement _ es) ->
      concat $ map (chainOf tenv) es
    (_, TermCase _ mSubject (e, _) patList) -> do
      let xs1 = concat $ (map (chainOf tenv) $ maybeToList mSubject)
      let xs2 = chainOf tenv e
      let xs3 = concat $ (flip map patList $ \((_, xts), body) -> chainOf' tenv xts [body])
      xs1 ++ xs2 ++ xs3

chainOf' :: TypeEnv -> [IdentPlus] -> [TermPlus] -> [IdentPlus]
chainOf' tenv binder es =
  case binder of
    [] ->
      concat $ map (chainOf tenv) es
    (_, x, t) : xts -> do
      let xs1 = chainOf tenv t
      let xs2 = chainOf' (IntMap.insert (asInt x) t tenv) xts es
      xs1 ++ filter (\(_, y, _) -> y /= x) xs2

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
