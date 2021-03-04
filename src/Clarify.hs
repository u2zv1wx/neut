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
import Data.Maybe (catMaybes)
import Data.Namespace
import Data.Term
import qualified Data.Text as T

clarify :: TermPlus -> WithEnv CompPlus
clarify =
  clarify' IntMap.empty

clarify' :: TypeEnv -> TermPlus -> WithEnv CompPlus
clarify' tenv term =
  case term of
    (m, TermTau) ->
      returnCartesianImmediate m
    (m, TermUpsilon x) ->
      return (m, CompUpIntro (m, ValueUpsilon x))
    (m, TermPi {}) ->
      returnClosureType m
    (m, TermPiIntro mxts e) -> do
      fvs <- nubFVS <$> chainOf tenv term
      e' <- clarify' (insTypeEnv mxts tenv) e
      retClosure tenv Nothing fvs m mxts e'
    (m, TermPiElim e es) -> do
      es' <- mapM (clarifyPlus tenv) es
      e' <- clarify' tenv e
      callClosure m e' es'
    (m, TermFix (_, x, t) mxts e) -> do
      let tenv' = IntMap.insert (asInt x) t tenv
      e' <- clarify' (insTypeEnv mxts tenv') e
      fvs <- nubFVS <$> chainOf tenv term
      retClosure tenv (Just x) fvs m mxts e'
    (m, TermConst x) ->
      clarifyConst tenv m x
    (m, TermInt size l) ->
      return (m, CompUpIntro (m, ValueInt size l))
    (m, TermFloat size l) ->
      return (m, CompUpIntro (m, ValueFloat size l))
    (m, TermEnum _) ->
      returnCartesianImmediate m
    (m, TermEnumIntro l) ->
      return (m, CompUpIntro (m, ValueEnumIntro l))
    (m, TermEnumElim (e, _) bs) -> do
      let (cs, es) = unzip bs
      fvs <- constructEnumFVS tenv es
      es' <- (mapM (clarify' tenv) >=> alignFVS tenv m fvs) es
      (y, e', yVar) <- clarifyPlus tenv e
      return $ bindLet [(y, e')] (m, CompEnumElim yVar (zip (map snd cs) es'))
    (m, TermTensor {}) ->
      returnCartesianImmediate m -- `tensor`s must be used linearly
    (m, TermTensorIntro es) -> do
      (zs, es', xs) <- unzip3 <$> mapM (clarifyPlus tenv) es
      return $ bindLet (zip zs es') (m, CompUpIntro (m, ValueSigmaIntro xs))
    (m, TermTensorElim xts e1 e2) -> do
      (zName, e1', z) <- clarifyPlus tenv e1
      let (_, xs, _) = unzip3 xts
      e2' <- clarify' (insTypeEnv xts tenv) e2
      return $ bindLet [(zName, e1')] (m, CompSigmaElim xs z e2')
    (m, TermDerangement expKind resultType ekts) -> do
      let (es, ks, ts) = unzip3 ekts
      xs <- mapM (const $ newNameWith' "sys") es
      let xts = zipWith (\x t -> (fst t, x, t)) xs ts
      let borrowedVarList = catMaybes $ map takeIffLinear (zip xts ks)
      let xsAsVars = map (\(mx, x, _) -> (mx, ValueUpsilon x)) xts
      resultVarName <- newNameWith' "result"
      tuple <- constructResultTuple tenv m borrowedVarList (m, resultVarName, resultType)
      let lamBody = (m, CompUpElim resultVarName (m, CompPrimitive (PrimitiveDerangement expKind xsAsVars)) tuple)
      cls <- retClosure tenv Nothing [] m xts lamBody
      es' <- mapM (clarifyPlus tenv) es
      callClosure m cls es'

clarifyPlus :: TypeEnv -> TermPlus -> WithEnv (Ident, CompPlus, ValuePlus)
clarifyPlus tenv e@(m, _) = do
  e' <- clarify' tenv e
  (varName, var) <- newValueUpsilonWith m "var"
  return (varName, e', var)

clarifyBinder :: TypeEnv -> [IdentPlus] -> WithEnv [(Hint, Ident, CompPlus)]
clarifyBinder tenv binder =
  case binder of
    [] ->
      return []
    ((m, x, t) : xts) -> do
      t' <- clarify' tenv t
      xts' <- clarifyBinder (IntMap.insert (asInt x) t tenv) xts
      return $ (m, x, t') : xts'

constructEnumFVS :: TypeEnv -> [TermPlus] -> WithEnv [IdentPlus]
constructEnumFVS tenv es =
  nubFVS <$> concat <$> mapM (chainOf tenv) es

alignFVS :: TypeEnv -> Hint -> [IdentPlus] -> [CompPlus] -> WithEnv [CompPlus]
alignFVS tenv m fvs es = do
  es' <- mapM (retClosure tenv Nothing fvs m []) es
  mapM (\cls -> callClosure m cls []) es'

nubFVS :: [IdentPlus] -> [IdentPlus]
nubFVS =
  nubBy (\(_, x, _) (_, y, _) -> x == y)

clarifyConst :: TypeEnv -> Hint -> T.Text -> WithEnv CompPlus
clarifyConst tenv m x
  | Just op <- asPrimOp x =
    clarifyPrimOp tenv op m
  | Just _ <- asLowTypeMaybe x =
    returnCartesianImmediate m
  | x == nsOS <> "file-descriptor" =
    returnCartesianImmediate m
  | x == nsOS <> "stdin" =
    clarify' tenv (m, TermInt 64 0)
  | x == nsOS <> "stdout" =
    clarify' tenv (m, TermInt 64 1)
  | x == nsOS <> "stderr" =
    clarify' tenv (m, TermInt 64 2)
  | x == nsUnsafe <> "pointer" =
    returnCartesianImmediate m
  | x == nsUnsafe <> "cast" =
    clarifyCast tenv m
  | otherwise = do
    renv <- gets resTypeEnv
    case Map.lookup x renv of
      Nothing ->
        return (m, CompUpIntro (m, ValueConst x))
      Just (discarder, copier) -> do
        v <- tryCache m x $ do
          discarder' <- toSwitcherBranch m tenv discarder
          copier' <- toSwitcherBranch m tenv copier
          registerSwitcher m x discarder' copier'
        return (m, CompUpIntro v)

clarifyCast :: TypeEnv -> Hint -> WithEnv CompPlus
clarifyCast tenv m = do
  a <- newNameWith' "t1"
  b <- newNameWith' "t2"
  z <- newNameWith' "z"
  let varA = (m, TermUpsilon a)
  let u = (m, TermTau)
  clarify' tenv (m, TermPiIntro [(m, a, u), (m, b, u), (m, z, varA)] (m, TermUpsilon z))

clarifyPrimOp :: TypeEnv -> PrimOp -> Hint -> WithEnv CompPlus
clarifyPrimOp tenv op@(PrimOp _ domList _) m = do
  argTypeList <- mapM (lowTypeToType m) domList
  (xs, varList) <- unzip <$> mapM (const (newValueUpsilonWith m "prim")) domList
  let mxts = zipWith (\x t -> (m, x, t)) xs argTypeList
  retClosure tenv Nothing [] m mxts (m, CompPrimitive (PrimitivePrimOp op varList))

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
    then return (m, CompUpIntro (m, ValueUpsilon resultVarName))
    else do
      let tupleTypeInfo = borrowedVarTypeList ++ [result]
      tuple <- termSigmaIntro m tupleTypeInfo
      let tenv' = insTypeEnv tupleTypeInfo tenv
      clarify' tenv' tuple

makeClosure ::
  Maybe Ident ->
  [(Hint, Ident, CompPlus)] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Hint -> -- meta of lambda
  [(Hint, Ident, CompPlus)] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CompPlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv ValuePlus
makeClosure mName mxts2 m mxts1 e = do
  let xts1 = dropFst mxts1
  let xts2 = dropFst mxts2
  envExp <- cartesianSigma Nothing m $ map Right xts2
  let vs = map (\(mx, x, _) -> (mx, ValueUpsilon x)) mxts2
  let fvEnv = (m, ValueSigmaIntro vs)
  case mName of
    Nothing -> do
      i <- newCount
      let name = "thunk-" <> T.pack (show i)
      registerIfNecessary m name False xts1 xts2 e
      return (m, ValueSigmaIntro [envExp, fvEnv, (m, ValueConst name)])
    Just name -> do
      let cls = (m, ValueSigmaIntro [envExp, fvEnv, (m, ValueConst $ asText'' name)])
      let e' = substCompPlus (IntMap.fromList [(asInt name, cls)]) e
      registerIfNecessary m (asText'' name) True xts1 xts2 e'
      return cls

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
    (envVarName, envVar) <- newValueUpsilonWith m "env"
    let args = map fst xts1 ++ [envVarName]
    let body = (m, CompSigmaElim (map fst xts2) envVar e')
    insCompEnv name isFixed args body

makeClosure' ::
  TypeEnv ->
  Maybe Ident -> -- the name of newly created closure
  [IdentPlus] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Hint -> -- meta of lambda
  [IdentPlus] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CompPlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv ValuePlus
makeClosure' tenv mName fvs m xts e = do
  fvs' <- clarifyBinder tenv fvs
  xts' <- clarifyBinder tenv xts
  makeClosure mName fvs' m xts' e

retClosure ::
  TypeEnv ->
  Maybe Ident -> -- the name of newly created closure
  [IdentPlus] -> -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  Hint -> -- meta of lambda
  [IdentPlus] -> -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  CompPlus -> -- the `e` in `lam (x1, ..., xn). e`
  WithEnv CompPlus
retClosure tenv mName fvs m xts e = do
  cls <- makeClosure' tenv mName fvs m xts e
  return (m, CompUpIntro cls)

callClosure :: Hint -> CompPlus -> [(Ident, CompPlus, ValuePlus)] -> WithEnv CompPlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  (clsVarName, clsVar) <- newValueUpsilonWith m "closure"
  typeVarName <- newNameWith' "exp"
  (envVarName, envVar) <- newValueUpsilonWith m "env"
  (lamVarName, lamVar) <- newValueUpsilonWith m "thunk"
  return $
    bindLet
      ((clsVarName, e) : zip zs es')
      ( m,
        CompSigmaElim
          [typeVarName, envVarName, lamVarName]
          clsVar
          (m, CompPiElimDownElim lamVar (xs ++ [envVar]))
      )

chainOf :: TypeEnv -> TermPlus -> WithEnv [IdentPlus]
chainOf tenv term =
  case term of
    (_, TermTau) ->
      return []
    (m, TermUpsilon x) -> do
      t <- lookupTypeEnv m x tenv
      xts <- chainOf tenv t
      return $ xts ++ [(m, x, t)]
    (_, TermPi {}) ->
      return []
    (_, TermPiIntro xts e) ->
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
  z <- newNameWith' "internal.sigma-tau-tuple"
  let vz = (m, TermUpsilon z)
  k <- newNameWith'' "sigma"
  let args = map (\(mx, x, _) -> (mx, TermUpsilon x)) xts
  return
    ( m,
      TermPiIntro
        [ (m, z, (m, TermTau)),
          (m, k, (m, TermPi xts vz))
        ]
        (m, TermPiElim (m, TermUpsilon k) args)
    )

toSwitcherBranch :: Hint -> TypeEnv -> TermPlus -> WithEnv (ValuePlus -> WithEnv CompPlus)
toSwitcherBranch m tenv d = do
  d' <- clarify' tenv d
  (varName, var) <- newValueUpsilonWith m "res"
  return $ \val -> callClosure m d' [(varName, (m, CompUpIntro val), var)]
