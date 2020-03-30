{-# LANGUAGE OverloadedStrings #-}

module Parse.Rule
  ( parseInductive
  , insForm
  , insInductive
  , internalize
  , toVar'
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Monoid ((<>))

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm
import Parse.Interpret

parseInductive :: Meta -> [TreePlus] -> WithEnv [QuasiStmt]
parseInductive m ts = parseConnective m ts toInductive toInductiveIntroList

-- variable naming convention on parsing connectives:
--   a : the name of a formation rule, like `nat`, `list`, `stream`, etc.
--   b : the name of an introduction/elimination rule, like `zero`, `cons`, `head`, etc.
--   x : the name of an argument of a formation rule, like `A` in `list A` or `stream A`.
--   y : the name of an argument of an introduction/elimination rule, like `w` or `ws` in `cons : Pi (w : A, ws : list A). list A`.
parseConnective ::
     Meta
  -> [TreePlus]
  -> ([IdentifierPlus] -> [IdentifierPlus] -> Connective -> WithEnv [QuasiStmt])
  -> ([IdentifierPlus] -> Connective -> WithEnv [QuasiStmt])
  -> WithEnv [QuasiStmt]
parseConnective m ts f g = do
  connectiveList <- mapM parseConnective' ts
  fs <- mapM formationRuleOf' connectiveList
  ats <- mapM ruleAsIdentPlus fs
  bts <- concat <$> mapM toInternalRuleList connectiveList
  checkNameSanity m $ ats ++ bts
  connectiveList' <- concat <$> mapM (f ats bts) connectiveList
  ruleList <- concat <$> mapM (g ats) connectiveList
  return $ connectiveList' ++ ruleList

parseConnective' :: TreePlus -> WithEnv Connective
parseConnective' (m, TreeNode ((_, TreeLeaf name):(_, TreeNode xts):rules)) = do
  m' <- adjustPhase m
  xts' <- mapM interpretIdentifierPlus xts
  rules' <- mapM parseRule rules
  return (m', asIdent name, xts', rules')
parseConnective' t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) ...)"

parseRule :: TreePlus -> WithEnv Rule
parseRule (m, TreeNode [(mName, TreeLeaf name), (_, TreeNode xts), t]) = do
  m' <- adjustPhase m
  mName' <- adjustPhase mName
  t' <- interpret t
  xts' <- mapM interpretIdentifierPlus xts
  return (m', asIdent name, mName', xts', t')
parseRule t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) TREE)"

-- renameFormArgs ::
--      [IdentifierPlus]
--   -> WeakTermPlus
--   -> WithEnv ([IdentifierPlus], WeakTermPlus)
-- renameFormArgs [] tLast = return ([], tLast)
-- renameFormArgs ((m, a, t):ats) tLast = do
--   a' <- newNameWith'' "var"
--   let sub = [(a, (m, WeakTermUpsilon a'))]
--   let (ats', tLast') = substWeakTermPlus'' sub ats tLast
--   (ats'', tLast'') <- renameFormArgs ats' tLast'
--   return ((m, a', t) : ats'', tLast'')
checkNameSanity :: Meta -> [IdentifierPlus] -> WithEnv ()
checkNameSanity m atsbts = do
  let asbs = map (\(_, x, _) -> x) atsbts
  when (not $ linearCheck $ map asText asbs) $
    raiseError
      m
      "the names of the rules of inductive/coinductive type must be distinct"

toInductive ::
     [IdentifierPlus] -> [IdentifierPlus] -> Connective -> WithEnv [QuasiStmt]
toInductive ats bts connective@(m, a@(I (ai, _)), xts, _) = do
  formationRule <- formationRuleOf connective >>= ruleAsIdentPlus
  let cod = (m, WeakTermPiElim (m, WeakTermUpsilon a) (map toVar' xts))
  -- z <- newNameWith'' "_"
  -- let zt = (m, z, cod)
  -- (atsbts', cod') <- renameFormArgs (ats ++ bts) cod
  mls1 <- piUnivLevelsfrom (ats ++ bts) cod
  -- mls2 <- piUnivLevelsfrom (xts ++ atsbts' ++ [zt]) cod'
  return $
    [ QuasiStmtLetInductive
        (length ats)
        m
        formationRule
        -- nat := lam (...). Pi{nat} (...)
        (m, WeakTermPiIntro xts (m, WeakTermPiPlus ai mls1 (ats ++ bts) cod))
    -- induction principle
    -- , QuasiStmtLetWT
    --     m
    --     ( m
    --     , asIdent (ai <> "." <> "induction")
    --     , (m, WeakTermPi mls2 (xts ++ atsbts' ++ [zt]) cod'))
    --     ( m
    --     , WeakTermPiIntro
    --         (xts ++ atsbts' ++ [zt])
    --         (m, WeakTermPiElim (toVar' zt) (map toVar' atsbts')))
    ]

toInductiveIntroList :: [IdentifierPlus] -> Connective -> WithEnv [QuasiStmt]
toInductiveIntroList ats (_, a, xts, rules) = do
  bts <- mapM ruleAsIdentPlus rules
  concat <$> mapM (toInductiveIntro ats bts xts a) rules

-- represent the introduction rule within CoC
toInductiveIntro ::
     [IdentifierPlus]
  -> [IdentifierPlus]
  -> [IdentifierPlus]
  -> Identifier
  -> Rule
  -> WithEnv [QuasiStmt]
toInductiveIntro ats bts xts a@(I (ai, _)) (mb, b@(I (bi, k)), m, yts, cod)
  | (_, WeakTermPiElim (_, WeakTermUpsilon a') es) <- cod
  , a == a'
  , length xts == length es = do
    mls <- piUnivLevelsfrom (xts ++ yts) cod
    let vs = varWeakTermPlus (m, WeakTermPi mls yts cod)
    let xts' = filter (\(_, x, _) -> x `elem` vs) xts
    let b' = I (ai <> ":" <> bi, k)
    let piType = (m, WeakTermPi mls (xts' ++ yts) cod)
    let xtsyts = xts' ++ yts
    let atsbts = ats ++ bts
    let bInner = (mb, WeakTermUpsilon b)
    let app = (m, WeakTermPiElim bInner (map toVar' yts))
    let lam =
          ( m
          , WeakTermPiIntroNoReduce
              xtsyts
              (m, WeakTermPiIntroPlus ai (bi, xts', yts) atsbts app))
    let attrList = map (QuasiStmtImplicit m b') [0 .. length xts' - 1]
    let as = map (\(_, x, _) -> x) ats
    return (QuasiStmtLetInductiveIntro m (mb, b', piType) lam as : attrList)
  | otherwise =
    raiseError m $
    "the succedent of an introduction rule of `" <>
    ai <>
    "` must be of the form `(" <> showItems (ai : map (const "_") xts) <> ")`"

ruleAsIdentPlus :: Rule -> WithEnv IdentifierPlus
ruleAsIdentPlus (mb, b, m, xts, t) = do
  mls <- piUnivLevelsfrom xts t
  return (mb, b, (m, WeakTermPi mls xts t))

formationRuleOf :: Connective -> WithEnv Rule
formationRuleOf (m, a, xts, _) = do
  l <- newCount
  return (m, a, m, xts, (m, WeakTermTau l))

formationRuleOf' :: Connective -> WithEnv Rule
formationRuleOf' (m, a@(I (x, _)), xts, rules) = do
  let bs = map (\(_, I (b, _), _, _, _) -> x <> ":" <> b) rules
  let bis = zip bs [0 ..]
  -- register "nat" ~> [("zero", 0), ("succ", 1)], "list" ~> [("nil", 0), ("cons", 1)], etc.
  insEnumEnv m x bis
  l <- newCount
  return (m, a, m, xts, (m, WeakTermTau l))

toInternalRuleList :: Connective -> WithEnv [IdentifierPlus]
toInternalRuleList (_, _, _, rules) = mapM ruleAsIdentPlus rules

toVar' :: IdentifierPlus -> WeakTermPlus
toVar' (m, x, _) = (m, WeakTermUpsilon x)

insForm :: Int -> IdentifierPlus -> WeakTermPlus -> WithEnv ()
insForm 1 (_, I (_, i), _) e =
  modify
    (\env -> env {formationEnv = IntMap.insert i (Just e) (formationEnv env)})
insForm _ (_, I (_, i), _) _ =
  modify
    (\env -> env {formationEnv = IntMap.insert i Nothing (formationEnv env)})

insInductive :: [Identifier] -> IdentifierPlus -> WithEnv ()
insInductive [I (_, i)] bt = do
  ienv <- gets inductiveEnv
  modify
    (\env -> env {inductiveEnv = Map.insertWith optConcat i (Just [bt]) ienv})
insInductive as _ = do
  forM_ as $ \(I (_, i)) -> do
    modify
      (\env -> env {inductiveEnv = Map.insert i Nothing (inductiveEnv env)})

optConcat :: Maybe [a] -> Maybe [a] -> Maybe [a]
optConcat mNew mOld = do
  mNew' <- mNew
  mOld' <- mOld
  -- insert mNew at the end of the list (to respect the structure of ind/coind represented as pi/sigma)
  return $ mOld' ++ mNew'

data Mode
  = ModeForward
  | ModeBackward
  deriving (Show)

internalize ::
     SubstWeakTerm -> [IdentifierPlus] -> IdentifierPlus -> WithEnv WeakTermPlus
internalize isub atsbts (m, y, t) =
  zeta ModeForward isub atsbts t (m, WeakTermUpsilon y)

flipMode :: Mode -> Mode
flipMode ModeForward = ModeBackward
flipMode ModeBackward = ModeForward

isResolved :: SubstWeakTerm -> WeakTermPlus -> Bool
isResolved sub e = do
  let xs = map fst sub
  let ys = varWeakTermPlus e
  all (\x -> x `notElem` ys) xs

zeta ::
     Mode -- 現在の変換がinvertedかそうでないかをtrackするための変数
  -> SubstWeakTerm -- out ~> in (substitution {x1 := x1', ..., xn := xn'})
  -> [IdentifierPlus] -- ats ++ bts
  -> WeakTermPlus -- a type `A`
  -> WeakTermPlus -- a term `e` of type `A`
  -> WithEnv WeakTermPlus -- a term of type `A{x1 := x1', ..., xn := xn'}`
zeta mode isub atsbts t e = do
  ienv <- gets inductiveEnv
  isub' <- invSubst isub
  case t of
    (_, WeakTermPi _ xts cod) -> zetaPi mode isub atsbts xts cod e
    -- (_, WeakTermSigma xts) -> zetaSigma mode isub atsbts xts e
    (_, WeakTermPiElim va@(_, WeakTermUpsilon a@(I (_, i))) es) -- esの長さをチェックするべきでは？
      | Just _ <- lookup a (isub ++ isub') ->
        zetaInductive mode isub atsbts es e
      | Just (Just bts) <- Map.lookup i ienv
      , not (all (isResolved isub) es) ->
        zetaInductiveNested mode isub atsbts e va a es bts
      | Just Nothing <- Map.lookup i ienv ->
        zetaInductiveNestedMutual (metaOf t) a
    _ -> do
      if isResolved isub t -- flipが絡むのでは？
        then return e
        else raiseError (metaOf t) $
             "malformed inductive/coinductive type definition: " <> toText t

zetaPi ::
     Mode
  -> SubstWeakTerm
  -> [IdentifierPlus]
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WeakTermPlus
  -> WithEnv WeakTermPlus
zetaPi mode isub atsbts xts cod e = do
  (xts', cod') <- renameBinder xts cod
  let (ms', xs', ts') = unzip3 xts'
  let vs' = zipWith (\m x -> (m, WeakTermUpsilon x)) ms' xs'
  -- backward conversion to create (A', ..., A') -> (A, ..., A)
  isub' <- invSubst isub
  vs <- zipWithM (zeta (flipMode mode) isub' atsbts) ts' vs' -- これだとtsの中のxの出現が狂う、というわけ？
  -- forward conversion to create B -> B'
  app' <- zeta mode isub atsbts cod' (fst e, WeakTermPiElim e vs)
  -- return the composition: (A' ..., A') -> (A, ..., A) -> B -> B'
  let ts'' = map (substWeakTermPlus isub) ts'
  return (fst e, WeakTermPiIntro (zip3 ms' xs' ts'') app')

-- zetaSigma ::
--      Mode
--   -> SubstWeakTerm
--   -> [IdentifierPlus]
--   -> [IdentifierPlus]
--   -> WeakTermPlus
--   -> WithEnv WeakTermPlus
-- zetaSigma mode isub atsbts xts e = do
--   let (ms, xs, ts) = unzip3 xts
--   xs' <- mapM newNameWith xs
--   let vs = zipWith (\m x -> (m, WeakTermUpsilon x)) ms xs'
--   vs' <- zipWithM (zeta mode isub atsbts) ts vs
--   let ts' = map (substWeakTermPlus isub) ts
--   let sigType = (fst e, WeakTermSigma (zip3 ms xs ts'))
--   return
--     ( fst e
--     , WeakTermSigmaElim
--         sigType
--         (zip3 ms xs' ts)
--         e
--         (fst e, WeakTermSigmaIntro sigType vs'))
zetaInductive ::
     Mode
  -> SubstWeakTerm
  -> [IdentifierPlus]
  -> [WeakTermPlus]
  -> WeakTermPlus
  -> WithEnv WeakTermPlus
zetaInductive mode isub atsbts es e
  | ModeBackward <- mode =
    raiseError
      (metaOf e)
      "found a contravariant occurence of <name> in the antecedent of an introduction rule"
  | all (isResolved isub) es = do
    return (fst e, WeakTermPiElim e (map toVar' atsbts))
  | otherwise = raiseError (metaOf e) "found a self-nested inductive type"

zetaInductiveNested ::
     Mode
  -> SubstWeakTerm -- inductiveのためのaのsubst (outer -> inner)
  -> [IdentifierPlus] -- innerのためのatsbts
  -> WeakTermPlus -- 変換されるべきterm
  -> WeakTermPlus -- list Aにおけるlist
  -> Identifier -- list (トップレベルで定義されている名前、つまりouterの名前)
  -> [WeakTermPlus] -- list AにおけるA
  -> [IdentifierPlus] -- トップレベルで定義されているコンストラクタたち
  -> WithEnv WeakTermPlus
zetaInductiveNested mode isub atsbts e va aOuter es bts = do
  (xts, (_, aInner, _), btsInner) <- lookupInductive (metaOf va) aOuter
  let es' = map (substWeakTermPlus isub) es
  args <-
    zipWithM
      (toInternalizedArg mode isub aInner aOuter xts atsbts es es')
      bts
      btsInner
  let m = fst e
  return
    ( m
    , WeakTermPiElim
        e
        ((m, WeakTermPiIntro xts (m, WeakTermPiElim va es')) : args))

zetaInductiveNestedMutual :: Meta -> Identifier -> WithEnv WeakTermPlus
zetaInductiveNestedMutual m (I (a, _)) =
  raiseError m $
  "mutual inductive type `" <>
  a <> "` cannot be used to construct a nested inductive type"

lookupInductive ::
     Meta
  -> Identifier
  -> WithEnv ([IdentifierPlus], IdentifierPlus, [IdentifierPlus])
lookupInductive m (I (ai, i)) = do
  fenv <- gets formationEnv
  case IntMap.lookup i fenv of
    Just (Just (_, WeakTermPiIntro xts (_, WeakTermPiPlus _ _ atsbts (_, WeakTermPiElim (_, WeakTermUpsilon _) _)))) -> do
      let at = head atsbts
      let bts = tail atsbts -- valid since a is not mutual
      return (xts, at, bts)
    Just (Just e) ->
      raiseCritical m $
      "malformed inductive type (Parse.lookupInductive): \n" <> toText e
    Just Nothing ->
      raiseError m $
      "the inductive type `" <> ai <> "` must be a non-mutual inductive type"
    Nothing -> raiseCritical m $ "no such inductive type defined: " <> ai

toInternalizedArg ::
     Mode
  -> SubstWeakTerm -- inductiveのためのaのsubst (outer -> inner)
  -> Identifier -- innerでのaの名前。listの定義の中に出てくるほうのlist.
  -> Identifier -- outerでのaの名前。listとか。
  -> [IdentifierPlus] -- aの引数。
  -> [IdentifierPlus] -- base caseでのinternalizeのための情報。
  -> [WeakTermPlus] -- list @ (e1, ..., en)の引数部分。
  -> [WeakTermPlus] -- eiをisubでsubstしたもの。
  -> IdentifierPlus -- outerでのコンストラクタ。
  -> IdentifierPlus -- innerでのコンストラクタ。xts部分の引数だけouterのコンストラクタと型がずれていることに注意。
  -> WithEnv WeakTermPlus
toInternalizedArg mode isub aInner aOuter xts atsbts es es' b (mbInner, _, (_, WeakTermPi _ ytsInner _)) = do
  let (ms, ys, ts) = unzip3 ytsInner
  let vxs = map toVar' xts
  -- 引数の型を適切にsubstする。これによって、aInner (x1, ..., xn)の出現がaOuter (e1', ..., en')へと置き換えられて、
  -- 結果的にaOuterの中身はすべて処理済みとなる。
  -- ytsInnerはPiの内部でのコンストラクタの型であるから、substをするときはaInnerからsubstを行なう必要がある。……本当か？
  -- このsubstを行なうことで結局z @ (aOuter, ARGS)のARGS部分の引数がaOuter関連のもので揃うから正しいはず。
  ts' <- mapM (substRuleType ((aInner, vxs), (aOuter, es'))) ts
  -- aInner (x1, ..., xn) ~> aOuter (e1', ..., en')が終わったら、こんどは型のxiをeiに置き換える。
  -- これによって、
  --   - aOuterの中身はすべて処理済み
  --   - aOuterの外にはeiが出現しうる
  -- という状況が実現できる。これはrecursionの停止を与える。
  let xs = map (\(_, x, _) -> x) xts -- fixme: このへんもrenameBinderでやったほうがいい？
  let ts'' = map (substWeakTermPlus (zip xs es)) ts'
  ys' <- mapM newNameWith ys
  -- これで引数の型の調整が終わったので、あらためてidentPlusの形に整える
  -- もしかしたらyって名前を別名に変更したほうがいいかもしれないが。
  let ytsInner' = zip3 ms ys' ts''
  -- 引数をコンストラクタに渡せるようにするために再帰的にinternalizeをおこなう。
  -- list (item-outer A)みたいな形だったものは、list (item-inner A)となっているはずなので、zetaは停止する。
  -- list (list (item-outer A))みたいな形だったものも、list (list (item-inner A))となってzetaは停止する。
  let f (m, y, t) = zeta mode isub atsbts t (m, WeakTermUpsilon y)
  args <- mapM f ytsInner'
  -- あとは結果を返すだけ
  return
    ( mbInner
    , WeakTermPiIntro
        ytsInner'
        (mbInner, WeakTermPiElim (toVar' b) (es' ++ args)))
toInternalizedArg _ _ _ _ _ _ _ _ _ (m, _, _) =
  raiseCritical
    m
    "the type of an introduction rule must be represented by a Pi-type, but its not"

renameBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
renameBinder [] e = return ([], e)
renameBinder ((m, x, t):ats) e = do
  x' <- newNameWith x
  let sub = [(x, (m, WeakTermUpsilon x'))]
  let (ats', e') = substWeakTermPlus'' sub ats e -- discern済みなのでこれでオーケーのはず
  (ats'', e'') <- renameBinder ats' e'
  return ((m, x', t) : ats'', e'')

type RuleType = (Identifier, [WeakTermPlus])

-- subst a @ (e1, ..., en) ~> a' @ (e1', ..., en')
substRuleType :: (RuleType, RuleType) -> WeakTermPlus -> WithEnv WeakTermPlus
substRuleType _ (m, WeakTermTau l) = return (m, WeakTermTau l)
substRuleType _ (m, WeakTermUpsilon x) = return (m, WeakTermUpsilon x)
substRuleType sub (m, WeakTermPi mls xts t) = do
  (xts', t') <- substRuleType'' sub xts t
  return (m, WeakTermPi mls xts' t')
substRuleType sub (m, WeakTermPiPlus name mls xts t) = do
  (xts', t') <- substRuleType'' sub xts t
  return (m, WeakTermPiPlus name mls xts' t')
substRuleType sub (m, WeakTermPiIntro xts body) = do
  (xts', body') <- substRuleType'' sub xts body
  return (m, WeakTermPiIntro xts' body')
substRuleType sub (m, WeakTermPiIntroNoReduce xts body) = do
  (xts', body') <- substRuleType'' sub xts body
  return (m, WeakTermPiIntroNoReduce xts' body')
substRuleType sub (m, WeakTermPiIntroPlus ind (name, args1, args2) xts body) = do
  args' <- substRuleType' sub $ args1 ++ args2
  let args1' = take (length args1) args'
  let args2' = drop (length args1) args'
  (xts', body') <- substRuleType'' sub xts body
  return (m, WeakTermPiIntroPlus ind (name, args1', args2') xts' body')
substRuleType sub@((a1, es1), (a2, es2)) (m, WeakTermPiElim e es)
  | (mx, WeakTermUpsilon x) <- e
  , a1 == x =
    case (mapM asUpsilon es1, mapM asUpsilon es) of
      (Just xs', Just ys')
        | xs' == ys' -> return (m, WeakTermPiElim (mx, WeakTermUpsilon a2) es2)
      _ ->
        raiseError
          m
          "generalized inductive type cannot be used to construct a nested inductive type"
  | otherwise = do
    e' <- substRuleType sub e
    es' <- mapM (substRuleType sub) es
    return (m, WeakTermPiElim e' es')
-- substRuleType sub (m, WeakTermSigma xts) = do
--   xts' <- substRuleType' sub xts
--   return (m, WeakTermSigma xts')
-- substRuleType sub (m, WeakTermSigmaIntro t es) = do
--   t' <- substRuleType sub t
--   es' <- mapM (substRuleType sub) es
--   return (m, WeakTermSigmaIntro t' es')
-- substRuleType sub (m, WeakTermSigmaElim t xts e1 e2) = do
--   t' <- substRuleType sub t
--   e1' <- substRuleType sub e1
--   (xts', e2') <- substRuleType'' sub xts e2
--   return (m, WeakTermSigmaElim t' xts' e1' e2')
substRuleType sub (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- substRuleType sub t
  if fst (fst sub) == x
    then return (m, WeakTermIter (mx, x, t') xts e)
    else do
      (xts', e') <- substRuleType'' sub xts e
      return (m, WeakTermIter (mx, x, t') xts' e')
substRuleType _ (m, WeakTermConst x up) = return (m, WeakTermConst x up)
substRuleType _ (m, WeakTermZeta x) = return (m, WeakTermZeta x)
substRuleType sub (m, WeakTermInt t x) = do
  t' <- substRuleType sub t
  return (m, WeakTermInt t' x)
substRuleType _ (m, WeakTermFloat16 x) = do
  return (m, WeakTermFloat16 x)
substRuleType _ (m, WeakTermFloat32 x) = do
  return (m, WeakTermFloat32 x)
substRuleType _ (m, WeakTermFloat64 x) = do
  return (m, WeakTermFloat64 x)
substRuleType sub (m, WeakTermFloat t x) = do
  t' <- substRuleType sub t
  return (m, WeakTermFloat t' x)
substRuleType _ (m, WeakTermEnum x) = return (m, WeakTermEnum x)
substRuleType _ (m, WeakTermEnumIntro l) = return (m, WeakTermEnumIntro l)
substRuleType sub (m, WeakTermEnumElim (e, t) branchList) = do
  t' <- substRuleType sub t
  e' <- substRuleType sub e
  let (caseList, es) = unzip branchList
  es' <- mapM (substRuleType sub) es
  return (m, WeakTermEnumElim (e', t') (zip caseList es'))
substRuleType sub (m, WeakTermArray dom k) = do
  dom' <- substRuleType sub dom
  return (m, WeakTermArray dom' k)
substRuleType sub (m, WeakTermArrayIntro k es) = do
  es' <- mapM (substRuleType sub) es
  return (m, WeakTermArrayIntro k es')
substRuleType sub (m, WeakTermArrayElim mk xts v e) = do
  v' <- substRuleType sub v
  (xts', e') <- substRuleType'' sub xts e
  return (m, WeakTermArrayElim mk xts' v' e')
substRuleType _ (m, WeakTermStruct ts) = return (m, WeakTermStruct ts)
substRuleType sub (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  es' <- mapM (substRuleType sub) es
  return (m, WeakTermStructIntro $ zip es' ts)
substRuleType sub (m, WeakTermStructElim xts v e) = do
  v' <- substRuleType sub v
  let xs = map (\(_, x, _) -> x) xts
  if fst (fst sub) `elem` xs
    then return (m, WeakTermStructElim xts v' e)
    else do
      e' <- substRuleType sub e
      return (m, WeakTermStructElim xts v' e')
substRuleType sub (m, WeakTermCase (e, t) cxtes) = do
  e' <- substRuleType sub e
  t' <- substRuleType sub t
  cxtes' <-
    flip mapM cxtes $ \((c, xts), body) -> do
      (xts', body') <- substRuleType'' sub xts body
      return ((c, xts'), body')
  return (m, WeakTermCase (e', t') cxtes')

substRuleType' ::
     (RuleType, RuleType) -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
substRuleType' _ [] = return []
substRuleType' sub ((m, x, t):xts) = do
  t' <- substRuleType sub t
  if fst (fst sub) == x
    then return $ (m, x, t') : xts
    else do
      xts' <- substRuleType' sub xts
      return $ (m, x, t') : xts'

substRuleType'' ::
     (RuleType, RuleType)
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
substRuleType'' sub [] e = do
  e' <- substRuleType sub e
  return ([], e')
substRuleType'' sub ((m, x, t):xts) e = do
  t' <- substRuleType sub t
  if fst (fst sub) == x
    then return ((m, x, t') : xts, e)
    else do
      (xts', e') <- substRuleType'' sub xts e
      return ((m, x, t') : xts', e')

invSubst :: SubstWeakTerm -> WithEnv SubstWeakTerm
invSubst [] = return []
invSubst ((x, (m, WeakTermUpsilon x')):sub) = do
  sub' <- invSubst sub
  return $ (x', (m, WeakTermUpsilon x)) : sub'
invSubst _ =
  raiseCritical'
    "substitution used in internalization/externalization must be of the form {VAR ~> VAR, ..., VAR ~> VAR}"
