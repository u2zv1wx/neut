module Parse.Rule
  ( parseInductive,
    insForm,
    insInductive,
    internalize,
    registerLabelInfo,
    generateProjections,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Either (rights)
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm
import Parse.Interpret

parseInductive :: Meta -> [TreePlus] -> WithEnv [QuasiStmt]
parseInductive m ts = do
  ts' <- mapM setupIndPrefix ts
  parseConnective m ts' toInductive toInductiveIntroList

setupIndPrefix :: TreePlus -> WithEnv TreePlus
setupIndPrefix (m, TreeNode ((ma, TreeLeaf a) : xts : rules)) = do
  rules' <- mapM (setupIndPrefix' a) rules
  return (m, TreeNode ((ma, TreeLeaf a) : xts : rules'))
setupIndPrefix t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) TREE)"

setupIndPrefix' :: T.Text -> TreePlus -> WithEnv TreePlus
setupIndPrefix' a (m, TreeNode ((mb, TreeLeaf b) : rest)) =
  return (m, TreeNode ((mb, TreeLeaf (a <> ":" <> b)) : rest))
setupIndPrefix' _ t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) TREE)"

-- variable naming convention on parsing connectives:
--   a : the name of a formation rule, like `nat`, `list`, `stream`, etc.
--   b : the name of an introduction/elimination rule, like `zero`, `cons`, `head`, etc.
--   x : the name of an argument of a formation rule, like `A` in `list A` or `stream A`.
--   y : the name of an argument of an introduction/elimination rule, like `w` or `ws` in `cons : Pi (w : A, ws : list A). list A`.
parseConnective ::
  Meta ->
  [TreePlus] ->
  ([WeakTextPlus] -> [WeakTextPlus] -> Connective -> WithEnv [QuasiStmt]) ->
  ([WeakTextPlus] -> Connective -> WithEnv [QuasiStmt]) ->
  WithEnv [QuasiStmt]
parseConnective m ts f g = do
  connectiveList <- mapM parseConnective' ts
  fs <- mapM formationRuleOf' connectiveList
  -- fs <- mapM formationRuleOf connectiveList
  ats <- mapM ruleAsWeakTextPlus fs
  bts <- concat <$> mapM toInternalRuleList connectiveList
  checkNameSanity m $ ats ++ bts
  connectiveList' <- concat <$> mapM (f ats bts) connectiveList
  ruleList <- concat <$> mapM (g ats) connectiveList
  return $ connectiveList' ++ ruleList

parseConnective' :: TreePlus -> WithEnv Connective
parseConnective' (m, TreeNode ((_, TreeLeaf name) : (_, TreeNode xts) : rules)) = do
  xts' <- mapM interpretWeakIdentPlus xts
  rules' <- mapM parseRule rules
  return (m, name, xts', rules')
parseConnective' t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) ...)"

registerLabelInfo :: [TreePlus] -> WithEnv ()
registerLabelInfo ts = do
  connectiveList <- mapM parseConnective' ts
  fs <- mapM formationRuleOf connectiveList
  ats <- mapM ruleAsWeakTextPlus fs
  bts <- concat <$> mapM toInternalRuleList connectiveList
  forM_ ats $ \(_, a, _) -> do
    let asbs = map (\(_, x, _) -> x) $ ats ++ bts
    modify (\env -> env {labelEnv = Map.insert a asbs (labelEnv env)})

generateProjections :: [TreePlus] -> WithEnv [QuasiStmt]
generateProjections ts = do
  connectiveList <- mapM parseConnective' ts
  fs <- mapM formationRuleOf connectiveList
  ats <- mapM ruleAsWeakTextPlus fs
  bts <- concat <$> mapM toInternalRuleList connectiveList
  let bts' = map textPlusToWeakIdentPlus bts
  stmtListList <-
    forM ats $ \(ma, a, ta) ->
      forM bts $ \(mb, b, tb) -> do
        xts <- takeXTS ta
        (dom@(my, y, ty), cod) <- separate tb
        v <- newNameWith'' "base"
        let b' = a <> ":" <> b
        return
          [ QuasiStmtLetWT
              mb
              (mb, asIdent b', (mb, WeakTermPi Nothing (xts ++ [dom]) cod))
              ( mb,
                weakTermPiIntro
                  (xts ++ [dom])
                  ( mb,
                    WeakTermCase
                      a
                      (my, WeakTermUpsilon y)
                      [ ( ( (mb, a <> ":" <> "unfold"),
                            -- `xts ++` is required since LetWT bypasses `infer`
                            xts
                              ++ [(ma, asIdent a, ta)]
                              ++ bts'
                              ++ [(mb, v, ty)]
                          ),
                          ( mb,
                            WeakTermPiElim
                              (mb, WeakTermUpsilon $ asIdent b)
                              [(mb, WeakTermUpsilon v)]
                          )
                        )
                      ]
                  )
              )
          ]
  return $ concat $ concat stmtListList

separate :: WeakTermPlus -> WithEnv (WeakIdentPlus, WeakTermPlus)
separate (_, WeakTermPi _ [xt] cod) = return (xt, cod)
separate t = raiseSyntaxError (fst t) "(pi (TREE) TREE)"

takeXTS :: WeakTermPlus -> WithEnv [WeakIdentPlus]
takeXTS (_, WeakTermPi _ xts _) = return xts
takeXTS t = raiseSyntaxError (fst t) "(pi (TREE ... TREE) TREE)"

parseRule :: TreePlus -> WithEnv Rule
parseRule (m, TreeNode [(mName, TreeLeaf name), (_, TreeNode xts), t]) = do
  t' <- interpret t
  xts' <- mapM interpretWeakIdentPlus xts
  return (m, name, mName, xts', t')
parseRule t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) TREE)"

checkNameSanity :: Meta -> [WeakTextPlus] -> WithEnv ()
checkNameSanity m atsbts = do
  let asbs = map (\(_, x, _) -> x) atsbts
  when (not $ linearCheck asbs) $
    raiseError
      m
      "the names of the rules of inductive/coinductive type must be distinct"

toInductive ::
  [WeakTextPlus] -> [WeakTextPlus] -> Connective -> WithEnv [QuasiStmt]
toInductive ats bts connective@(m, ai, xts, _) = do
  let a = asIdent ai
  formationRule <- formationRuleOf connective >>= ruleAsWeakIdentPlus
  let cod = (m, WeakTermPiElim (m, WeakTermUpsilon a) (map toVar' xts))
  z <- newNameWith'' "_"
  let zt = (m, z, cod)
  let atsbts = map textPlusToWeakIdentPlus $ ats ++ bts
  return
    [ QuasiStmtLetInductive
        (length ats)
        m
        formationRule
        -- nat := lam (...). Pi{nat} (...)
        (m, weakTermPiIntro xts (m, WeakTermPi (Just ai) atsbts cod)),
      -- induction principle
      QuasiStmtLetWT
        m
        ( m,
          asIdent $ ai <> ":" <> "induction",
          (m, WeakTermPi Nothing (xts ++ [zt] ++ atsbts) cod)
        )
        ( m,
          weakTermPiIntro
            (xts ++ [zt] ++ atsbts)
            (m, WeakTermPiElim (toVar' zt) (map toVar' atsbts))
        )
    ]

toInductiveIntroList :: [WeakTextPlus] -> Connective -> WithEnv [QuasiStmt]
toInductiveIntroList ats (_, a, xts, rules) = do
  let ats' = map textPlusToWeakIdentPlus ats
  bts <- mapM ruleAsWeakIdentPlus rules -- fixme: このbtsはmutualな別の部分からもとってくる必要があるはず
  concat <$> mapM (toInductiveIntro ats' bts xts a) rules

-- represent the introduction rule within CoC
toInductiveIntro ::
  [WeakIdentPlus] ->
  [WeakIdentPlus] ->
  [WeakIdentPlus] ->
  T.Text ->
  Rule ->
  WithEnv [QuasiStmt]
toInductiveIntro ats bts xts ai (mb, bi, m, yts, cod)
  | (_, WeakTermPiElim (_, WeakTermUpsilon a') es) <- cod,
    ai == asText a',
    length xts == length es = do
    let vs = varWeakTermPlus (m, weakTermPi yts cod)
    let ixts = filter (\(_, (_, x, _)) -> x `S.member` vs) $ zip [0 ..] xts
    let (is, xts') = unzip ixts
    modify (\env -> env {revIndEnv = Map.insert bi (ai, is) (revIndEnv env)})
    return
      [ QuasiStmtLetInductiveIntro
          m
          (mb, asIdent bi, (m, weakTermPi (xts' ++ yts) cod))
          ( m {metaIsReducible = False},
            weakTermPiIntro
              (xts' ++ yts)
              ( m,
                WeakTermPiIntro
                  (Just (bi, xts' ++ yts))
                  (ats ++ bts)
                  ( m,
                    WeakTermPiElim
                      (mb, WeakTermUpsilon (asIdent bi))
                      (map toVar' yts)
                  )
              )
          )
          (map (\(_, x, _) -> asText x) ats)
      ]
  | otherwise =
    raiseError m $
      "the succedent of an introduction rule of `"
        <> ai
        <> "` must be of the form `("
        <> showItems (ai : map (const "_") xts)
        <> ")`"

ruleAsWeakIdentPlus :: Rule -> WithEnv WeakIdentPlus
ruleAsWeakIdentPlus (mb, b, m, xts, t) =
  return (mb, asIdent b, (m, weakTermPi xts t))

ruleAsWeakTextPlus :: Rule -> WithEnv WeakTextPlus
ruleAsWeakTextPlus (mb, b, m, xts, t) =
  return (mb, b, (m, weakTermPi xts t))

textPlusToWeakIdentPlus :: WeakTextPlus -> WeakIdentPlus
textPlusToWeakIdentPlus (mx, x, t) = (mx, asIdent x, t)

formationRuleOf :: Connective -> WithEnv Rule
formationRuleOf (m, a, xts, _) = return (m, a, m, xts, (m, WeakTermTau))

formationRuleOf' :: Connective -> WithEnv Rule
formationRuleOf' (m, x, xts, rules) = do
  let bs = map (\(_, b, _, _, _) -> b) rules
  let bis = zip bs [0 ..]
  -- register "nat" ~> [("zero", 0), ("succ", 1)], "list" ~> [("nil", 0), ("cons", 1)], etc.
  insEnumEnv m x bis
  return (m, x, m, xts, (m, WeakTermTau))

toInternalRuleList :: Connective -> WithEnv [WeakTextPlus]
toInternalRuleList (_, _, _, rules) = mapM ruleAsWeakTextPlus rules

toVar' :: WeakIdentPlus -> WeakTermPlus
toVar' (m, x, _) = (m, WeakTermUpsilon x)

-- toConst :: WeakTextPlus -> WeakTermPlus
-- toConst (m, x, _) = (m, WeakTermConst x)

insForm :: Int -> WeakIdentPlus -> WeakTermPlus -> WithEnv ()
insForm 1 (_, I (x, _), _) e =
  modify (\env -> env {formationEnv = Map.insert x (Just e) (formationEnv env)})
insForm _ (_, I (x, _), _) _ =
  modify (\env -> env {formationEnv = Map.insert x Nothing (formationEnv env)})

insInductive :: [T.Text] -> WeakIdentPlus -> WithEnv ()
insInductive [ai] bt = do
  ienv <- gets indEnv
  modify (\env -> env {indEnv = Map.insertWith optConcat ai (Just [bt]) ienv})
insInductive as _ =
  forM_ as $ \ai ->
    modify (\env -> env {indEnv = Map.insert ai Nothing (indEnv env)})

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
  [T.Text] -> [WeakIdentPlus] -> WeakIdentPlus -> WithEnv WeakTermPlus
internalize as atsbts (m, y, t) = do
  let sub = Map.fromList $ zip (map Right as) (map toVar' atsbts)
  theta ModeForward sub atsbts t (m, WeakTermUpsilon y)

flipMode :: Mode -> Mode
flipMode ModeForward = ModeBackward
flipMode ModeBackward = ModeForward

isResolved :: SubstWeakTerm -> WeakTermPlus -> Bool
isResolved sub e = do
  let xs = rights $ Map.keys sub
  all (`S.notMember` constWeakTermPlus e) xs

-- type SubstWeakTerm = Map.HashMap T.Text WeakTermPlus
-- e : Aを受け取って、flipしていないときはIN(A) = BをみたすB型のtermを、
-- また、flipしてるときはOUT(A) = BをみたすB型のtermを、
-- それぞれ構成して返す。IN/OUTはSubstWeakTermによって定まるものとする。
theta ::
  Mode -> -- 現在の変換がflipしているかそうでないかの情報
  SubstWeakTerm -> -- out ~> in (substitution sub := {x1 := x1', ..., xn := xn'})
  [WeakIdentPlus] -> -- 現在定義しようとしているinductive typeのatsbts. base caseのinternalizeのために必要。
  WeakTermPlus -> -- a type `A`
  WeakTermPlus -> -- a term `e` of type `A`
  WithEnv WeakTermPlus
theta mode isub atsbts t e = do
  ienv <- gets indEnv
  case t of
    (_, WeakTermPi _ xts cod) -> thetaPi mode isub atsbts xts cod e
    (_, WeakTermPiElim va@(_, WeakTermConst ai) es)
      | Just _ <- Map.lookup (Right ai) isub ->
        thetaInductive mode isub ai atsbts es e
      -- nested inductive
      | Just (Just bts) <- Map.lookup ai ienv,
        not (all (isResolved isub) es) ->
        thetaInductiveNested mode isub atsbts e va ai es bts
      -- nestedの外側がmutualであるとき。このときはエラーとする。
      | Just Nothing <- Map.lookup ai ienv ->
        thetaInductiveNestedMutual (metaOf t) ai
    _ ->
      if isResolved isub t
        then return e
        else
          raiseError (metaOf t) $
            "malformed inductive/coinductive type definition: " <> toText t

thetaPi ::
  Mode ->
  SubstWeakTerm ->
  [WeakIdentPlus] ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WeakTermPlus ->
  WithEnv WeakTermPlus
thetaPi mode isub atsbts xts cod e = do
  (xts', cod') <- renameBinder xts cod
  let (ms', xs', ts') = unzip3 xts'
  -- eta展開のための変数を用意
  let xs'' = zipWith (\m x -> (m, WeakTermUpsilon x)) ms' xs'
  -- xsを「逆方向」で変換（実際には逆向きの変換は不可能なので、2回flipされることを期待して変換）
  -- こうしたあとでx : In(A)と束縛してからthetaでの変換結果を使えば、x' : Out(A)が得られるので
  -- 引数として与えられるようになる、というわけ。
  xsBackward <- zipWithM (theta (flipMode mode) isub atsbts) ts' xs''
  -- appのほうを「順方向」で変換
  appForward <- theta mode isub atsbts cod' (fst e, WeakTermPiElim e xsBackward)
  -- 結果をまとめる
  let ts'' = map (substWeakTermPlus isub) ts' -- 引数をinternalizeされたバージョンの型にする
  return (fst e, weakTermPiIntro (zip3 ms' xs' ts'') appForward)

thetaInductive ::
  Mode ->
  SubstWeakTerm ->
  T.Text ->
  [WeakIdentPlus] ->
  [WeakTermPlus] ->
  WeakTermPlus ->
  WithEnv WeakTermPlus
thetaInductive mode isub a atsbts es e
  | ModeBackward <- mode =
    raiseError (metaOf e) $
      "found a contravariant occurence of `"
        <> a
        <> "` in the antecedent of an introduction rule"
  -- `list @ i64` のように、中身が処理済みであることをチェック (この場合はes == [i64])
  | all (isResolved isub) es =
    return (fst e, WeakTermPiElim e (map toVar' atsbts))
  | otherwise = raiseError (metaOf e) "found a self-nested inductive type"

thetaInductiveNested ::
  Mode ->
  SubstWeakTerm -> -- inductiveのためのaのsubst (outer -> inner)
  [WeakIdentPlus] -> -- innerのためのatsbts
  WeakTermPlus -> -- 変換されるべきterm
  WeakTermPlus -> -- list Aにおけるlist
  T.Text -> -- list (トップレベルで定義されている名前、つまりouterの名前)
  [WeakTermPlus] -> -- list AにおけるA
  [WeakIdentPlus] -> -- トップレベルで定義されているコンストラクタたち
  WithEnv WeakTermPlus
thetaInductiveNested mode isub atsbts e va aOuter es bts = do
  (xts, (_, aInner, _), btsInner) <- lookupInductive (metaOf va) aOuter
  let es' = map (substWeakTermPlus isub) es
  args <-
    zipWithM
      (toInternalizedArg mode isub aInner aOuter xts atsbts es es')
      bts
      btsInner
  let m = fst e
  return
    ( m,
      WeakTermPiElim
        e
        ((m, weakTermPiIntro xts (m, WeakTermPiElim va es')) : args)
    )

thetaInductiveNestedMutual :: Meta -> T.Text -> WithEnv WeakTermPlus
thetaInductiveNestedMutual m ai =
  raiseError m $
    "mutual inductive type `"
      <> ai
      <> "` cannot be used to construct a nested inductive type"

lookupInductive ::
  Meta ->
  T.Text ->
  WithEnv ([WeakIdentPlus], WeakIdentPlus, [WeakIdentPlus])
lookupInductive m ai = do
  fenv <- gets formationEnv
  case Map.lookup ai fenv of
    Just (Just (_, WeakTermPiIntro Nothing xts (_, WeakTermPi (Just _) atsbts (_, WeakTermPiElim (_, WeakTermUpsilon _) _)))) -> do
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

-- nested inductiveにおける引数をinternalizeする。
-- （これ、recursiveに処理できないの？）
toInternalizedArg ::
  Mode ->
  SubstWeakTerm -> -- inductiveのためのaのsubst (outer -> inner)
  Ident -> -- innerでのaの名前。listの定義の中に出てくるほうのlist.
  T.Text -> -- outerでのaの名前。listとか。
  [WeakIdentPlus] -> -- aの引数。
  [WeakIdentPlus] -> -- base caseでのinternalizeのための情報。
  [WeakTermPlus] -> -- list @ (e1, ..., en)の引数部分。
  [WeakTermPlus] -> -- eiをisubでsubstしたもの。
  WeakIdentPlus -> -- outerでのコンストラクタ。
  WeakIdentPlus -> -- innerでのコンストラクタ。xts部分の引数だけouterのコンストラクタと型がずれていることに注意。
  WithEnv WeakTermPlus
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
  let xs = map (\(_, x, _) -> Left $ asInt x) xts -- fixme: このへんもrenameBinderでやったほうがいい？
  let sub = Map.fromList $ zip xs es
  let ts'' = map (substWeakTermPlus sub) ts'
  ys' <- mapM newNameWith ys
  -- これで引数の型の調整が終わったので、あらためてidentPlusの形に整える
  -- もしかしたらyって名前を別名に変更したほうがいいかもしれないが。
  let ytsInner' = zip3 ms ys' ts''
  -- 引数をコンストラクタに渡せるようにするために再帰的にinternalizeをおこなう。
  -- list (item-outer A)みたいな形だったものは、list (item-inner A)となっているはずなので、thetaは停止する。
  -- list (list (item-outer A))みたいな形だったものも、list (list (item-inner A))となってthetaは停止する。
  let f (m, y, t) = theta mode isub atsbts t (m, WeakTermUpsilon y)
  args <- mapM f ytsInner'
  -- あとは結果を返すだけ
  return
    ( mbInner,
      weakTermPiIntro
        ytsInner'
        (mbInner, WeakTermPiElim (toVar' b) (es' ++ args))
    )
-- (mbInner, WeakTermPiElim (toVar' b) (es' ++ args)))
toInternalizedArg _ _ _ _ _ _ _ _ _ (m, _, _) =
  raiseCritical
    m
    "the type of an introduction rule must be represented by a Pi-type, but its not"

renameBinder ::
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv ([WeakIdentPlus], WeakTermPlus)
renameBinder [] e = return ([], e)
renameBinder ((m, x, t) : ats) e = do
  x' <- newNameWith x
  let sub = Map.singleton (Left $ asInt x) (m, WeakTermUpsilon x')
  let (ats', e') = substWeakTermPlus'' sub ats e -- discern済みなのでこれでオーケーのはず
  (ats'', e'') <- renameBinder ats' e'
  return ((m, x', t) : ats'', e'')

type RuleTypeDom = (Ident, [WeakTermPlus])

type RuleTypeCod = (T.Text, [WeakTermPlus])

type SubstRule = (RuleTypeDom, RuleTypeCod)

-- subst a @ (e1, ..., en) ~> a' @ (e1', ..., en')
substRuleType :: SubstRule -> WeakTermPlus -> WithEnv WeakTermPlus
substRuleType _ (m, WeakTermTau) = return (m, WeakTermTau)
substRuleType _ (m, WeakTermUpsilon x) = return (m, WeakTermUpsilon x)
substRuleType sub (m, WeakTermPi mName xts t) = do
  (xts', t') <- substRuleType'' sub xts t
  return (m, WeakTermPi mName xts' t')
substRuleType sub (m, WeakTermPiIntro info xts body) = do
  info' <- fmap2M (substRuleType' sub) info
  (xts', body') <- substRuleType'' sub xts body
  return (m, WeakTermPiIntro info' xts' body')
substRuleType sub@((a1, es1), (a2, es2)) (m, WeakTermPiElim e es)
  | (mx, WeakTermUpsilon x) <- e,
    a1 == x =
    case (mapM asUpsilon es1, mapM asUpsilon es) of
      (Just xs', Just ys')
        | xs' == ys' -> return (m, WeakTermPiElim (mx, WeakTermConst a2) es2) -- `aOuter @ (処理済み, ..., 処理済み)` への変換
      _ ->
        raiseError
          m
          "generalized inductive type cannot be used to construct a nested inductive type"
  | otherwise = do
    e' <- substRuleType sub e
    es' <- mapM (substRuleType sub) es
    return (m, WeakTermPiElim e' es')
substRuleType sub (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- substRuleType sub t
  if fst (fst sub) == x
    then return (m, WeakTermIter (mx, x, t') xts e)
    else do
      (xts', e') <- substRuleType'' sub xts e
      return (m, WeakTermIter (mx, x, t') xts' e')
substRuleType _ (m, WeakTermConst x) = return (m, WeakTermConst x)
substRuleType _ (m, WeakTermZeta x) = return (m, WeakTermZeta x)
substRuleType sub (m, WeakTermInt t x) = do
  t' <- substRuleType sub t
  return (m, WeakTermInt t' x)
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
substRuleType sub (m, WeakTermCase indName e cxtes) = do
  e' <- substRuleType sub e
  cxtes' <-
    flip mapM cxtes $ \((c, xts), body) -> do
      (xts', body') <- substRuleType'' sub xts body
      return ((c, xts'), body')
  return (m, WeakTermCase indName e' cxtes')
substRuleType sub (m, WeakTermQuestion e t) = do
  e' <- substRuleType sub e
  t' <- substRuleType sub t
  return (m, WeakTermQuestion e' t')
substRuleType sub (m, WeakTermErase xs e) = do
  e' <- substRuleType sub e
  return (m, WeakTermErase xs e')

substRuleType' :: SubstRule -> [WeakIdentPlus] -> WithEnv [WeakIdentPlus]
substRuleType' _ [] = return []
substRuleType' sub ((m, x, t) : xts) = do
  t' <- substRuleType sub t
  if fst (fst sub) == x
    then return $ (m, x, t') : xts
    else do
      xts' <- substRuleType' sub xts
      return $ (m, x, t') : xts'

substRuleType'' ::
  SubstRule ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv ([WeakIdentPlus], WeakTermPlus)
substRuleType'' sub [] e = do
  e' <- substRuleType sub e
  return ([], e')
substRuleType'' sub ((m, x, t) : xts) e = do
  t' <- substRuleType sub t
  if fst (fst sub) == x
    then return ((m, x, t') : xts, e)
    else do
      (xts', e') <- substRuleType'' sub xts e
      return ((m, x, t') : xts', e')
