module Parse.Rule
  ( parseInductive,
    asInductive,
    insForm,
    insInductive,
    internalize,
    registerLabelInfo,
    generateProjections,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm
import Parse.Discern
import Parse.Interpret

parseInductive :: Meta -> [TreePlus] -> WithEnv [WeakStmt]
parseInductive m ts = do
  ts' <- mapM setupIndPrefix ts
  parseConnective m ts' toInductive toInductiveIntroList

setupIndPrefix :: TreePlus -> WithEnv TreePlus
setupIndPrefix inputTree =
  case inputTree of
    (m, TreeNode ((ma, TreeLeaf a) : xts : rules)) -> do
      rules' <- mapM (setupIndPrefix' a) rules
      return (m, TreeNode ((ma, TreeLeaf a) : xts : rules'))
    _ -> raiseSyntaxError (fst inputTree) "(LEAF (TREE ... TREE) TREE)"

setupIndPrefix' :: T.Text -> TreePlus -> WithEnv TreePlus
setupIndPrefix' a inputTree =
  case inputTree of
    (m, TreeNode ((mb, TreeLeaf b) : rest)) ->
      return (m, TreeNode ((mb, TreeLeaf (a <> ":" <> b)) : rest))
    _ -> raiseSyntaxError (fst inputTree) "(LEAF (TREE ... TREE) TREE)"

-- variable naming convention on parsing connectives:
--   a : the name of a formation rule, like `nat`, `list`, `stream`, etc.
--   b : the name of an introduction/elimination rule, like `zero`, `cons`, `head`, etc.
--   x : the name of an argument of a formation rule, like `A` in `list A` or `stream A`.
--   y : the name of an argument of an introduction/elimination rule, like `w` or `ws` in `cons : Pi (w : A, ws : list A). list A`.
parseConnective ::
  Meta ->
  [TreePlus] ->
  ([WeakTextPlus] -> [WeakTextPlus] -> Connective -> WithEnv [WeakStmt]) ->
  ([WeakTextPlus] -> Connective -> WithEnv [WeakStmt]) ->
  WithEnv [WeakStmt]
parseConnective m ts f g = do
  connectiveList <- mapM parseConnective' ts
  fs <- mapM formationRuleOf' connectiveList
  ats <- mapM ruleAsWeakTextPlus fs
  bts <- concat <$> mapM toInternalRuleList connectiveList
  checkNameSanity m $ ats ++ bts
  connectiveList' <- concat <$> mapM (f ats bts) connectiveList
  ruleList <- concat <$> mapM (g ats) connectiveList
  return $ connectiveList' ++ ruleList

parseConnective' :: TreePlus -> WithEnv Connective
parseConnective' inputTree =
  case inputTree of
    (m, TreeNode ((_, TreeLeaf name) : (_, TreeNode xts) : rules)) -> do
      xts' <- mapM interpretWeakIdentPlus xts
      rules' <- mapM parseRule rules
      return (m, name, xts', rules')
    _ -> raiseSyntaxError (fst inputTree) "(LEAF (TREE ... TREE) ...)"

toIndInfo :: [TreePlus] -> WithEnv ([WeakTextPlus], [WeakTextPlus])
toIndInfo ts = do
  connectiveList <- mapM parseConnective' ts
  fs <- mapM formationRuleOf connectiveList
  ats <- mapM ruleAsWeakTextPlus fs
  bts <- concat <$> mapM toInternalRuleList connectiveList
  return (ats, bts)

registerLabelInfo :: [TreePlus] -> WithEnv ()
registerLabelInfo ts = do
  (ats, bts) <- toIndInfo ts
  forM_ ats $ \(_, a, _) -> do
    let asbs = map (\(_, x, _) -> x) $ ats ++ bts
    modify (\env -> env {labelEnv = Map.insert a asbs (labelEnv env)})

generateProjections :: [TreePlus] -> WithEnv [WeakStmt]
generateProjections ts = do
  (ats, bts) <- toIndInfo ts
  let bts' = map textPlusToWeakIdentPlus bts
  stmtListList <-
    forM ats $ \(ma, a, ta) ->
      forM bts $ \(mb, b, tb) -> do
        xts <- takeXTS ta
        (dom@(my, y, ty), cod) <- separate tb
        v <- newNameWith'' "base"
        let b' = a <> ":" <> b
        e <-
          discern
            ( mb,
              weakTermPiIntro
                (xts ++ [dom])
                ( mb,
                  WeakTermCase
                    (Just $ asIdent a)
                    (my, WeakTermUpsilon y)
                    [ ( ( (mb, asIdent (a <> ":unfold")),
                          xts ++ [(ma, asIdent a, ta)] ++ bts' ++ [(mb, v, ty)] -- `xts ++` is required since LetWT bypasses `infer`
                        ),
                        ( mb,
                          WeakTermPiElim (mb, WeakTermUpsilon $ asIdent b) [(mb, WeakTermUpsilon v)]
                        )
                      )
                    ]
                )
            )
        bt <- discernIdentPlus (mb, asIdent b', (mb, weakTermPi (xts ++ [dom]) cod))
        return [WeakStmtLetWT mb bt e]
  return $ concat $ concat stmtListList

separate :: WeakTermPlus -> WithEnv (WeakIdentPlus, WeakTermPlus)
separate e =
  case e of
    (_, WeakTermPi _ [xt] cod) ->
      return (xt, cod)
    _ ->
      raiseSyntaxError (fst e) "(pi (TREE) TREE)"

takeXTS :: WeakTermPlus -> WithEnv [WeakIdentPlus]
takeXTS t =
  case t of
    (_, WeakTermPi _ xts _) ->
      return xts
    _ ->
      raiseSyntaxError (fst t) "(pi (TREE ... TREE) TREE)"

parseRule :: TreePlus -> WithEnv Rule
parseRule inputTree =
  case inputTree of
    (m, TreeNode [(mName, TreeLeaf name), (_, TreeNode xts), t]) -> do
      t' <- interpret t
      xts' <- mapM interpretWeakIdentPlus xts
      return (m, name, mName, xts', t')
    _ ->
      raiseSyntaxError (fst inputTree) "(LEAF (TREE ... TREE) TREE)"

checkNameSanity :: Meta -> [WeakTextPlus] -> WithEnv ()
checkNameSanity m atsbts = do
  let asbs = map (\(_, x, _) -> x) atsbts
  when (not $ linearCheck asbs) $
    raiseError
      m
      "the names of the rules of inductive/coinductive type must be distinct"

toInductive ::
  [WeakTextPlus] -> [WeakTextPlus] -> Connective -> WithEnv [WeakStmt]
toInductive ats bts connective@(m, ai, xts, _) = do
  at <- formationRuleOf connective >>= ruleAsWeakIdentPlus
  let cod = (m, WeakTermPiElim (m, WeakTermUpsilon $ asIdent ai) (map toVar' xts))
  let atsbts = map textPlusToWeakIdentPlus $ ats ++ bts
  -- definition of inductive type
  indType <-
    discern
      (m, weakTermPiIntro xts (m, WeakTermPi (Just ai) atsbts cod))
  at' <- discernIdentPlus at
  insForm (length ats) at' indType
  -- definition of induction principle (fold)
  z <- newNameWith'' "_"
  let zt = (m, z, cod)
  let indArgs = xts ++ [zt] ++ atsbts
  inductionPrinciple <-
    discern
      (m, weakTermPiIntro indArgs (m, WeakTermPiElim (toVar' zt) (map toVar' atsbts)))
  indIdent <-
    discernIdentPlus
      (m, asIdent $ ai <> ":induction", (m, weakTermPi indArgs cod))
  return
    [ WeakStmtLetWT m at' indType,
      WeakStmtLetWT m indIdent inductionPrinciple
    ]

toInductiveIntroList :: [WeakTextPlus] -> Connective -> WithEnv [WeakStmt]
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
  WithEnv [WeakStmt]
toInductiveIntro ats bts xts ai (mb, bi, m, yts, cod)
  | (_, WeakTermPiElim (_, WeakTermUpsilon a') es) <- cod,
    ai == asText a',
    length xts == length es = do
    let vs = varWeakTermPlus (m, weakTermPi yts cod)
    let ixts = filter (\(_, (_, x, _)) -> x `S.member` vs) $ zip [0 ..] xts
    let (is, xts') = unzip ixts
    constructor <-
      discern
        ( m,
          weakTermPiIntro
            (xts' ++ yts)
            ( m,
              WeakTermPiIntro
                (Just (asIdent ai, bi, xts' ++ yts))
                (ats ++ bts)
                (m, WeakTermPiElim (mb, WeakTermUpsilon (asIdent bi)) (map toVar' yts))
            )
        )
    constructorIdent <-
      discernIdentPlus
        (mb, asIdent bi, (m, weakTermPi (xts' ++ yts) cod))
    case constructor of
      (_, WeakTermPiIntro _ xtsyts (_, WeakTermPiIntro indInfo@(Just (ai', _, _)) atsbts (_, WeakTermPiElim b _))) -> do
        let as = take (length ats) $ map (\(_, x, _) -> asInt x) atsbts
        modify (\env -> env {revIndEnv = Map.insert bi (ai', is) (revIndEnv env)})
        insInductive as constructorIdent
        yts' <- mapM (internalize as atsbts) $ drop (length is) xtsyts
        return
          [ WeakStmtLetWT
              m
              constructorIdent
              ( m {metaIsReducible = False},
                weakTermPiIntro
                  xtsyts
                  ( m,
                    WeakTermPiIntro indInfo atsbts (m, WeakTermPiElim b yts')
                  )
              )
          ]
      _ -> raiseCritical m "inductive-intro"
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

insForm :: Int -> WeakIdentPlus -> WeakTermPlus -> WithEnv ()
insForm i (_, a, _) e
  | i == 1 =
    modify (\env -> env {formationEnv = IntMap.insert (asInt a) (Just e) (formationEnv env)})
  | otherwise =
    modify (\env -> env {formationEnv = IntMap.insert (asInt a) Nothing (formationEnv env)})

insInductive :: [Int] -> WeakIdentPlus -> WithEnv ()
insInductive as bt =
  case as of
    [ai] -> do
      ienv <- gets indEnv
      modify (\env -> env {indEnv = IntMap.insertWith optConcat ai (Just [bt]) ienv})
    _ ->
      forM_ as $ \ai ->
        modify (\env -> env {indEnv = IntMap.insert ai Nothing (indEnv env)})

optConcat :: Maybe [a] -> Maybe [a] -> Maybe [a]
optConcat mNew mOld = do
  mNew' <- mNew
  mOld' <- mOld
  -- insert mNew at the end of the list (to respect the structure of ind/coind represented as pi/sigma)
  return $ mOld' ++ mNew'

asInductive :: [TreePlus] -> WithEnv [TreePlus]
asInductive =
  \case
    [] -> return []
    (t : ts) -> do
      (sub, t') <- asInductive' t
      ts' <- asInductive $ map (substTree sub) ts
      return $ t' : ts'

asInductive' :: TreePlus -> WithEnv ((T.Text, T.Text), TreePlus)
asInductive' t =
  case t of
    (m, TreeNode ((_, TreeLeaf a) : (_, TreeNode xts) : rules)) -> do
      let a' = "(" <> a <> ")"
      let sub = (a, a')
      let xts' = map (substTree sub) xts
      rules'' <- mapM styleRule $ map (substTree sub) rules
      let hole = "(_)"
      argList <- mapM extractArg xts
      return
        ( (a, a'),
          ( m,
            TreeNode
              [ (m, TreeLeaf a),
                (m, TreeNode xts'),
                ( m,
                  TreeNode
                    [ (m, TreeLeaf "unfold"),
                      ( m,
                        TreeNode
                          ( [ ( m,
                                TreeNode
                                  [ (m, TreeLeaf a'),
                                    ( m,
                                      TreeNode
                                        [ (m, TreeLeaf "pi"),
                                          (m, TreeNode xts'),
                                          (m, TreeLeaf "tau")
                                        ]
                                    )
                                  ]
                              )
                            ]
                              ++ rules''
                              ++ [ ( m,
                                     TreeNode
                                       [ (m, TreeLeaf hole),
                                         (m, TreeNode ((m, TreeLeaf a') : argList))
                                       ]
                                   )
                                 ]
                          )
                      ),
                      (m, TreeNode ((m, TreeLeaf a) : argList))
                    ]
                )
              ]
          )
        )
    _ -> raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) ...)"

extractArg :: TreePlus -> WithEnv TreePlus
extractArg =
  \case
    (m, TreeLeaf x) -> return (m, TreeLeaf x)
    (_, TreeNode [(m, TreeLeaf x), _]) -> return (m, TreeLeaf x)
    t -> raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

styleRule :: TreePlus -> WithEnv TreePlus
styleRule =
  \case
    (m, TreeNode [(mName, TreeLeaf name), (_, TreeNode xts), t]) ->
      return
        ( m,
          TreeNode
            [ (mName, TreeLeaf name),
              (m, TreeNode [(m, TreeLeaf "pi"), (m, TreeNode xts), t])
            ]
        )
    t -> raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) TREE)"

data Mode
  = ModeForward
  | ModeBackward
  deriving (Show)

internalize ::
  [Int] -> [WeakIdentPlus] -> WeakIdentPlus -> WithEnv WeakTermPlus
internalize as atsbts (m, y, t) = do
  let sub = IntMap.fromList $ zip as (map toVar' atsbts)
  theta ModeForward sub atsbts t (m, WeakTermUpsilon y)

flipMode :: Mode -> Mode
flipMode mode =
  case mode of
    ModeForward -> ModeBackward
    ModeBackward -> ModeForward

isResolved :: SubstWeakTerm -> WeakTermPlus -> Bool
isResolved sub e = do
  let outerVarList = IntMap.keys sub
  let freeVarSet = S.map asInt $ varWeakTermPlus e
  all (`S.notMember` freeVarSet) outerVarList

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
    (_, WeakTermPiElim va@(_, WeakTermUpsilon ai) es)
      | Just _ <- IntMap.lookup (asInt ai) isub ->
        thetaInductive mode isub ai atsbts es e
      -- nested inductive
      | Just (Just bts) <- IntMap.lookup (asInt ai) ienv,
        not (all (isResolved isub) es) ->
        thetaInductiveNested mode isub atsbts e va ai es bts
      -- nestedの外側がmutualであるとき。このときはエラーとする。
      | Just Nothing <- IntMap.lookup (asInt ai) ienv ->
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
  Ident ->
  [WeakIdentPlus] ->
  [WeakTermPlus] ->
  WeakTermPlus ->
  WithEnv WeakTermPlus
thetaInductive mode isub a atsbts es e
  | ModeBackward <- mode =
    raiseError (metaOf e) $
      "found a contravariant occurence of `"
        <> asText a
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
  Ident -> -- list (トップレベルで定義されている名前、つまりouterの名前)
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

thetaInductiveNestedMutual :: Meta -> Ident -> WithEnv WeakTermPlus
thetaInductiveNestedMutual m ai =
  raiseError m $
    "mutual inductive type `"
      <> asText ai
      <> "` cannot be used to construct a nested inductive type"

lookupInductive ::
  Meta ->
  Ident ->
  WithEnv ([WeakIdentPlus], WeakIdentPlus, [WeakIdentPlus])
lookupInductive m ai = do
  fenv <- gets formationEnv
  case IntMap.lookup (asInt ai) fenv of
    Just (Just (_, WeakTermPiIntro Nothing xts (_, WeakTermPi (Just _) atsbts (_, WeakTermPiElim (_, WeakTermUpsilon _) _)))) -> do
      let at = head atsbts
      let bts = tail atsbts -- valid since a is not mutual
      return (xts, at, bts)
    Just (Just e) ->
      raiseCritical m $
        "malformed inductive type (Parse.lookupInductive): \n" <> toText e
    Just Nothing ->
      raiseError m $
        "the inductive type `" <> asText ai <> "` must be a non-mutual inductive type"
    Nothing -> raiseCritical m $ "no such inductive type defined: " <> asText ai

-- nested inductiveにおける引数をinternalizeする。
-- （これ、recursiveに処理できないの？）
toInternalizedArg ::
  Mode ->
  SubstWeakTerm -> -- inductiveのためのaのsubst (outer -> inner)
  Ident -> -- innerでのaの名前。listの定義の中に出てくるほうのlist.
  Ident -> -- outerでのaの名前。listとか。
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
  let xs = map (\(_, x, _) -> asInt x) xts -- fixme: このへんもrenameBinderでやったほうがいい？
  let sub = IntMap.fromList $ zip xs es
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
renameBinder binder e =
  case binder of
    [] -> return ([], e)
    (m, x, t) : ats -> do
      x' <- newNameWith x
      let sub = IntMap.singleton (asInt x) (m, WeakTermUpsilon x')
      let (ats', e') = substWeakTermPlus'' sub ats e -- discern済みなのでこれでオーケーのはず
      (ats'', e'') <- renameBinder ats' e'
      return ((m, x', t) : ats'', e'')

type RuleTypeDom = (Ident, [WeakTermPlus])

type RuleTypeCod = (Ident, [WeakTermPlus])

type SubstRule = (RuleTypeDom, RuleTypeCod)

-- subst a @ (e1, ..., en) ~> a' @ (e1', ..., en')
substRuleType :: SubstRule -> WeakTermPlus -> WithEnv WeakTermPlus
substRuleType sub@((a1, es1), (a2, es2)) term =
  case term of
    (m, WeakTermTau) ->
      return (m, WeakTermTau)
    (m, WeakTermUpsilon x) ->
      return (m, WeakTermUpsilon x)
    (m, WeakTermPi mName xts t) -> do
      (xts', t') <- substRuleType'' sub xts t
      return (m, WeakTermPi mName xts' t')
    (m, WeakTermPiIntro info xts body) -> do
      (xts', body') <- substRuleType'' sub xts body
      case info of
        Nothing -> return (m, WeakTermPiIntro Nothing xts' body')
        Just (indName, consName, args) -> do
          args' <- substRuleType' sub args
          return (m, WeakTermPiIntro (Just (indName, consName, args')) xts' body')
    (m, WeakTermPiElim e es)
      | (mx, WeakTermUpsilon x) <- e,
        a1 == x ->
        case (mapM asUpsilon es1, mapM asUpsilon es) of
          (Just xs', Just ys')
            | xs' == ys' -> return (m, WeakTermPiElim (mx, WeakTermUpsilon a2) es2) -- `aOuter @ (処理済み, ..., 処理済み)` への変換
          _ ->
            raiseError
              m
              "generalized inductive type cannot be used to construct a nested inductive type"
      | otherwise -> do
        e' <- substRuleType sub e
        es' <- mapM (substRuleType sub) es
        return (m, WeakTermPiElim e' es')
    (m, WeakTermIter (mx, x, t) xts e) -> do
      t' <- substRuleType sub t
      if fst (fst sub) == x
        then return (m, WeakTermIter (mx, x, t') xts e)
        else do
          (xts', e') <- substRuleType'' sub xts e
          return (m, WeakTermIter (mx, x, t') xts' e')
    (m, WeakTermConst x) ->
      return (m, WeakTermConst x)
    (m, WeakTermBoxElim x) ->
      return (m, WeakTermBoxElim x)
    (m, WeakTermZeta x) ->
      return (m, WeakTermZeta x)
    (m, WeakTermInt t x) -> do
      t' <- substRuleType sub t
      return (m, WeakTermInt t' x)
    (m, WeakTermFloat t x) -> do
      t' <- substRuleType sub t
      return (m, WeakTermFloat t' x)
    (m, WeakTermEnum x) ->
      return (m, WeakTermEnum x)
    (m, WeakTermEnumIntro l) ->
      return (m, WeakTermEnumIntro l)
    (m, WeakTermEnumElim (e, t) branchList) -> do
      t' <- substRuleType sub t
      e' <- substRuleType sub e
      let (caseList, es) = unzip branchList
      es' <- mapM (substRuleType sub) es
      return (m, WeakTermEnumElim (e', t') (zip caseList es'))
    (m, WeakTermArray dom k) -> do
      dom' <- substRuleType sub dom
      return (m, WeakTermArray dom' k)
    (m, WeakTermArrayIntro k es) -> do
      es' <- mapM (substRuleType sub) es
      return (m, WeakTermArrayIntro k es')
    (m, WeakTermArrayElim mk xts v e) -> do
      v' <- substRuleType sub v
      (xts', e') <- substRuleType'' sub xts e
      return (m, WeakTermArrayElim mk xts' v' e')
    (m, WeakTermStruct ts) ->
      return (m, WeakTermStruct ts)
    (m, WeakTermStructIntro ets) -> do
      let (es, ts) = unzip ets
      es' <- mapM (substRuleType sub) es
      return (m, WeakTermStructIntro $ zip es' ts)
    (m, WeakTermStructElim xts v e) -> do
      v' <- substRuleType sub v
      let xs = map (\(_, x, _) -> x) xts
      if fst (fst sub) `elem` xs
        then return (m, WeakTermStructElim xts v' e)
        else do
          e' <- substRuleType sub e
          return (m, WeakTermStructElim xts v' e')
    (m, WeakTermCase indName e cxtes) -> do
      e' <- substRuleType sub e
      cxtes' <-
        flip mapM cxtes $ \((c, xts), body) -> do
          (xts', body') <- substRuleType'' sub xts body
          return ((c, xts'), body')
      return (m, WeakTermCase indName e' cxtes')
    (m, WeakTermQuestion e t) -> do
      e' <- substRuleType sub e
      t' <- substRuleType sub t
      return (m, WeakTermQuestion e' t')
    (m, WeakTermErase xs e) -> do
      e' <- substRuleType sub e
      return (m, WeakTermErase xs e')

substRuleType' :: SubstRule -> [WeakIdentPlus] -> WithEnv [WeakIdentPlus]
substRuleType' sub binder =
  case binder of
    [] -> return []
    (m, x, t) : xts -> do
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
substRuleType'' sub binder e =
  case binder of
    [] -> do
      e' <- substRuleType sub e
      return ([], e')
    (m, x, t) : xts -> do
      t' <- substRuleType sub t
      if fst (fst sub) == x
        then return ((m, x, t') : xts, e)
        else do
          (xts', e') <- substRuleType'' sub xts e
          return ((m, x, t') : xts', e')
