module Parse.Rule
  ( parseData,
    asData,
    generateProjections,
  )
where

import Data.Log
import Control.Monad.State.Lazy
import Data.Env
import Data.Ident
import Data.Hint
import Data.Namespace
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm
import Parse.Discern
import Parse.Interpret

type Rule = -- inference rule
  ( Hint, -- location of the name
    T.Text, -- the name of the rule
    Hint, -- location of the rule
    [WeakIdentPlus], -- the antecedents of the inference rule (e.g. [(x, A), (xs, list A)])
    WeakTermPlus -- the consequent of the inference rule
  )

type Connective =
  ( Hint, -- location of the connective
    T.Text, -- the name of the connective (e.g. nat, list)
    [WeakIdentPlus], -- parameter of the connective (e.g. the `A` in `list A`)
    [Rule] -- list of introduction rule when inductive / list of elimination rule when coinductive
  )

parseData :: Hint -> [TreePlus] -> WithEnv [WeakStmt]
parseData m ts = do
  ts' <- mapM setupDataPrefix ts
  parseConnective m ts'

setupDataPrefix :: TreePlus -> WithEnv TreePlus
setupDataPrefix inputTree =
  case inputTree of
    (m, TreeNode ((ma, TreeLeaf a) : xts : rules)) -> do
      rules' <- mapM (setupDataPrefix' a) rules
      return (m, TreeNode ((ma, TreeLeaf a) : xts : rules'))
    _ ->
      raiseSyntaxError (fst inputTree) "(LEAF (TREE ... TREE) TREE)"

setupDataPrefix' :: T.Text -> TreePlus -> WithEnv TreePlus
setupDataPrefix' a inputTree =
  case inputTree of
    (m, TreeNode ((mb, TreeLeaf b) : rest)) ->
      return (m, TreeNode ((mb, TreeLeaf (a <> nsSep <> b)) : rest))
    _ ->
      raiseSyntaxError (fst inputTree) "(LEAF (TREE ... TREE) TREE)"

-- variable naming convention on parsing connectives:
--   a : the name of a formation rule, like `nat`, `list`, `stream`, etc.
--   b : the name of an introduction/elimination rule, like `zero`, `cons`, `head`, etc.
--   x : the name of an argument of a formation rule, like `A` in `list A` or `stream A`.
--   y : the name of an argument of an introduction/elimination rule, like `w` or `ws` in `cons : Pi (w : A, ws : list A). list A`.
parseConnective :: Hint -> [TreePlus] -> WithEnv [WeakStmt]
parseConnective m ts = do
  connectiveList <- mapM parseConnective' ts
  fs <- mapM formationRuleOf connectiveList
  ats <- mapM ruleAsWeakTextPlus fs
  bts <- concat <$> mapM toInternalRuleList connectiveList
  checkNameSanity m $ ats ++ bts
  connectiveList' <- toData ats bts connectiveList
  ruleList <- concat <$> mapM (toDataIntroList ats bts) connectiveList
  return $ connectiveList' ++ ruleList

parseConnective' :: TreePlus -> WithEnv Connective
parseConnective' inputTree =
  case inputTree of
    (m, TreeNode ((_, TreeLeaf name) : (_, TreeNode xts) : rules)) -> do
      xts' <- mapM interpretWeakIdentPlus xts
      rules' <- mapM parseRule rules
      return (m, name, xts', rules')
    _ ->
      raiseSyntaxError (fst inputTree) "(LEAF (TREE ... TREE) ...)"

toDataInfo :: TreePlus -> WithEnv (WeakTextPlus, [WeakIdentPlus])
toDataInfo ts = do
  connectiveList <- parseConnective' ts
  fs <- formationRuleOf connectiveList
  at <- ruleAsWeakTextPlus fs
  bts <- toInternalRuleList connectiveList
  case bts of
    [(_, "new", (_, WeakTermPi xts _))] ->
      return (at, xts)
    _ ->
      undefined

generateProjections :: TreePlus -> WithEnv [WeakStmt]
generateProjections t = do
  ((ma, a, ta), bts) <- toDataInfo t
  (xts, _) <- separatePi ta
  h <- newNameWith'' "_"
  let dom = (ma, h, (ma, WeakTermPiElim (ma, WeakTermUpsilon $ asIdent a) (map toVar' xts)))
  forM bts $ \(mb, b, tb) ->
    WeakStmtLet mb
      <$> discernIdentPlus
        ( mb,
          asIdent (a <> nsSep <> asText b),
          (mb, WeakTermPi (xts ++ [dom]) tb)
        )
      <*> discern
        ( mb,
          WeakTermPiIntro
            (xts ++ [dom])
            ( mb,
              WeakTermPiElim
                (mb, WeakTermUpsilon $ asIdent (a <> nsSep <> "case"))
                $ tb : map toVar' (xts ++ [dom]) ++ [(mb, WeakTermPiIntro bts (mb, WeakTermUpsilon b))]
            )
        )

separatePi :: WeakTermPlus -> WithEnv ([WeakIdentPlus], WeakTermPlus)
separatePi e =
  case e of
    (_, WeakTermPi xts cod) ->
      return (xts, cod)
    _ -> do
      p' e
      raiseSyntaxError (fst e) "(pi (TREE ... TREE) TREE)"

parseRule :: TreePlus -> WithEnv Rule
parseRule inputTree =
  case inputTree of
    (m, TreeNode [(mName, TreeLeaf name), (_, TreeNode xts), t]) -> do
      t' <- interpret t
      xts' <- mapM interpretWeakIdentPlus xts
      return (m, name, mName, xts', t')
    _ ->
      raiseSyntaxError (fst inputTree) "(LEAF (TREE ... TREE) TREE)"

checkNameSanity :: Hint -> [WeakTextPlus] -> WithEnv ()
checkNameSanity m atsbts = do
  let asbs = map (\(_, x, _) -> x) atsbts
  when (not $ isLinear asbs) $
    raiseError
      m
      "the names of the rules of inductive/coinductive type must be distinct"

toData :: [WeakTextPlus] -> [WeakTextPlus] -> [Connective] -> WithEnv [WeakStmt]
toData ats bts connectiveList =
  case connectiveList of
    [] ->
      return []
    connective@(m, ai, xts, _) : rest -> do
      at <- formationRuleOf connective >>= ruleAsWeakIdentPlus
      let cod = (m, WeakTermPiElim (m, WeakTermUpsilon $ asIdent ai) (map toVar' xts))
      let atsbts = map textPlusToWeakIdentPlus $ ats ++ bts
      -- definition of inductive type
      indType <- discern (m, WeakTermPiIntro xts (m, WeakTermPi atsbts cod))
      at' <- discernIdentPlus at
      -- definition of case
      z <- newNameWith'' "value"
      let zt = (m, z, cod)
      -- univVarName <- newNameWith'' "univ"
      let univVarName = asIdent "internal.case-tau"
      let univVar = (m, WeakTermUpsilon univVarName)
      bts' <- mapM (toCaseBranchType univVar) bts
      let indArgs = [(m, univVarName, (m, WeakTermTau))] ++ xts ++ [zt] ++ bts'
      rest' <- toData ats bts rest
      caseBody <-
        discern
          (m, WeakTermPiIntro indArgs (m, WeakTermPiElim (toVar' zt) (map toVar' atsbts)))
      caseIdent <-
        discernIdentPlus
          (m, asIdent $ ai <> nsSep <> "case", (m, WeakTermPi indArgs univVar))
      let stmtLet = WeakStmtLet (m {metaIsReducible = False}) at' indType
      let stmtCase = WeakStmtLetBypass m caseIdent caseBody
      return $ [stmtLet] ++ rest' ++ [stmtCase]

toCaseBranchType :: WeakTermPlus -> WeakTextPlus -> WithEnv WeakIdentPlus
toCaseBranchType univVar (mx, x, t) =
  case t of
    (mPi, WeakTermPi args _) ->
      return (mx, asIdent x, (mPi, WeakTermPi args univVar))
    _ ->
      raiseCritical' "toCaseBranchType"

toDataIntroList :: [WeakTextPlus] -> [WeakTextPlus] -> Connective -> WithEnv [WeakStmt]
toDataIntroList ats bts (_, a, xts, rules) = do
  let ats' = map textPlusToWeakIdentPlus ats
  let bts' = map textPlusToWeakIdentPlus bts
  concat <$> mapM (toDataIntro ats' bts' xts a) rules

toDataIntro ::
  [WeakIdentPlus] ->
  [WeakIdentPlus] ->
  [WeakIdentPlus] ->
  T.Text ->
  Rule ->
  WithEnv [WeakStmt]
toDataIntro ats bts xts ai (mb, bi, m, yts, cod)
  | (_, WeakTermPiElim (_, WeakTermUpsilon a') es) <- cod,
    ai == asText a',
    length xts == length es = do
    let vs = varWeakTermPlus' (yts ++ ats ++ bts) []
    let xts' = filter (\(_, x, _) -> x `S.member` vs) xts
    constructor <-
      discern
        ( m,
          WeakTermPiIntro
            (xts' ++ yts)
            ( m,
              WeakTermPiIntro
                (ats ++ bts)
                (m, WeakTermPiElim (mb, WeakTermUpsilon (asIdent bi)) (map toVar' yts)) -- ill-typed!
            )
        )
    constructorIdent <-
      discernIdentPlus
        (mb, asIdent bi, (m, WeakTermPi (xts' ++ yts) cod))
    return [WeakStmtLetBypass m constructorIdent constructor]
  | otherwise =
    raiseError m $
      "the succedent of an introduction rule of `"
        <> ai
        <> "` must be of the form `("
        <> showItems (ai : map (const "_") xts)
        <> ")`"

ruleAsWeakIdentPlus :: Rule -> WithEnv WeakIdentPlus
ruleAsWeakIdentPlus (mb, b, m, xts, t) =
  return (mb, asIdent b, (m, WeakTermPi xts t))

ruleAsWeakTextPlus :: Rule -> WithEnv WeakTextPlus
ruleAsWeakTextPlus (mb, b, m, xts, t) =
  return (mb, b, (m, WeakTermPi xts t))

textPlusToWeakIdentPlus :: WeakTextPlus -> WeakIdentPlus
textPlusToWeakIdentPlus (mx, x, t) =
  (mx, asIdent x, t)

formationRuleOf :: Connective -> WithEnv Rule
formationRuleOf (m, a, xts, _) =
  return (m, a, m, xts, (m, WeakTermTau))

toInternalRuleList :: Connective -> WithEnv [WeakTextPlus]
toInternalRuleList (_, _, _, rules) =
  mapM ruleAsWeakTextPlus rules

toVar' :: WeakIdentPlus -> WeakTermPlus
toVar' (m, x, _) =
  (m, WeakTermUpsilon x)

toApp :: Hint -> TreePlus -> [TreePlus] -> WithEnv TreePlus
toApp m a xts = do
  argList <- mapM extractArg xts
  return (m, TreeNode (a : argList))

asData :: Hint -> [TreePlus] -> WithEnv TreePlus
asData m ts =
  case ts of
    (a : (_, TreeNode xts) : rules) -> do
      app <- toApp m a xts
      return
        ( m,
          TreeNode
            [ a,
              (m, TreeNode xts),
              ( m,
                TreeNode
                  [ (m, TreeLeaf "new"),
                    (m, TreeNode rules),
                    app
                  ]
              )
            ]
        )
    _ ->
      raiseSyntaxError m "(LEAF (TREE ... TREE) ...)"

extractArg :: TreePlus -> WithEnv TreePlus
extractArg tree =
  case tree of
    (m, TreeLeaf x) ->
      return (m, TreeLeaf x)
    (_, TreeNode [(m, TreeLeaf x), _]) ->
      return (m, TreeLeaf x)
    t ->
      raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"
