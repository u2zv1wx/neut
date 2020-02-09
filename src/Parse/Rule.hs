{-# LANGUAGE OverloadedStrings #-}

module Parse.Rule
  ( parseInductive
  , parseCoinductive
  , insForm
  , insInductive
  , insCoinductive
  , internalize
  , externalize
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Monoid ((<>))

import qualified Data.HashMap.Strict as Map

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm
import Parse.Interpret

parseInductive :: [TreePlus] -> WithEnv [Stmt]
parseInductive ts = parseConnective ts toInductive toInductiveIntroList

parseCoinductive :: [TreePlus] -> WithEnv [Stmt]
parseCoinductive ts = parseConnective ts toCoinductive toCoinductiveElimList

-- variable naming convention on parsing connectives:
--   a : the name of a formation rule, like `nat`, `list`, `stream`, etc.
--   b : the name of an introduction/elimination rule, like `zero`, `cons`, `head`, etc.
--   x : the name of an argument of a formation rule, like `A` in `list A` or `stream A`.
--   y : the name of an argument of an introduction/elimination rule, like `w` or `ws` in `cons : Pi (w : A, ws : list A). list A`.
parseConnective ::
     [TreePlus]
  -> ([IdentifierPlus] -> [IdentifierPlus] -> Connective -> WithEnv Stmt)
  -> ([IdentifierPlus] -> Connective -> WithEnv [Stmt])
  -> WithEnv [Stmt]
parseConnective ts f g = do
  connectiveList <- mapM parseConnective' ts
  let ats = map (ruleAsIdentPlus . formationRuleOf) connectiveList
  let bts = concatMap toInternalRuleList connectiveList
  connectiveList' <- mapM (f ats bts) connectiveList
  ruleList <- concat <$> mapM (g ats) connectiveList
  return $ connectiveList' ++ ruleList

parseConnective' :: TreePlus -> WithEnv Connective
parseConnective' (m, TreeNode ((_, TreeAtom name):(_, TreeNode xts):rules)) = do
  m' <- adjustPhase m
  xts' <- mapM interpretIdentifierPlus xts
  rules' <- mapM parseRule rules
  return (m', name, xts', rules')
parseConnective' _ = throwError' "parseConnective: syntax error"

parseRule :: TreePlus -> WithEnv Rule
parseRule (m, TreeNode [(mName, TreeAtom name), (_, TreeNode xts), t]) = do
  m' <- adjustPhase m
  mName' <- adjustPhase mName
  t' <- interpret t
  xts' <- mapM interpretIdentifierPlus xts
  return (m', name, mName', xts', t')
parseRule _ = throwError' "parseRule: syntax error"

-- represent the inductive logical connective within CoC
toInductive ::
     [IdentifierPlus] -> [IdentifierPlus] -> Connective -> WithEnv Stmt
toInductive ats bts connective@(m, a, xts, _) = do
  let formationRule = formationRuleOf connective
  return $
    StmtLetInductive
      (length ats)
      m
      (ruleAsIdentPlus formationRule)
      ( m
      , WeakTermPiIntro
          xts
          ( m
          , WeakTermPi
              (ats ++ bts)
              (m, WeakTermPiElim (m, WeakTermUpsilon a) (map toVar' xts))))

toInductiveIntroList :: [IdentifierPlus] -> Connective -> WithEnv [Stmt]
toInductiveIntroList ats (_, _, xts, rules) = do
  let bts = map ruleAsIdentPlus rules
  mapM (toInductiveIntro ats bts xts) rules

-- represent the introduction rule within CoC
toInductiveIntro ::
     [IdentifierPlus]
  -> [IdentifierPlus]
  -> [IdentifierPlus]
  -> Rule
  -> WithEnv Stmt
toInductiveIntro ats bts xts (mb, b, m, yts, cod) = do
  return $
    StmtLetInductiveIntro
      m
      (mb, b, (m, WeakTermPi (xts ++ yts) cod))
      (xts ++ yts)
      ats
      bts
      (mb, WeakTermUpsilon b)
      yts
      []
      (map (\(_, a, _) -> a) ats)

-- -- represent the coinductive logical connective within CoC
toCoinductive ::
     [IdentifierPlus] -> [IdentifierPlus] -> Connective -> WithEnv Stmt
toCoinductive ats bts c@(m, a, xts, _) = do
  let cod = (m, WeakTermPiElim (m, WeakTermUpsilon a) (map toVar' xts))
  let f = formationRuleOf c
  h <- newNameWith "cod"
  return $
    StmtLet
      m
      (ruleAsIdentPlus f) -- a : Pi xts. Univ
      (m, WeakTermPiIntro xts (m, WeakTermSigma (ats ++ bts ++ [(m, h, cod)])))

toCoinductiveElimList :: [IdentifierPlus] -> Connective -> WithEnv [Stmt]
toCoinductiveElimList ats (_, _, xts, rules) = do
  let bts = map ruleAsIdentPlus rules
  mapM (toCoinductiveElim ats bts xts) rules

-- represent the elimination rule within CoC
toCoinductiveElim ::
     [IdentifierPlus]
  -> [IdentifierPlus]
  -> [IdentifierPlus]
  -> Rule
  -> WithEnv Stmt
toCoinductiveElim ats bts xts (mb, b, m, yts, cod)
  | [yt] <- yts = do
    return $
      StmtLetCoinductiveElim
        m
        (mb, b, (m, WeakTermPi (xts ++ [yt]) cod))
        (xts ++ [yt])
        cod
        ats
        bts
        yt
        (toVar' yt)
        (m, WeakTermPiElim (mb, WeakTermUpsilon b) [toVar' yt])
        []
        (map (\(_, a, _) -> a) ats)
  | otherwise = throwError' "toCoinductiveElim"

ruleAsIdentPlus :: Rule -> IdentifierPlus
ruleAsIdentPlus (mb, b, m, xts, t) = (mb, b, (m, WeakTermPi xts t))

formationRuleOf :: Connective -> Rule
formationRuleOf = undefined

toInternalRuleList :: Connective -> [IdentifierPlus]
toInternalRuleList (_, _, _, rules) = map ruleAsIdentPlus rules

toVar' :: IdentifierPlus -> WeakTermPlus
toVar' (m, x, _) = (m, WeakTermUpsilon x)

-- toVar'' :: IdentifierPlus -> (WeakTermPlus, WeakTermPlus)
-- toVar'' (m, x, t) = ((m, WeakTermUpsilon x), t)
insForm :: Int -> IdentifierPlus -> WeakTermPlus -> WithEnv ()
insForm 1 (_, a, _) e =
  modify (\env -> env {formationEnv = Map.insert a (Just e) (formationEnv env)})
insForm _ (_, a, _) _ =
  modify (\env -> env {formationEnv = Map.insert a Nothing (formationEnv env)})

insInductive :: [Identifier] -> IdentifierPlus -> WithEnv ()
insInductive [a] bt = do
  ienv <- gets inductiveEnv
  modify
    (\env -> env {inductiveEnv = Map.insertWith optConcat a (Just [bt]) ienv})
insInductive as _ = do
  forM_ as $ \a -> do
    modify
      (\env -> env {inductiveEnv = Map.insert a Nothing (inductiveEnv env)})

insCoinductive :: [Identifier] -> IdentifierPlus -> WithEnv ()
insCoinductive [a] bt = do
  cenv <- gets coinductiveEnv
  modify
    (\env -> env {coinductiveEnv = Map.insertWith optConcat a (Just [bt]) cenv})
insCoinductive as _ = do
  forM_ as $ \a -> do
    modify
      (\env -> env {coinductiveEnv = Map.insert a Nothing (coinductiveEnv env)})

optConcat :: Maybe [a] -> Maybe [a] -> Maybe [a]
optConcat mNew mOld = do
  mNew' <- mNew
  mOld' <- mOld
  -- insert mNew at the end of the list (to respect the structure of ind/coind represented as pi/sigma)
  return $ mOld' ++ mNew'

-- ここでモジュールを切るべき？
data Mode
  = ModeInternalize
  | ModeExternalize

internalize ::
     SubstWeakTerm -> [IdentifierPlus] -> IdentifierPlus -> WithEnv WeakTermPlus
internalize isub atsbts (m, y, t) =
  zeta ModeInternalize isub [] atsbts t (m, WeakTermUpsilon y)

internalize' ::
     Mode
  -> SubstWeakTerm
  -> SubstWeakTerm
  -> [IdentifierPlus]
  -> IdentifierPlus
  -> WithEnv WeakTermPlus
internalize' mode isub csub atsbts (m, y, t) =
  zeta mode isub csub atsbts t (m, WeakTermUpsilon y)

externalize ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WeakTermPlus
  -> WithEnv WeakTermPlus
externalize csub atsbts t e = zeta ModeExternalize [] csub atsbts t e

flipMode :: Mode -> Mode
flipMode ModeInternalize = ModeExternalize
flipMode ModeExternalize = ModeInternalize

zeta ::
     Mode
  -> SubstWeakTerm -- out ~> in (substitution {x1 := x1', ..., xn := xn'})
  -> SubstWeakTerm -- in ~> out
  -> [IdentifierPlus] -- ats ++ bts
  -> WeakTermPlus -- a type `A`
  -> WeakTermPlus -- a term `e` of type `A`
  -> WithEnv WeakTermPlus -- a term of type `A{x1 := x1', ..., xn := xn'}`
zeta mode isub csub atsbts t e = do
  ienv <- gets inductiveEnv
  cenv <- gets coinductiveEnv
  case t of
    (_, WeakTermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      let vs = map toVar' xts
      -- backward conversion to create (A', ..., A') -> (A, ..., A)
      vs' <- zipWithM (zeta (flipMode mode) isub csub atsbts) ts vs
      let app = (fst e, WeakTermPiElim e vs')
      -- forward conversion to create B -> B'
      app' <- zeta mode isub csub atsbts cod app
      let ts' = map (substWeakTermPlus undefined) ts
      let xts' = zip3 ms xs ts'
      -- return (A' ..., A') -> (A, ..., A) -> B -> B'
      return $ (fst e, WeakTermPiIntro xts' app')
    (_, WeakTermPiElim va@(ma, WeakTermUpsilon a) es)
      -- ordinary internalization
      | ModeInternalize <- mode
      , Just _ <- lookup a isub -> do
        _ <- undefined isub (concatMap varWeakTermPlus es) -- sanity check
        return (fst e, WeakTermPiElim e (map toVar' atsbts))
      -- nested inductive type
      | ModeInternalize <- mode
      , Just (Just bts) <- Map.lookup a ienv -> do
        let es' = map (substWeakTermPlus undefined) es
        (xts, btsInner) <- lookupInductive a
        let a' = (ma, WeakTermPiIntro xts (ma, WeakTermPiElim va es'))
        args <-
          zipWithM
            (toInternalizedArg mode isub csub xts atsbts es')
            bts
            btsInner
        return (fst e, WeakTermPiElim e (a' : args))
      -- invalid nested inductive type
      | ModeInternalize <- mode
      , Just Nothing <- Map.lookup a ienv ->
        throwError' $
        "mutual inductive type `" <>
        a <> "` cannot be used to construct a nested inductive type"
      -- ordinary externalization
      | ModeExternalize <- mode
      , Just _ <- lookup a csub -> do
        _ <- undefined isub (concatMap varWeakTermPlus es) -- sanity check
        x <- newNameWith "zeta"
        let sigmaType = (fst e, WeakTermSigma (atsbts ++ [(fst t, x, t)]))
        return (fst e, WeakTermSigmaIntro sigmaType (map toVar' atsbts ++ [e]))
      -- nested coinductive type
      | ModeExternalize <- mode
      , Just (Just _) <- Map.lookup a cenv -> undefined
      -- invalid nested coinductive type
      | ModeExternalize <- mode
      , Just Nothing <- Map.lookup a cenv ->
        throwError' $
        "mutual coinductive type `" <>
        a <> "` cannot be used to construct a nested coinductive type"
    (_, WeakTermSigma _) -> undefined
    _ ->
      if undefined isub (varWeakTermPlus t)
        then return e
        else undefined

lookupInductive :: Identifier -> WithEnv ([IdentifierPlus], [IdentifierPlus])
lookupInductive a = do
  fenv <- gets formationEnv
  case Map.lookup a fenv of
    Just (Just (_, WeakTermPiIntro xts (_, WeakTermPi atsbts (_, WeakTermPiElim (_, WeakTermUpsilon _) _)))) -> do
      let bts = tail atsbts -- this is valid since a is not mutual
      return (xts, bts)
    Just (Just _) ->
      throwError' $
      "[compiler bug] malformed inductive type (Parse.lookupInductive)"
    Just Nothing ->
      throwError' $
      "the inductive type `" <> a <> "` must be a non-mutual inductive type"
    Nothing ->
      throwError' $ "[compiler bug] no such inductive type defined: " <> a

toInternalizedArg ::
     Mode
  -> SubstWeakTerm
  -> SubstWeakTerm
  -> [IdentifierPlus]
  -> [IdentifierPlus]
  -> [WeakTermPlus]
  -> IdentifierPlus
  -> IdentifierPlus
  -> WithEnv WeakTermPlus
toInternalizedArg mode isub csub xts atsbts es' b (mbInner, _, (_, WeakTermPi yts _)) = do
  yts' <- mapM (modifyArgs isub xts (undefined, (undefined, es'))) yts
  args <- mapM (internalize' mode isub csub atsbts) yts'
  return (mbInner, WeakTermPiElim (toVar' b) (es' ++ args))
toInternalizedArg _ _ _ _ _ _ _ _ = throwError' "toInternalizedArg"

-- 型アノテーションつきの変数(meta, y, t)をうけとって、tのなかの
--   - 変数をisubに沿ってsubstし、かつ、
--   - a @ (e1, ..., en)をa' @ (e1', ..., en')でsubst
-- したものをt'として、(meta, y, t')を返す。
-- ……たんに、isubとlamとでsubstしたあとでreduceすればいいだけじゃないかしら。
-- a @ (e1, ..., en)をa' @ (e1', ..., en')にしたいときは、a'' = lam (...). a' @ (e1', ..., en')としてreduceすればよいわけで。
-- というか、reduceではなくて、zetaのタイミングで((lam (...). e) e1 ... en)があったらsubstして、みたいにすればいいだけでは。
-- そうすればけっきょくふつうのsubstをすればよいということになるはず。……generalizedだと型が合わないからだめ、みたいなエラーを出力できなくて困るか。
modifyArgs ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> (Identifier, (Identifier, [WeakTermPlus]))
  -> IdentifierPlus
  -> WithEnv IdentifierPlus
modifyArgs _ _ _ _ = undefined
