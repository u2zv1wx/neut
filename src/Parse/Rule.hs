{-# LANGUAGE OverloadedStrings #-}

module Parse.Rule where

import Control.Monad.Except
import Control.Monad.State
import Data.Monoid ((<>))
import Data.Tuple (swap)

import qualified Data.HashMap.Strict as Map

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm
import Parse.Interpret

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

toVar'' :: IdentifierPlus -> (WeakTermPlus, WeakTermPlus)
toVar'' (m, x, t) = ((m, WeakTermUpsilon x), t)

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

-- toInductiveIntro ats bts xts (mb, b, m, yts, cod) = do
--   return $
--     StmtLet
--       m
--       (mb, b, (m, WeakTermPi (xts ++ yts) cod)) -- e.g. cons : Pi (A : tau, w : A, ws : list A). list A,
--                                                 -- where b = cons, xts = [A : tau], yts = [w : A, ws : list A], cod = list A
--       ( m
--       , WeakTermPiIntro
--           (xts ++ yts)
--           -- list A = (lam (A : Tau). Pi (list : (...), nil : (...), cons : (...)). list A) @ A
--           --        = Pi (list : (...), nil : (...), cons : (...)). list A
--           ( m
--           , WeakTermPiIntro
--               (ats ++ bts) -- ats = [list : (...)],
--                            -- bts = [nil : Pi (yts). list A, cons : (...)]
--               (m, WeakTermPiElim (mb, WeakTermUpsilon b) (map toVar' yts)) -- nil @ yts : list A
--                                                                            -- (note that the `nil` here doesn't have xts as arguments)
--            ))
-- concatStmtList (StmtCoinductive {}:_) = undefined
-- toCoinductiveElim ats bts xts (m, (mb, b), yts, cod)
--   | length yts > 0 = do
--     return $
--       StmtLet
--         m
--         (mb, b, (m, WeakTermPi (xts ++ yts) cod)) -- tail : Pi (A : tau, s : stream A). stream A
--         ( m
--         , WeakTermPiIntro
--             (xts ++ yts)
--             -- stream A = (lam (A : Tau). Sigma (stream : (...), head : (...), tail : (...)). stream A) @ A
--             --          = Sigma (list : (...), head : (...), tail : (...)). stream A
--             -- ats = [list : (...)]
--             -- bts = [head : (...), tail : Pi (y1 : stream A). stream A]
--             -- (head yts : stream A)
--             -- ~> ats ++ bts ++ [head yts] = [list : (...), head : (...), tail : Pi (y1 : stream A). stream A, y1 : stream A]
--             ( m
--             , WeakTermSigmaElim
--                 cod -- sigmaElimの型の部分はelimの結果の型。変数（yts）を同一名の変数（yts）でsubstするので依存の処理の心配もなし。
--                 -- 同一の変数名を使うのがポイント。head yts : a @ (e1, ..., en)なので、
--                 -- (1)のほうのhead ytsの型に出現するaは(1)の行のatsによって束縛されたものとなり、
--                 -- (2)のほうのhead ytsの方に出現するaは外側のtoCoinductiveの結果によって定義されたものとなる。
--                 -- 別に異なる名前を両者に与えてもよいが、同一の名前を使ったほうが実装がラクなのでこちらをとることにする。
--                 (ats ++ bts ++ [head yts]) -- (1)
--                 (toVar' $ head yts) -- (2)
--                 (m, WeakTermPiElim (mb, WeakTermUpsilon b) (map toVar' yts))))
--   | otherwise =
--     throwError'
--       "toCoinductiveElim: the antecedant of an elimination rule cannot be empty"
data Mode
  = ModeInternalize
  | ModeExternalize

flipMode :: Mode -> Mode
flipMode ModeInternalize = ModeExternalize
flipMode ModeExternalize = ModeInternalize

psi ::
     Mode
  -> [(Identifier, Identifier)] -- out ~> in (substitution {x1 := x1', ..., xn := xn'})
  -> [(Identifier, Identifier)] -- in ~> out
  -> [IdentifierPlus] -- ats ++ bts
  -> WeakTermPlus -- a type `A`
  -> WeakTermPlus -- a term `e` of type `A`
  -> WithEnv WeakTermPlus -- a term of type `A{x1 := x1', ..., xn := xn'}`
psi m isub csub atsbts t e = do
  ienv <- gets inductiveEnv
  cenv <- gets coinductiveEnv
  case t of
    (_, WeakTermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      let vs = map toVar' xts
      let isub' = map swap isub
      let csub' = map swap csub
      -- backward conversion to create (A', ..., A') -> (A, ..., A)
      vs' <- zipWithM (psi (flipMode m) isub' csub' atsbts) ts vs
      let app = (fst e, WeakTermPiElim e vs')
      -- forward conversion to create B -> B'
      app' <- psi m isub csub atsbts cod app
      let ts' = map (substWeakTermPlus undefined) ts
      let xts' = zip3 ms xs ts'
      -- return (A' ..., A') -> (A, ..., A) -> B -> B'
      return $ (fst e, WeakTermPiIntro xts' app')
    (_, WeakTermPiElim va@(ma, WeakTermUpsilon a) es)
      -- ordinary internalization
      | Just _ <- lookup a isub -> do
        _ <- undefined isub (concatMap varWeakTermPlus es) -- sanity check
        return (fst e, WeakTermPiElim e (map toVar' atsbts))
      -- nested inductive type
      | Just (Just bts) <- Map.lookup a ienv -> do
        let es' = map (substWeakTermPlus undefined) es
        (xts, btsInner) <- lookupInductive a
        a' <- newNameWith "psi"
        let a' = (ma, WeakTermPiIntro xts (ma, WeakTermPiElim va es'))
        args <-
          zipWithM (toInternalizedArg m isub csub xts atsbts es') bts btsInner
        return (fst e, WeakTermPiElim e (a' : args))
      -- invalid nested inductive type
      | Just Nothing <- Map.lookup a ienv ->
        throwError' $
        "mutual inductive type `" <>
        a <> "` cannot be used to construct a nested inductive type"
      -- ordinary externalization
      | Just _ <- lookup a csub -> do
        _ <- undefined isub (concatMap varWeakTermPlus es) -- sanity check
        x <- newNameWith "psi"
        let sigmaType = (fst e, WeakTermSigma (atsbts ++ [(fst t, x, t)]))
        return (fst e, WeakTermSigmaIntro sigmaType (map toVar' atsbts ++ [e]))
      -- nested coinductive type
      | Just (Just _) <- Map.lookup a cenv -> undefined
      -- invalid nested coinductive type
      | Just Nothing <- Map.lookup a cenv ->
        throwError' $
        "mutual coinductive type `" <>
        a <> "` cannot be used to construct a nested coinductive type"
    (_, WeakTermPiElim (_, WeakTermPiIntro {}) _) -> undefined
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
  -> [(Identifier, Identifier)]
  -> [(Identifier, Identifier)]
  -> [IdentifierPlus]
  -> [IdentifierPlus]
  -> [WeakTermPlus]
  -> IdentifierPlus
  -> IdentifierPlus
  -> WithEnv WeakTermPlus
toInternalizedArg mode isub csub xts atsbts es' b (mbInner, _, (_, WeakTermPi yts _)) = do
  yts' <- mapM (modifyArgs isub xts (undefined, (undefined, es'))) yts
  args <- mapM (internalize mode isub csub atsbts) yts'
  return (mbInner, WeakTermPiElim (toVar' b) (es' ++ args))
toInternalizedArg _ _ _ _ _ _ _ _ = throwError' "toInternalizedArg"

-- 型アノテーションつきの変数(meta, y, t)をうけとって、tのなかの
--   - 変数をisubに沿ってsubstし、かつ、
--   - a @ (e1, ..., en)をa' @ (e1', ..., en')でsubst
-- したものをt'として、(meta, y, t')を返す。
-- ……たんに、isubとlamとでsubstしたあとでreduceすればいいだけじゃないかしら。
-- a @ (e1, ..., en)をa' @ (e1', ..., en')にしたいときは、a'' = lam (...). a' @ (e1', ..., en')としてreduceすればよいわけで。
-- というか、reduceではなくて、psiのタイミングで((lam (...). e) e1 ... en)があったらsubstして、みたいにすればいいだけでは。
-- そうすればけっきょくふつうのsubstをすればよいということになるはず。……generalizedだと型が合わないからだめ、みたいなエラーを出力できなくて困るか。
modifyArgs ::
     [(Identifier, Identifier)]
  -> [IdentifierPlus]
  -> (Identifier, (Identifier, [WeakTermPlus]))
  -> IdentifierPlus
  -> WithEnv IdentifierPlus
modifyArgs isub xts (a, (a', es')) (m, y, t) = do
  undefined

internalize ::
     Mode
  -> [(Identifier, Identifier)]
  -> [(Identifier, Identifier)]
  -> [IdentifierPlus]
  -> IdentifierPlus
  -> WithEnv WeakTermPlus
internalize mode isub csub atsbts (m, y, t) =
  psi mode isub csub atsbts t (m, WeakTermUpsilon y)
