{-# LANGUAGE OverloadedStrings #-}

module Check
  ( check
  ) where

import Control.Monad.State
import Data.List (find)
import Data.Time
import Numeric

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Env
import Data.Term
import Data.WeakTerm
import Elaborate
import Reduce.Term

check :: WeakStmt -> WithEnv ()
check (WeakStmtReturn e) = do
  (e', _) <- infer e
  analyze >> synthesize
  void $ elaborate e'
check (WeakStmtLet _ (_, x, t) e cont) = do
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  check' x e' t' cont
check (WeakStmtLetWT _ (_, x, t) e cont) = do
  t' <- inferType t
  check' x e t' cont
check (WeakStmtVerify m e cont) = do
  (e', _) <- infer e
  e'' <- elaborate e'
  start <- liftIO $ getCurrentTime
  _ <- normalize e''
  stop <- liftIO $ getCurrentTime
  let sec = showFloat' (realToFrac $ diffUTCTime stop start :: Float)
  note m $ "verification succeeded (" <> T.pack sec <> " seconds)"
  check cont
check (WeakStmtImplicit m x idxList cont) = do
  t <- lookupTypeEnv m (Right x) x
  case t of
    (_, TermPi _ xts _) -> do
      case find (\idx -> idx < 0 || length xts <= idx) idxList of
        Nothing -> do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = Map.insertWith (++) x idxList ienv})
          check cont
        Just idx -> do
          raiseError m $
            "the specified index `" <>
            T.pack (show idx) <> "` is out of range of the domain of " <> x
    _ ->
      raiseError m $
      "the type of " <>
      x <> " must be a Pi-type, but is:\n" <> toText (weaken t)
check (WeakStmtConstDecl _ (_, x, t) cont) = do
  t' <- inferType t
  analyze >> synthesize >> cleanup
  t'' <- reduceTermPlus <$> elaborate t'
  insTypeEnv (Right x) t''
  check cont

check' :: T.Text -> WeakTermPlus -> WeakTermPlus -> WeakStmt -> WithEnv ()
check' x e t cont = do
  analyze >> synthesize >> cleanup
  e' <- elaborate e
  t' <- elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  check cont

cleanup :: WithEnv ()
cleanup = do
  modify (\env -> env {constraintEnv = []})
  modify (\env -> env {weakTypeEnv = IntMap.empty})
  modify (\env -> env {zetaEnv = IntMap.empty})

showFloat' :: Float -> String
showFloat' x = showFFloat Nothing x ""
