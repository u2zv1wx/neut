module Polarize where

import           Control.Monad

import           Data

polarize :: MTerm -> Either String PolTerm
polarize (Var s, i) = return $ Value (VVar s, i)
polarize (Const s, i) = return $ Value (VConst s, i)
polarize (Lam s e, i) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Comp (CLam s c, i)
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (App e1 e2, i) = do
  mc <- polarize e1
  mv <- polarize e2
  case (mc, mv) of
    (Comp c, Value v) -> return $ Comp (CApp c v, i)
    _ ->
      Left $ "the polarity of " ++ show e1 ++ " or " ++ show e2 ++ " is wrong"
polarize (Ret e, i) = do
  mv <- polarize e
  case mv of
    Value v -> return $ Comp (CRet v, i)
    _       -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Bind s e1 e2, i) = do
  mc1 <- polarize e1
  mc2 <- polarize e2
  case (mc1, mc2) of
    (Comp c1, Comp c2) -> return $ Comp (CBind s c1 c2, i)
    _ ->
      Left $
      "foo the polarity of " ++ show e1 ++ " or " ++ show e2 ++ " is wrong"
polarize (Thunk e, i) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Value (VThunk c, i)
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Unthunk e, i) = do
  mv <- polarize e
  case mv of
    Value v -> return $ Comp (CUnthunk v, i)
    _       -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Mu s e, i) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Comp (CMu s c, i)
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Case e ves, i) = do
  ves' <-
    forM ves $ \(v, e) -> do
      v' <- polarize v
      e' <- polarize e
      case (v', e') of
        (Value v, Comp c) -> return (v, c)
        _ ->
          Left $ "the polarity of " ++ show v ++ " or " ++ show e ++ " is wrong"
  e' <- polarize e
  case e' of
    Value v -> return $ Comp (CCase v ves', i)
polarize (Asc e t, _) = polarize e
