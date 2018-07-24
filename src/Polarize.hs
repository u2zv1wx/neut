module Polarize where

import           Control.Monad

import           Data

polarize :: Term -> Either String PolTerm
polarize (Var s) = return $ Value $ VVar s
polarize (Const s) = return $ Value $ VConst s
polarize (Lam s e) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Comp $ CLam s c
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (App e1 e2) = do
  mc <- polarize e1
  mv <- polarize e2
  case (mc, mv) of
    (Comp c, Value v) -> return $ Comp $ CApp c v
    _ ->
      Left $ "the polarity of " ++ show e1 ++ " or " ++ show e2 ++ " is wrong"
polarize (ConsApp e1 e2) = do
  mv1 <- polarize e1
  mv2 <- polarize e2
  case (mv1, mv2) of
    (Value v1, Value v2) -> return $ Value $ VConsApp v1 v2
    _ ->
      Left $ "the polarity of " ++ show e1 ++ " or " ++ show e2 ++ " is wrong"
polarize (Ret e) = do
  mv <- polarize e
  case mv of
    Value v -> return $ Comp $ CRet v
    _       -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Bind s e1 e2) = do
  mc1 <- polarize e1
  mc2 <- polarize e2
  case (mc1, mc2) of
    (Comp c1, Comp c2) -> return $ Comp $ CBind s c1 c2
    _ ->
      Left $ "the polarity of " ++ show e1 ++ " or " ++ show e2 ++ " is wrong"
polarize (Thunk e) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Value $ VThunk c
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Unthunk e) = do
  mv <- polarize e
  case mv of
    Value v -> return $ Comp $ CUnthunk v
    _       -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Send s e) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Comp $ CSend s c
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Recv s e) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Comp $ CRecv s c
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Dispatch e1 e2) = do
  mc1 <- polarize e1
  mc2 <- polarize e2
  case (mc1, mc2) of
    (Comp c1, Comp c2) -> return $ Comp $ CDispatch c1 c2
    _ ->
      Left $ "the polarity of " ++ show e1 ++ " or " ++ show e2 ++ " is wrong"
polarize (Coleft e) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Comp $ CColeft c
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Coright e) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Comp $ CCoright c
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Mu s e) = do
  mc <- polarize e
  case mc of
    Comp c -> return $ Comp $ CMu s c
    _      -> Left $ "the polarity of " ++ show e ++ " is wrong"
polarize (Case e ves) = do
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
    Comp c -> return $ Comp $ CCase c ves'
polarize (Asc e t) = do
  polarize e
