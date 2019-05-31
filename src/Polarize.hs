-- This module "polarizes" a neutral term to a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value calculus. The basics of Call-By-Push-Value can be found in
-- P. Levy. "Call-by-Push-Value: A Subsuming Paradigm". Ph. D. thesis, Queen
-- Mary College, 2001. In the thesis, Levy gives a translation from a call-by-value
-- calculus to a call-by-push-value calculus. Our translation is a dependent
-- extension of the translation. The crucial point in our translation would be that,
-- in dependent setting, the distinction between the type constructor `↑(-)`
-- and the term constructor `return (-)` seems to disappear. Indeed, in this
-- translation, we only use `NegUpIntro` (the term-level construct), and
-- not `NegUp` (the type-level construct).
module Polarize
  ( polarize
  ) where

import Control.Monad

import Control.Comonad.Cofree

import Control.Monad.State
import Control.Monad.Trans.Except

import qualified Text.Show.Pretty as Pr

import Data
import Reduce
import Util

import Text.Read (readMaybe)

import Data.Maybe (isJust, maybeToList)

polarize :: WithEnv ()
polarize = do
  tenv <- gets termEnv
  forM_ tenv $ \(name, e) -> do
    e' <- polarize' e
    insPolEnv name e'
  -- penv <- gets polEnv
  -- forM_ penv $ \(name, e) -> do
  --   liftIO $ putStrLn name
  --   liftIO $ putStrLn $ Pr.ppShow e
  --   liftIO $ putStrLn "-----------------------------"

polarize' :: Term -> WithEnv Neg
polarize' (TermVar x) = return $ NegDownElim (PosVar x)
polarize' (TermConst x) = do
  insertDefinition x
  return $ NegDownElim (PosVar x)
polarize' (TermPiIntro x e) = do
  e' <- polarize' e
  return $ NegPiIntro x e'
polarize' (TermPiElim e1 e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2
  return $ NegPiElim e1' (PosDownIntro e2')
polarize' (TermSigmaIntro es) = do
  es' <- mapM polarize' es
  return $ NegUpIntro $ PosSigmaIntro (map PosDownIntro es')
polarize' (TermSigmaElim e1 xs e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2
  z <- newNameWith "sigma"
  return $ NegUpElim z e1' (NegSigmaElim (PosVar z) xs e2')
polarize' (TermIndexIntro l meta) = return $ NegUpIntro (PosIndexIntro l meta)
polarize' (TermIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  e' <- polarize' e
  x <- newNameWith "tmp"
  cs <- mapM polarize' es
  return $ NegUpElim x e' (NegIndexElim (PosVar x) (zip labelList cs))
polarize' (TermMu x e) = do
  e' <- polarize' e
  return $ NegMu x e'

-- insert (possibly) environment-specific definition of constant
insertDefinition :: Identifier -> WithEnv ()
insertDefinition x
  | isPrintConstant x = insertPrintDefinition x
  | isArithBinOpConstant x = insertArithBinOp x
  | otherwise = lift $ throwE $ "No such primitive: " ++ x

isPrintConstant :: Identifier -> Bool
isPrintConstant x = do
  let xs = wordsWhen (== '.') x
  length xs == 3 &&
    head xs == "core" && isArithType (xs !! 1) && xs !! 2 == "print"

insertPrintDefinition :: Identifier -> WithEnv ()
insertPrintDefinition op = do
  x <- newNameWith "lam"
  x' <- newNameWith "lam"
  penv <- gets polEnv
  let internalOp = "internal." ++ op -- FIXME: this should be environment-specific
  -- when (op `notElem` map fst penv) $
  --   insPolEnv op $
  --   NegPiIntro x $
  --   NegUpElim x' (NegDownElim (PosVar x)) $
  --   NegPiElim (NegDownElim (PosConst internalOp)) (PosVar x')
  when (op `notElem` map fst penv) $
    insPolEnv op $
    NegPiIntro x $
    NegUpElim x' (NegDownElim (PosVar x)) $ NegConstElim internalOp [PosVar x']
    -- NegPi (NegDownElim (PosConst internalOp)) (PosVar x')

isArithBinOpConstant :: Identifier -> Bool
isArithBinOpConstant x = do
  let xs = wordsWhen (== '.') x
  length xs == 3 &&
    head xs == "core" && isArithType (xs !! 1) && isArithBinOp (xs !! 2)

isArithBinOp :: Identifier -> Bool
isArithBinOp "add" = True
isArithBinOp "sub" = True
isArithBinOp "mul" = True
isArithBinOp "div" = True
isArithBinOp _ = False

isArithType :: Identifier -> Bool
isArithType x
  | not (null x)
  , Just y <- readMaybe $ tail x
  , y > 0 = head x == 'i' || head x == 'u' || head x == 'f'
  | otherwise = False

insertArithBinOp :: Identifier -> WithEnv ()
insertArithBinOp op = do
  x <- newNameWith "lam"
  x' <- newNameWith "lam"
  y <- newNameWith "lam"
  y' <- newNameWith "lam"
  penv <- gets polEnv
  let llvmop = "llvm." ++ op
  when (op `notElem` map fst penv) $
    insPolEnv op $
    NegPiIntro x $
    NegPiIntro y $
    NegUpElim x' (NegDownElim (PosVar x)) $
    NegUpElim y' (NegDownElim (PosVar y)) $
    NegConstElim llvmop [PosVar x', PosVar y']
  -- when (op `notElem` map fst penv) $
  --   insPolEnv op $
  --   NegPiIntro x $
  --   NegPiIntro y $
  --   NegUpElim x' (NegDownElim (PosVar x)) $
  --   NegUpElim y' (NegDownElim (PosVar y)) $
  --   NegPiElim
  --     (NegPiElim (NegDownElim (PosConst llvmop)) (PosVar x'))
  --     (PosVar y')

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =
  case dropWhile p s of
    "" -> []
    s' -> w : wordsWhen p s''
      where (w, s'') = break p s'
