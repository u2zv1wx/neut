module Load
  ( load
  ) where

import qualified Control.Monad.Except       as E
import           Control.Monad.Identity
import           Control.Monad.State        hiding (lift)
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data.IORef

import           Asm
import           Data

import           Emit
import           Infer
import           Lift
import           Macro
import           Parse
import           Pattern
import           Polarize
import           Read
import           Rename
import           Virtual

import qualified Text.Show.Pretty           as Pr

load :: String -> WithEnv ()
load s = do
  astList <- strToTree s
  load' astList

load' :: [Tree] -> WithEnv ()
load' [] = return ()
load' ((_ :< TreeNode [_ :< TreeAtom "notation", from, to]):as) = do
  modify (\e -> e {notationEnv = (from, to) : notationEnv e})
  load' as
load' ((_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom s]):as) = do
  modify (\e -> e {reservedEnv = s : reservedEnv e})
  load' as
load' ((_ :< TreeNode ((_ :< TreeAtom "type"):(_ :< TreeAtom s):ts)):as) = do
  args <- mapM parseTypeArg ts
  -- TODO: check polarity, variable binding
  insDefinedTypeEnv s args
  load' as
load' ((_ :< TreeNode [_ :< TreeAtom "value", _ :< TreeAtom x, tp]):as) = do
  t <- parseType tp >>= renameType
  checkType t
  -- TODO: check polarity, variable binding
  t' <- unwrapDown t
  let (tailType, identArgTypes) = forallArgs t'
  let argTypes = map snd identArgTypes
  let resultType = Fix $ TypeStruct $ Fix (TypeInt 32) : argTypes
  let newType = Fix $ TypeDown $ coForallArgs (resultType, identArgTypes)
  insTypeEnv x t
  insValueEnv x newType
  env <- get
  case tailType of
    Fix (TypeNode s _)
      | isDefinedType s env -> do
        insConstructorEnv s x
        load' as
    t ->
      E.lift $
      throwE $
      "the codomain of value type " ++
      show x ++ " must be a user-defined type. Note:\n" ++ Pr.ppShow t
load' (a:as) = do
  e <- macroExpand a >>= parse >>= rename
  let main = "main"
  check main e
  e' <- lift e >>= polarize >>= toComp
  c' <- virtualC e'
  liftIO $ putStrLn $ Pr.ppShow c'
  insCodeEnv main [] c'
  emit
  load' as
