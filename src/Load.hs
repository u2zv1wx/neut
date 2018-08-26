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
  t <- parseType tp
  -- TODO: check polarity, variable binding
  let (tailType, _) = forallArgs t
  env <- get
  case tailType of
    Fix (TypeNode s _)
      | isDefinedType s env -> do
        insTypeEnv x t
        insValueEnv x t
        insConstructorEnv s x
        load' as
    _ ->
      E.lift $
      throwE $
      "the codomain of value type " ++ show x ++ " must be a user-defined type"
load' (a:as) = do
  e <- macroExpand a >>= parse >>= rename >>= lift
  liftIO $ putStrLn $ Pr.ppShow e
  let main = "main"
  check main e
  -- polarizeTypeEnv wtenv
  e' <- polarize e >>= toComp
  c' <- virtualC e'
  insCodeEnv main [] c'
  -- asm <- asmCode c'
  emit
  load' as
