module Parse.Rename
  ( rename
  , nameInModule
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.List                  (intercalate)

import           Data.Basic
import           Data.Env
import           Data.WeakTerm

-- Alpha-convert all the variables so that different variables have different names.
rename :: WeakTerm -> WithEnv WeakTerm
rename (i :< WeakTermUniv j) = return $ i :< WeakTermUniv j
rename (i :< WeakTermUpsilon x) = do
  let x' = normalForm x
  let isAbsolute = '.' `elem` x'
  if isAbsolute
    then do
      x'' <- lookupNameEnv x'
      return $ i :< WeakTermUpsilon x''
    else do
      mx <- nameInModule x' >>= lookupNameEnv''
      case mx of
        Just x'' -> return $ i :< WeakTermUpsilon x''
        Nothing -> do
          penv <- gets prefixEnv
          let candidateList = map (\prefix -> prefix ++ "." ++ x') penv
          my <- lookupNameEnvByList candidateList
          case my of
            Just y  -> return $ i :< WeakTermUpsilon y
            Nothing -> lift $ throwE $ "unbound variable: " ++ x
rename (i :< WeakTermEpsilon s) = return $ i :< WeakTermEpsilon s
rename (i :< WeakTermEpsilonIntro x) = return $ i :< WeakTermEpsilonIntro x
rename (i :< WeakTermEpsilonElim (t, x) e caseList) = do
  e' <- rename e
  t' <- rename t
  local $ do
    x' <- newIdentifierWith x
    caseList' <- renameCaseList caseList
    return $ i :< WeakTermEpsilonElim (t', x') e' caseList'
rename (i :< WeakTermPi s txs) = do
  s' <- rename s
  txs' <- renameBindings txs
  return $ i :< WeakTermPi s' txs'
rename (i :< WeakTermPiIntro s txs e) = do
  s' <- rename s
  (txs', e') <- renameBindingsWithBody txs e
  return $ i :< WeakTermPiIntro s' txs' e'
rename (i :< WeakTermPiElim s e es) = do
  s' <- rename s
  e' <- rename e
  es' <- mapM rename es
  return $ i :< WeakTermPiElim s' e' es'
rename (i :< WeakTermSigma s txs) = do
  s' <- rename s
  txs' <- renameBindings txs
  return $ i :< WeakTermSigma s' txs'
rename (i :< WeakTermSigmaIntro s es) = do
  s' <- rename s
  es' <- mapM rename es
  return $ i :< WeakTermSigmaIntro s' es'
rename (i :< WeakTermSigmaElim s txs e1 e2) = do
  s' <- rename s
  e1' <- rename e1
  (txs', e2') <- renameBindingsWithBody txs e2
  return $ i :< WeakTermSigmaElim s' txs' e1' e2'
rename (i :< WeakTermRec tx e) =
  local $ do
    tx' <- newIdentifierPlusWith tx
    e' <- rename e
    return $ i :< WeakTermRec tx' e'
rename (i :< WeakTermConst x) = return $ i :< WeakTermConst x
rename (i :< WeakTermHole x) = return $ i :< WeakTermHole x

renameBindings :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
renameBindings [] = return []
renameBindings ((t, x):txs) = do
  t' <- rename t
  local $ do
    x' <- newIdentifierWith x
    txs' <- renameBindings txs
    return $ (t', x') : txs'

renameBindingsWithBody ::
     [IdentifierPlus] -> WeakTerm -> WithEnv ([IdentifierPlus], WeakTerm)
renameBindingsWithBody [] e = do
  e' <- rename e
  return ([], e')
renameBindingsWithBody ((t, x):txs) e = do
  t' <- rename t
  local $ do
    x' <- newIdentifierWith x
    (txs', e') <- renameBindingsWithBody txs e
    return ((t', x') : txs', e')

newIdentifierWith :: Identifier -> WithEnv Identifier
newIdentifierWith x = nameInModule x >>= newNameWith

newIdentifierPlusWith :: IdentifierPlus -> WithEnv IdentifierPlus
newIdentifierPlusWith (t, x) = do
  t' <- rename t
  x' <- newIdentifierWith x
  return (t', x')

renameCaseList :: [(Case, WeakTerm)] -> WithEnv [(Case, WeakTerm)]
renameCaseList caseList =
  forM caseList $ \(l, body) ->
    local $ do
      body' <- rename body
      return (l, body')

normalForm :: Identifier -> Identifier
normalForm x = intercalate "." $ filter (/= "") $ wordsWhen (== '.') x

nameInModule :: Identifier -> WithEnv Identifier
nameInModule x = do
  menv <- gets moduleEnv
  return $ intercalate "." $ menv ++ [x]

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =
  case dropWhile p s of
    "" -> []
    s' -> do
      let (w, s'') = break p s'
      w : wordsWhen p s''
