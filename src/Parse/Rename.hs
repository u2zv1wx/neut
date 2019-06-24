module Parse.Rename
  ( rename
  , renameSortal
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
rename (i :< WeakTermUpsilon (s, x)) = do
  let x' = normalForm x
  s' <- renameSortal s
  let isAbsolute = '.' `elem` x'
  if isAbsolute
    then do
      x'' <- lookupNameEnv x'
      return $ i :< WeakTermUpsilon (s', x'')
    else do
      mx <- nameInModule x' >>= lookupNameEnv''
      case mx of
        Just x'' -> return $ i :< WeakTermUpsilon (s', x'')
        Nothing -> do
          penv <- gets prefixEnv
          let candidateList = map (\prefix -> prefix ++ "." ++ x') penv
          my <- lookupNameEnvByList candidateList
          case my of
            Just y  -> return $ i :< WeakTermUpsilon (s', y)
            Nothing -> lift $ throwE $ "unbound variable: " ++ x
rename (i :< WeakTermEpsilon s) = return $ i :< WeakTermEpsilon s
rename (i :< WeakTermEpsilonIntro x) = return $ i :< WeakTermEpsilonIntro x
rename (i :< WeakTermEpsilonElim (t, u) e caseList) = do
  e' <- rename e
  t' <- rename t
  local $ do
    u' <- newUpsilonWith u
    caseList' <- renameCaseList caseList
    return $ i :< WeakTermEpsilonElim (t', u') e' caseList'
rename (i :< WeakTermPi s tus) = do
  s' <- renameSortal s
  tus' <- renameBindings tus
  return $ i :< WeakTermPi s' tus'
rename (i :< WeakTermPiIntro s tus e) = do
  s' <- renameSortal s
  (tus', e') <- renameBindingsWithBody tus e
  return $ i :< WeakTermPiIntro s' tus' e'
rename (i :< WeakTermPiElim s e es) = do
  s' <- renameSortal s
  e' <- rename e
  es' <- mapM rename es
  return $ i :< WeakTermPiElim s' e' es'
rename (i :< WeakTermSigma s tus) = do
  s' <- renameSortal s
  tus' <- renameBindings tus
  return $ i :< WeakTermSigma s' tus'
rename (i :< WeakTermSigmaIntro s es) = do
  s' <- renameSortal s
  es' <- mapM rename es
  return $ i :< WeakTermSigmaIntro s' es'
rename (i :< WeakTermSigmaElim s tus e1 e2) = do
  s' <- renameSortal s
  e1' <- rename e1
  (tus', e2') <- renameBindingsWithBody tus e2
  return $ i :< WeakTermSigmaElim s' tus' e1' e2'
rename (i :< WeakTermRec ut e) =
  local $ do
    ut' <- newUpsilonPlusWith ut
    e' <- rename e
    return $ i :< WeakTermRec ut' e'
rename (i :< WeakTermConst x) = return $ i :< WeakTermConst x
rename (i :< WeakTermHole x) = return $ i :< WeakTermHole x

renameSortal :: WeakSortal -> WithEnv WeakSortal
renameSortal WeakSortalPrimitive = return WeakSortalPrimitive
renameSortal (WeakSortalTerm e) = do
  e' <- rename e
  return $ WeakSortalTerm e'

renameBindings :: [WeakUpsilonPlus] -> WithEnv [WeakUpsilonPlus]
renameBindings [] = return []
renameBindings ((t, u):tus) = do
  t' <- rename t
  local $ do
    u' <- newUpsilonWith u
    tus' <- renameBindings tus
    return $ (t', u') : tus'

renameBindingsWithBody ::
     [WeakUpsilonPlus] -> WeakTerm -> WithEnv ([WeakUpsilonPlus], WeakTerm)
renameBindingsWithBody [] e = do
  e' <- rename e
  return ([], e')
renameBindingsWithBody ((t, u):tus) e = do
  t' <- rename t
  local $ do
    u' <- newUpsilonWith u
    (tus', e') <- renameBindingsWithBody tus e
    return ((t', u') : tus', e')

newUpsilonWith :: WeakUpsilon -> WithEnv WeakUpsilon
newUpsilonWith (s, x) = do
  s' <- renameSortal s -- `s` must be renamed first
  x'' <- nameInModule x >>= newNameWith
  return (s', x'')

newUpsilonPlusWith :: WeakUpsilonPlus -> WithEnv WeakUpsilonPlus
newUpsilonPlusWith (t, u) = do
  t' <- rename t
  u' <- newUpsilonWith u
  return (t', u')

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
