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
rename (m :< WeakTermUniv j) = return $ m :< WeakTermUniv j
rename (m :< WeakTermUpsilon x) = do
  let x' = normalForm x
  let isAbsolute = '.' `elem` x'
  if isAbsolute
    then do
      x'' <- lookupNameEnv x'
      return $ m :< WeakTermUpsilon x''
    else do
      mx <- nameInModule x' >>= lookupNameEnv''
      case mx of
        Just x'' -> return $ m :< WeakTermUpsilon x''
        Nothing -> do
          penv <- gets prefixEnv
          let candidateList = map (\prefix -> prefix ++ "." ++ x') penv
          my <- lookupNameEnvByList candidateList
          case my of
            Just y  -> return $ m :< WeakTermUpsilon y
            Nothing -> lift $ throwE $ "unbound variable: " ++ x
rename (m :< WeakTermEpsilon s) = return $ m :< WeakTermEpsilon s
rename (m :< WeakTermEpsilonIntro x) = return $ m :< WeakTermEpsilonIntro x
rename (m :< WeakTermEpsilonElim (x, t) e caseList) = do
  e' <- rename e
  t' <- rename t
  local $ do
    x' <- newIdentifierWith x
    caseList' <- renameCaseList caseList
    return $ m :< WeakTermEpsilonElim (x', t') e' caseList'
rename (m :< WeakTermPi i xts) = do
  xts' <- renameBindings xts
  return $ m :< WeakTermPi i xts'
rename (m :< WeakTermPiIntro i xts e) = do
  (xts', e') <- renameBindingsWithBody xts e
  return $ m :< WeakTermPiIntro i xts' e'
rename (m :< WeakTermPiElim i e es) = do
  e' <- rename e
  es' <- mapM rename es
  return $ m :< WeakTermPiElim i e' es'
rename (m :< WeakTermSigma i xts) = do
  xts' <- renameBindings xts
  return $ m :< WeakTermSigma i xts'
rename (m :< WeakTermSigmaIntro i es) = do
  es' <- mapM rename es
  return $ m :< WeakTermSigmaIntro i es'
rename (m :< WeakTermSigmaElim i xts e1 e2) = do
  e1' <- rename e1
  (xts', e2') <- renameBindingsWithBody xts e2
  return $ m :< WeakTermSigmaElim i xts' e1' e2'
rename (m :< WeakTermTau i t) = do
  t' <- rename t
  return $ m :< WeakTermTau i t'
rename (m :< WeakTermTauIntro i e) = do
  e' <- rename e
  return $ m :< WeakTermTauIntro i e'
rename (m :< WeakTermTauElim i e) = do
  e' <- rename e
  return $ m :< WeakTermTauElim i e'
rename (m :< WeakTermTheta t) = do
  t' <- rename t
  return $ m :< WeakTermTheta t'
rename (m :< WeakTermThetaIntro e) = do
  e' <- rename e
  return $ m :< WeakTermThetaIntro e'
rename (m :< WeakTermThetaElim e i) = do
  e' <- rename e
  return $ m :< WeakTermThetaElim e' i
rename (m :< WeakTermMu xt e) =
  local $ do
    xt' <- newIdentifierPlusWith xt
    e' <- rename e
    return $ m :< WeakTermMu xt' e'
rename (m :< WeakTermConst x) = return $ m :< WeakTermConst x
rename (m :< WeakTermHole h) = return $ m :< WeakTermHole h

renameBindings :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
renameBindings [] = return []
renameBindings ((x, t):xts) = do
  t' <- rename t
  local $ do
    x' <- newIdentifierWith x
    xts' <- renameBindings xts
    return $ (x', t') : xts'

renameBindingsWithBody ::
     [IdentifierPlus] -> WeakTerm -> WithEnv ([IdentifierPlus], WeakTerm)
renameBindingsWithBody [] e = do
  e' <- rename e
  return ([], e')
renameBindingsWithBody ((x, t):xts) e = do
  t' <- rename t
  local $ do
    x' <- newIdentifierWith x
    (xts', e') <- renameBindingsWithBody xts e
    return ((x', t') : xts', e')

newIdentifierWith :: Identifier -> WithEnv Identifier
newIdentifierWith x = nameInModule x >>= newNameWith

newIdentifierPlusWith :: IdentifierPlus -> WithEnv IdentifierPlus
newIdentifierPlusWith (x, t) = do
  t' <- rename t
  x' <- newIdentifierWith x
  return (x', t')

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
