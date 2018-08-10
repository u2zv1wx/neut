module Pattern
  ( toDecision
  , patDist
  , swap
  ) where

import           Control.Comonad.Cofree

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data
import           Data.List                  (nub, transpose)

import           Debug.Trace

import qualified Text.Show.Pretty           as Pr

type ClauseMatrix a = ([[Pat]], [a])

-- Muranget, "Compiling Pattern Matching to Good Decision Trees", 2008
toDecision :: (Show a) => [Occurrence] -> ClauseMatrix a -> WithEnv (Decision a)
toDecision _ ([], _) = return $ DecisionFail
toDecision _ (_, []) = return $ DecisionFail
toDecision os (patMat, bodyList)
  | Nothing <- findPatApp patMat = return $ DecisionLeaf (head bodyList)
  | Just i <- findPatApp patMat
  , i /= 0 = do
    let patMat' = swapColumn 0 i patMat
    let os' = swapColumn 0 i os
    DecisionSwap i <$> toDecision os' (patMat', bodyList)
  | Just _ <- findPatApp patMat = do
    consList <- headConstructor patMat
    let consList' = nub consList
    newMatrixList <-
      forM consList' $ \(c, a) -> do
        let os' = (map (\j -> head os ++ [j]) [1 .. a]) ++ tail os
        tmp <- toDecision os' $ specialize c a (patMat, bodyList)
        return (c, tmp)
    cenv <- getCEnv patMat
    if length cenv <= length consList
      then return $ DecisionSwitch (head os) $ newMatrixList
      else do
        let dmat = defaultMatrix (patMat, bodyList)
        dmat' <- toDecision (tail os) dmat
        return $
          DecisionSwitch (head os) $ newMatrixList ++ [("default", dmat')]
  | otherwise = undefined

patDist :: [([Pat], a)] -> ([[Pat]], [a])
patDist [] = ([], [])
patDist ((ps, body):rest) = do
  let (pss, bodyList) = patDist rest
  (ps : pss, body : bodyList)

type Arity = Int

getCEnv :: [[Pat]] -> WithEnv [Identifier]
getCEnv [] = lift $ throwE "empty pattern"
getCEnv ([]:_) = lift $ throwE "empty pattern"
getCEnv (((Meta {ident = i} :< _):_):_) = do
  t <- lookupWTEnv i
  case t of
    Just (WeakTypeNode s _) -> lookupConstructorEnv s
    _                       -> undefined

headConstructor :: [[Pat]] -> WithEnv [(Identifier, Arity)]
headConstructor ([]) = return []
headConstructor (ps:pss) = do
  ps' <- headConstructor' ps
  pss' <- mapM headConstructor' pss
  return $ join $ ps' : pss'

headConstructor' :: [Pat] -> WithEnv [(Identifier, Arity)]
headConstructor' [] = return []
headConstructor' ((Meta {ident = i} :< PatVar _):_) = do
  wt <- lookupWTEnv i
  liftIO $ putStrLn $ "type: " ++ Pr.ppShow wt
  return []
headConstructor' ((Meta {ident = i} :< PatApp s args):_) = do
  wt <- lookupWTEnv i
  liftIO $ putStrLn $ "type: " ++ Pr.ppShow wt
  return [(s, length args)]

findPatApp :: [[Pat]] -> Maybe Int
findPatApp [] = Nothing
findPatApp (ps:pss) =
  case findPatApp' $ zip ps [0 ..] of
    Nothing -> findPatApp pss
    Just i  -> Just i

findPatApp' :: [(Pat, Int)] -> Maybe Int
findPatApp' []                       = Nothing
findPatApp' ((_ :< PatVar _, _):ps)  = findPatApp' ps
findPatApp' ((_ :< PatApp _ _, i):_) = Just i

specialize :: Identifier -> Arity -> ClauseMatrix a -> ClauseMatrix a
specialize c a (pss, bs) = do
  let pss' = join $ map (\(ps, b) -> specializeRow c a ps b) $ zip pss bs
  patDist pss'

specializeRow :: Identifier -> Arity -> [Pat] -> a -> [([Pat], a)]
specializeRow _ _ [] _ = []
specializeRow _ a ((i :< PatVar _):ps) body = do
  let newNames = map (const (i :< PatVar "_")) [1 .. a]
  [(newNames ++ ps, body)]
specializeRow c _ ((_ :< PatApp s args):ps) body = do
  if c /= s
    then []
    else [(args ++ ps, body)]

defaultMatrix :: ClauseMatrix a -> ClauseMatrix a
defaultMatrix (pss, bs) = do
  let pss' = join $ map (\(ps, b) -> defaultMatrixRow ps b) $ zip pss bs
  patDist pss'

defaultMatrixRow :: [Pat] -> a -> [([Pat], a)]
defaultMatrixRow [] _                      = []
defaultMatrixRow ((_ :< PatVar _):ps) body = [(ps, body)]
defaultMatrixRow ((_ :< PatApp _ _):_) _   = []

swapColumn :: Int -> Int -> [[a]] -> [[a]]
swapColumn i j mat = transpose $ swap i j $ transpose mat

swap :: Int -> Int -> [a] -> [a]
swap i j xs = do
  replaceNth j (xs !! i) (replaceNth i (xs !! j) xs)

replaceNth :: Int -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth n newVal (x:xs)
  | n == 0 = newVal : xs
  | otherwise = x : replaceNth (n - 1) newVal xs
