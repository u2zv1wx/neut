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
toDecision _ ([], _) = lift $ throwE $ "non-exclusive pattern"
toDecision _ (_, []) = lift $ throwE $ "non-exclusive pattern"
toDecision os (patMat, bodyList)
  | Nothing <- findPatApp patMat = do
    liftIO $ putStrLn $ "found Leaf. the patMat is:\n" ++ Pr.ppShow patMat
    liftIO $ putStrLn $ "and the occurrence vector is:\n" ++ Pr.ppShow os
    vs <- collectVar patMat
    return $ DecisionLeaf (zip os vs) (head bodyList)
  | Just i <- findPatApp patMat
  , i /= 0 = do
    let patMat' = swapColumn 0 i patMat
    let ts = map snd os
    let occurrenceList = map fst os
    let occurrenceList' = swapColumn 0 i occurrenceList
    let os' = zip occurrenceList' ts
    DecisionSwap i <$> toDecision os' (patMat', bodyList)
  | otherwise = do
    consList <- nub <$> headConstructor patMat
    newMatrixList <-
      forM consList $ \(c, args) -> do
        let a = length args
        let os' =
              (map (\j -> (fst (head os) ++ [j], args !! (j - 1))) [1 .. a]) ++
              tail os
        tmp <- specialize c a (patMat, bodyList)
        tmp' <- toDecision os' tmp
        return (c, tmp')
    cenv <- getCEnv patMat
    if length cenv <= length consList
      then return $ DecisionSwitch (head os) newMatrixList Nothing
      else do
        (tmp, bounds) <- defaultMatrix (patMat, bodyList)
        dmat <- toDecision (tail os) $ tmp
        return $ DecisionSwitch (head os) newMatrixList (Just (bounds, dmat))

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
    _                       -> lift $ throwE "type error in pattern"

headConstructor :: [[Pat]] -> WithEnv [(Identifier, [ValueType])]
headConstructor ([]) = return []
headConstructor (ps:pss) = do
  ps' <- headConstructor' ps
  pss' <- mapM headConstructor' pss
  return $ join $ ps' : pss'

headConstructor' :: [Pat] -> WithEnv [(Identifier, [ValueType])]
headConstructor' [] = return []
headConstructor' ((_ :< PatHole):_) = return []
headConstructor' ((_ :< PatVar _):_) = return []
headConstructor' ((_ :< PatApp s _):_) = do
  (_, args, cod) <- lookupVEnv' s
  return [(s, map snd args)]
  -- case vt of
  --   ValueTypeNode _ vts -> return [(s, vts)]
  -- return [(s, length args)]

collectVar :: [[Pat]] -> WithEnv [(Identifier, ValueType)]
collectVar [] = return []
collectVar (ps:pss) = do
  vs1 <- collectVar' ps
  vs2 <- collectVar pss
  return $ vs1 ++ vs2

collectVar' :: [Pat] -> WithEnv [(Identifier, ValueType)]
collectVar' [] = return []
collectVar' ((Meta {ident = i} :< PatVar s):ps) = do
  vt <- lookupValueTypeEnv' i
  tmp <- collectVar' ps
  return $ (s, vt) : tmp
collectVar' (_:ps) = collectVar' ps

findPatApp :: [[Pat]] -> Maybe Int
findPatApp [] = Nothing
findPatApp (ps:pss) =
  case findPatApp' $ zip ps [0 ..] of
    Nothing -> findPatApp pss
    Just i  -> Just i

findPatApp' :: [(Pat, Int)] -> Maybe Int
findPatApp' []                       = Nothing
findPatApp' ((_ :< PatHole, _):ps)   = findPatApp' ps
findPatApp' ((_ :< PatVar _, _):ps)  = findPatApp' ps
findPatApp' ((_ :< PatApp _ _, i):_) = Just i

specialize :: Identifier -> Arity -> ClauseMatrix a -> WithEnv (ClauseMatrix a)
specialize c a (pss, bs) = do
  pss' <- mapM (\(ps, b) -> specializeRow c a ps b) $ zip pss bs
  return $ patDist $ join pss'

specializeRow :: Identifier -> Arity -> [Pat] -> a -> WithEnv [([Pat], a)]
specializeRow _ _ [] _ = return []
specializeRow _ a ((i :< PatHole):ps) body = do
  newNames <- forM [1 .. a] $ const $ return $ i :< PatHole
  return [(newNames ++ ps, body)]
specializeRow c a ((i :< PatVar _):ps) body = do
  specializeRow c a ((i :< PatHole) : ps) body
specializeRow c _ ((_ :< PatApp s args):ps) body = do
  if c /= s
    then return []
    else return [(args ++ ps, body)]

defaultMatrix :: ClauseMatrix a -> WithEnv ((ClauseMatrix a), Maybe Identifier)
defaultMatrix (pss, bs) = do
  pss' <- mapM (\(ps, b) -> defaultMatrixRow ps b) $ zip pss bs
  let pss'' = map fst pss'
  let bounds = takeHeadJust $ map snd pss'
  return (patDist $ join pss'', bounds)

takeHeadJust :: [Maybe a] -> Maybe a
takeHeadJust []             = Nothing
takeHeadJust (Nothing:rest) = takeHeadJust rest
takeHeadJust (Just x:_)     = Just x

defaultMatrixRow :: [Pat] -> a -> WithEnv ([([Pat], a)], Maybe Identifier)
defaultMatrixRow [] _ = return ([], Nothing)
defaultMatrixRow ((_ :< PatHole):ps) body = do
  return ([(ps, body)], Nothing)
defaultMatrixRow ((_ :< PatVar s):ps) body = do
  return ([(ps, body)], Just s)
defaultMatrixRow ((_ :< PatApp _ _):_) _ = return ([], Nothing)

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
