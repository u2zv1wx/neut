module Pattern
  ( toDecision
  , patDist
  ) where

import           Control.Comonad.Cofree

import           Control.Monad

import           Data

type ClauseMatrix a = ([[Pat]], [a])

-- Muranget, "Compiling Pattern Matching to Good Decision Trees", 2008
toDecision :: [Occurrence] -> ClauseMatrix a -> Decision a
toDecision _ ([], _) = DecisionFail
toDecision [] _ = DecisionFail
toDecision _ (_, []) = DecisionFail
toDecision (o:os) (patMat@(p:_), bodyVec@(body:_)) = do
  case findPatApp p of
    Nothing -> DecisionLeaf body
    Just (_, i) -> do
      if i /= 1
        then do
          let matrix' = swap 1 i patMat
          let os' = swap 1 i (o : os)
          let newMat = toDecision os' (matrix', bodyVec)
          DecisionSwap i newMat
        else do
          let sigmaOne = headConstructor (patMat, bodyVec)
          let foo c a = do
                let newOccurences = (map (\i -> o ++ [i]) [1 .. a]) ++ os
                (c, toDecision newOccurences (specialize c (patMat, bodyVec)))
          let newMatrixList = map (uncurry foo) sigmaOne
          let defaultCase =
                ("_", toDecision os (defaultMatrix (patMat, bodyVec)))
          DecisionSwitch o $ newMatrixList ++ [defaultCase]

patDist :: [([Pat], a)] -> ([[Pat]], [a])
patDist [] = ([], [])
patDist ((ps, body):rest) = do
  let (pss, bodyList) = patDist rest
  (ps : pss, body : bodyList)

type Arity = Int

headConstructor :: ClauseMatrix a -> [(Identifier, Arity)]
headConstructor ([], _) = []
headConstructor ([]:rest, bodyList) = headConstructor (rest, bodyList)
headConstructor (((_ :< PatVar _):_):rest, bodyList) =
  headConstructor (rest, bodyList)
headConstructor (((_ :< PatApp s args):_):rest, bodyList) =
  (s, length args) : headConstructor (rest, bodyList)

findPatApp :: [Pat] -> Maybe (Pat, Int)
findPatApp ps = findPatApp' $ zip ps [1 ..]

findPatApp' :: [(Pat, Int)] -> Maybe (Pat, Int)
findPatApp' []                         = Nothing
findPatApp' ((_ :< PatVar _, _):ps)    = findPatApp' ps
findPatApp' (p@(_ :< PatApp _ _, _):_) = Just p

specialize :: Identifier -> ClauseMatrix a -> ClauseMatrix a
specialize = undefined

defaultMatrix :: ClauseMatrix a -> ClauseMatrix a
defaultMatrix = undefined

swap :: Int -> Int -> [a] -> [a]
swap f s xs = zipWith (swap' f s xs) [0 ..] xs

swap' :: Int -> Int -> [a] -> Int -> a -> a
swap' f s xs x y =
  if x == f
    then xs !! s
    else if x == s
           then xs !! f
           else y
