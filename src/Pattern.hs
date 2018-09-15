module Pattern
  ( toDecision
  , decision
  , patDist
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

decision :: Term -> WithEnv Term
decision (i :< TermVar s) = return $ i :< TermVar s
decision (i :< TermConst s) = return $ i :< TermConst s
decision (i :< TermLam s e) = do
  c <- decision e
  return $ i :< TermLam s c
decision (i :< TermApp e1 e2) = do
  c <- decision e1
  v <- decision e2
  return $ i :< TermApp c v
decision (i :< TermPair v1 v2) = do
  v1' <- decision v1
  v2' <- decision v2
  return $ i :< TermPair v1' v2'
decision (i :< TermMu s e) = do
  c <- decision e
  return $ i :< TermMu s c
decision (i :< TermCase vs ves) = do
  ves' <- decisionClause ves
  vs' <- mapM decision vs
  let vesMod = patDist ves'
  let indexList = map (const []) vs
  let metaList = map (\(meta :< _) -> meta) vs
  typeList <- mapM lookupTypeEnv' metaList
  let initialOccurences = zip indexList typeList
  decisionTree <- toDecision initialOccurences vesMod
  return $ i :< TermDecision vs' decisionTree
decision (_ :< TermDecision _ _) = error "Decision"

decisionClause :: [([Pat], Term)] -> WithEnv [([Pat], Term)]
decisionClause [] = return []
decisionClause ((patList, e):ves) = do
  e' <- decision e
  ves' <- decisionClause ves
  return $ (patList, e') : ves'

-- Muranget, "Compiling Pattern Matching to Good Decision Trees", 2008
toDecision :: (Show a) => [Occurrence] -> ClauseMatrix a -> WithEnv (Decision a)
toDecision _ ([], _) = lift $ throwE "non-exclusive pattern"
toDecision _ (_, []) = lift $ throwE "non-exclusive pattern"
toDecision os (patMat, bodyList)
  | Nothing <- findPatApp patMat = do
    vs <- collectVar patMat
    return $ DecisionLeaf (zip os vs) (head bodyList)
  | Just i <- findPatApp patMat
  , i /= 0 = do
    let patMat' = swapColumn 0 i patMat
    let (is, typeList) = unzip os
    let is' = swapColumn 0 i is
    let os' = zip is' typeList
    DecisionSwap i <$> toDecision os' (patMat', bodyList)
  | otherwise = do
    consList <- headConstructor patMat
    newMatrixList <-
      forM consList $ \(c, num, args) -> do
        let a = length args
        let os' =
              map (\j -> (fst (head os) ++ [j], args !! j)) [0 .. (a - 1)] ++
              tail os
        tmp <- specialize c a (patMat, bodyList)
        tmp' <- toDecision os' tmp
        return ((c, num), tmp')
    return $ DecisionSwitch (head os) newMatrixList Nothing
    -- consCount <- getCEnv patMat
    -- if consCount <= length consList
    --   then return $ DecisionSwitch (head os) newMatrixList Nothing
    --   else do
    --     (tmp, bounds) <- defaultMatrix (patMat, bodyList)
    --     dmat <- toDecision (tail os) tmp
    --     return $ DecisionSwitch (head os) newMatrixList (Just (bounds, dmat))

patDist :: [([Pat], a)] -> ([[Pat]], [a])
patDist [] = ([], [])
patDist ((ps, body):rest) = do
  let (pss, bodyList) = patDist rest
  (ps : pss, body : bodyList)

type Arity = Int

-- getCEnv :: [[Pat]] -> WithEnv Int
-- getCEnv [] = lift $ throwE "empty pattern"
-- getCEnv ([]:_) = lift $ throwE "empty pattern"
-- getCEnv (((i :< _):_):_) = do
--   t <- lookupTypeEnv i
--   case t of
--     Just (Fix (TypeSum labelList)) -> return $ length labelList
--     _                              -> lift $ throwE "type error in pattern"
headConstructor :: [[Pat]] -> WithEnv [(Identifier, Int, [Type])]
headConstructor [] = return []
headConstructor (ps:pss) = do
  ps' <- headConstructor' ps
  pss' <- mapM headConstructor' pss
  return $ join $ ps' : pss'

headConstructor' :: [Pat] -> WithEnv [(Identifier, Int, [Type])]
headConstructor' (pair@(_ :< PatPair _ _):_) = do
  patList <- pairSeq pair
  typeList <- mapM (\(i :< _) -> lookupTypeEnv' i) patList
  return [("pair", 0, typeList)]
headConstructor' _ = return []

collectVar :: [[Pat]] -> WithEnv [Identifier]
collectVar [] = return []
collectVar (ps:pss) = do
  vs1 <- collectVar' ps
  vs2 <- collectVar pss
  return $ vs1 ++ vs2

collectVar' :: [Pat] -> WithEnv [Identifier]
collectVar' [] = return []
collectVar' ((_ :< PatVar s):ps) = do
  tmp <- collectVar' ps
  return $ s : tmp
collectVar' (_:ps) = collectVar' ps

findPatApp :: [[Pat]] -> Maybe Int
findPatApp [] = Nothing
findPatApp (ps:pss) =
  case findPatApp' $ zip ps [0 ..] of
    Nothing -> findPatApp pss
    Just i  -> Just i

findPatApp' :: [(Pat, Int)] -> Maybe Int
findPatApp' []                        = Nothing
findPatApp' ((_ :< PatPair _ _, i):_) = Just i
findPatApp' (_:ps)                    = findPatApp' ps

specialize :: Identifier -> Arity -> ClauseMatrix a -> WithEnv (ClauseMatrix a)
specialize c a (pss, bs) = do
  pss' <- zipWithM (specializeRow c a) pss bs
  return $ patDist $ join pss'

specializeRow :: Identifier -> Arity -> [Pat] -> a -> WithEnv [([Pat], a)]
specializeRow _ _ [] _ = return []
specializeRow _ a ((i :< PatHole):ps) body = do
  newNames <- forM [1 .. a] $ const $ return $ i :< PatHole
  return [(newNames ++ ps, body)]
specializeRow c a ((i :< PatVar _):ps) body =
  specializeRow c a ((i :< PatHole) : ps) body
specializeRow c _ ((_ :< PatConst x):ps) body =
  if c /= x
    then return []
    else return [(ps, body)]
specializeRow c _ ((_ :< PatPair p1 p2):ps) body =
  if c /= "pair"
    then return []
    else return [(p1 : p2 : ps, body)]

defaultMatrix :: ClauseMatrix a -> WithEnv (ClauseMatrix a, Maybe Identifier)
defaultMatrix (pss, bs) = do
  pss' <- zipWithM defaultMatrixRow pss bs
  let pss'' = map fst pss'
  let bounds = takeHeadJust $ map snd pss'
  return (patDist $ join pss'', bounds)

takeHeadJust :: [Maybe a] -> Maybe a
takeHeadJust []             = Nothing
takeHeadJust (Nothing:rest) = takeHeadJust rest
takeHeadJust (Just x:_)     = Just x

defaultMatrixRow :: [Pat] -> a -> WithEnv ([([Pat], a)], Maybe Identifier)
defaultMatrixRow [] _                      = return ([], Nothing)
defaultMatrixRow ((_ :< PatHole):ps) body  = return ([(ps, body)], Nothing)
defaultMatrixRow ((_ :< PatVar s):ps) body = return ([(ps, body)], Just s)
defaultMatrixRow ((_ :< PatConst _):_) _   = return ([], Nothing)
defaultMatrixRow ((_ :< PatPair _ _):_) _  = return ([], Nothing)

swapColumn :: Int -> Int -> [[a]] -> [[a]]
swapColumn i j mat = transpose $ swap i j $ transpose mat
