module Register where

import           Data

import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Control.Comonad.Cofree

import           Data.List

import           Debug.Trace

import qualified Text.Show.Pretty           as Pr

type Edge = (Identifier, Identifier)

type Graph = [Edge]

regAlloc :: Int -> WithEnv ()
regAlloc i = do
  env <- get
  graphList <-
    forM (funEnv env) $ \(_, codeRef) -> do
      code <- liftIO $ readIORef codeRef
      build code
  let graph = join graphList
  let nodeList = nub $ map (\(i, _) -> i) graph
  is <- simplify nodeList i graph
  select i is graph

regAlloc' :: Int -> Code -> WithEnv ()
regAlloc' i code = do
  graph <- build code
  let nodeList = nub $ map (\(i, _) -> i) graph
  is <- simplify nodeList i graph
  select i is graph

build :: Code -> WithEnv Graph
build code = do
  info <- edgeInfo code
  edgeListList <- forM info $ \xs -> return [(p, q) | p <- xs, q <- xs]
  let edgeList = filter (\(i, j) -> i /= j) $ nub $ join edgeListList
  return edgeList

simplify :: [Identifier] -> Int -> Graph -> WithEnv [Identifier]
simplify _ _ [] = return []
simplify nodeList i edges = do
  case selectNode i nodeList edges of
    Nothing -> undefined -- spill
    Just x -> do
      let edges' = removeNodeFromEdgeList x edges
      let nodeList' = filter (\y -> y /= x) nodeList
      xs <- simplify nodeList' i edges'
      return $ x : xs

degree :: Identifier -> Graph -> Int
degree node edges = length $ filter (\(i, _) -> i == node) edges

selectNode :: Int -> [Identifier] -> Graph -> Maybe Identifier
selectNode _ [] _ = Nothing
selectNode i (x:xs) g = do
  if degree x g < i
    then Just x
    else selectNode i xs g

removeNodeFromEdgeList :: Identifier -> [Edge] -> [Edge]
removeNodeFromEdgeList _ [] = []
removeNodeFromEdgeList x ((p, _):rest)
  | p == x = removeNodeFromEdgeList x rest
removeNodeFromEdgeList x ((p, q):rest) = (p, q) : removeNodeFromEdgeList x rest

select :: Int -> [Identifier] -> Graph -> WithEnv ()
select _ [] _ = return ()
select i (x:xs) g = do
  let adj = map snd $ filter (\(p, _) -> p == x) g
  colorList <- getColorList adj
  case selectColor i colorList of
    Nothing -> undefined -- spill
    Just c -> do
      insRegEnv x c
      select i xs g

getColorList :: [Identifier] -> WithEnv [Int]
getColorList [] = return []
getColorList (x:xs) = do
  tmp <- lookupRegEnv x
  case tmp of
    Nothing -> getColorList xs
    Just i -> do
      is <- getColorList xs
      return $ i : is

selectColor :: Int -> [Int] -> Maybe Int
selectColor i xs = selectColor' [1 .. i] xs

selectColor' :: [Int] -> [Int] -> Maybe Int
selectColor' [] _ = Nothing
selectColor' (i:is) xs =
  if i `notElem` xs
    then Just i
    else selectColor' is xs

edgeInfo :: Code -> WithEnv [[Identifier]]
edgeInfo (meta :< (CodeReturn _ _ _)) = do
  return $ [codeMetaLive meta]
edgeInfo (meta :< (CodeLet _ _ cont)) = do
  info <- edgeInfo cont
  return $ codeMetaLive meta : info
edgeInfo (meta :< (CodeLetLink _ _ cont)) = do
  info <- edgeInfo cont
  return $ codeMetaLive meta : info
edgeInfo (meta :< (CodeSwitch _ defaultBranch branchList)) = do
  let labelList = defaultBranch : map snd branchList
  infoList <-
    forM labelList $ \label -> do
      lookupFunEnv label >>= liftIO . readIORef >>= edgeInfo
  return $ codeMetaLive meta : join infoList
edgeInfo (meta :< (CodeJump labelName)) = do
  info <- lookupFunEnv labelName >>= liftIO . readIORef >>= edgeInfo
  return $ codeMetaLive meta : info
edgeInfo (meta :< (CodeIndirectJump _)) = do
  return [codeMetaLive meta]
edgeInfo (meta :< (CodeStore _ _ cont)) = do
  info <- edgeInfo cont
  return $ codeMetaLive meta : info
edgeInfo (meta :< (CodeLoad _ _ cont)) = do
  info <- edgeInfo cont
  return $ codeMetaLive meta : info
edgeInfo (meta :< (CodeStackSave _ cont)) = do
  info <- edgeInfo cont
  return $ codeMetaLive meta : info
edgeInfo (meta :< (CodeStackRestore _ cont)) = do
  info <- edgeInfo cont
  return $ codeMetaLive meta : info
