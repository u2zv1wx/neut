module Register
  ( regAlloc
  ) where

import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Control.Comonad.Cofree

import           Data.List

import           Data
import           Liveness

import           Debug.Trace

import qualified Text.Show.Pretty           as Pr

type Edge = (Identifier, Identifier)

type Graph = [Edge]

-- regsiter allocation based on chordal graph coloring
regAlloc :: Int -> Asm -> WithEnv ()
regAlloc i asm = do
  asm' <- annotAsm asm >>= computeLiveness
  graph <- build asm'
  xs <- maxCardSearch graph
  env <- get
  color i graph xs
  env' <- get
  case spill env' of
    Nothing -> return ()
    Just x -> do
      asm'' <- insertSpill asm x >>= annotAsm >>= computeLiveness
      put env
      regAlloc i asm''

build :: Asm -> WithEnv Graph
build code = do
  info <- edgeInfo code
  edgeListList <- forM info $ \xs -> return [(p, q) | p <- xs, q <- xs]
  let edgeList = filter (uncurry (/=)) $ nub $ join edgeListList
  return edgeList

-- maximum cardinality search
maxCardSearch :: Graph -> WithEnv [Identifier]
maxCardSearch graph = do
  let nodeList = nub $ map fst graph
  weightList <- mapM (initialWeight graph) nodeList
  maxCardSearch' graph (zip nodeList weightList)

type WeightList = [(Identifier, Int)]

-- initial weight for a node is the number of neighbors that are precolored
initialWeight :: Graph -> Identifier -> WithEnv Int
initialWeight graph v = do
  env <- get
  let isAdjRegVar (p, q) = p == v && q `elem` regVarList env
  return $ length $ filter isAdjRegVar graph

maxCardSearch' :: Graph -> WeightList -> WithEnv [Identifier]
maxCardSearch' [] _ = return []
maxCardSearch' graph weightList = do
  let v = fst $ maximumBy (\(_, i) (_, j) -> compare i j) weightList
  let adj = map snd $ filter (\(p, _) -> p == v) graph
  let weightList' = updateWeightList adj weightList
  let graph' = removeNodeFromEdgeList v graph
  vs <- maxCardSearch' graph' weightList'
  return $ v : vs

updateWeightList :: [Identifier] -> WeightList -> WeightList
updateWeightList adj weightList =
  flip map weightList $ \(ident, i) ->
    if ident `elem` adj
      then (ident, i + 1)
      else (ident, i)

color :: Int -> Graph -> [Identifier] -> WithEnv ()
color _ _ [] = return ()
color i graph (x:xs) = do
  color i graph xs
  mj <- lookupRegEnv x
  case mj of
    Just _ -> return () -- precolored variable
    Nothing -> do
      let adj = map snd $ filter (\(p, _) -> p == x) graph
      env <- get
      let colorList = map snd $ filter (\(y, _) -> y `elem` adj) $ regEnv env
      let min = minimum colorList
      if min <= i
        then insRegEnv x min
        else insSpill x

removeNodeFromEdgeList :: Identifier -> [Edge] -> [Edge]
removeNodeFromEdgeList _ [] = []
removeNodeFromEdgeList x ((p, _):rest)
  | p == x = removeNodeFromEdgeList x rest
removeNodeFromEdgeList x ((p, q):rest) = (p, q) : removeNodeFromEdgeList x rest

edgeInfo :: Asm -> WithEnv [[Identifier]]
edgeInfo (meta :< AsmReturn _) = return [asmMetaLive meta]
edgeInfo (meta :< AsmMov _ _ cont) = do
  info <- edgeInfo cont
  return $ asmMetaLive meta : info
edgeInfo (meta :< AsmLoadWithOffset _ _ _ cont) = do
  info <- edgeInfo cont
  return $ asmMetaLive meta : info
edgeInfo (meta :< AsmStoreWithOffset _ _ _ cont) = do
  info <- edgeInfo cont
  return $ asmMetaLive meta : info
edgeInfo (meta :< AsmCall _ _ _ cont) = do
  info <- edgeInfo cont
  return $ asmMetaLive meta : info
edgeInfo (meta :< AsmPush _ cont) = do
  info <- edgeInfo cont
  return $ asmMetaLive meta : info
edgeInfo (meta :< AsmPop _ cont) = do
  info <- edgeInfo cont
  return $ asmMetaLive meta : info
edgeInfo (meta :< AsmAddInt64 _ _ cont) = do
  info <- edgeInfo cont
  return $ asmMetaLive meta : info
edgeInfo (meta :< AsmSubInt64 _ _ cont) = do
  info <- edgeInfo cont
  return $ asmMetaLive meta : info

insertSpill :: Asm -> Identifier -> WithEnv Asm
insertSpill (meta :< AsmReturn ans) x =
  insertPop x [ans] $ meta :< AsmReturn ans
insertSpill (meta :< AsmMov dest src cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x (varsInAsmArg src) $ meta :< AsmMov dest src cont''
insertSpill (meta :< AsmLoadWithOffset offset base dest cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x [base] $ meta :< AsmLoadWithOffset offset base dest cont''
insertSpill (meta :< AsmStoreWithOffset val offset base cont) x = do
  cont' <- insertSpill cont x
  insertPop x [base] $ meta :< AsmStoreWithOffset val offset base cont'
insertSpill (meta :< AsmCall dest fun args cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x (fun : args) $ meta :< AsmCall dest fun args cont''
insertSpill (meta :< AsmPush y cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [y] cont'
  return $ meta :< AsmPush y cont''
insertSpill (meta :< AsmPop y cont) x = do
  cont' <- insertSpill cont x
  insertPop x [y] $ meta :< AsmPop y cont'
insertSpill (meta :< AsmAddInt64 arg dest cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x (varsInAsmArg arg) $ meta :< AsmAddInt64 arg dest cont''
insertSpill (meta :< AsmSubInt64 arg dest cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x (varsInAsmArg arg) $ meta :< AsmSubInt64 arg dest cont''

insertPush :: Identifier -> [Identifier] -> Asm -> WithEnv Asm
insertPush x ds asm =
  if x `elem` ds
    then addMeta $ AsmPush x asm
    else return asm

insertPop :: Identifier -> [Identifier] -> Asm -> WithEnv Asm
insertPop x us asm =
  if x `elem` us
    then addMeta $ AsmPop x asm
    else return asm
