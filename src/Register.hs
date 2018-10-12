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

type Node = Identifier

type Graph = ([Node], [Edge])

-- regsiter allocation based on chordal graph coloring
regAlloc :: Int -> Asm -> WithEnv ()
regAlloc i asm
  -- liftIO $ putStrLn $ "regalloc"
 = do
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
  lvs <- liveInfo code
  uvs <- defInfo code
  edgeListList <- forM lvs $ \xs -> return [(p, q) | p <- xs, q <- xs]
  let edgeList = filter (uncurry (/=)) $ nub $ join edgeListList
  let nodeList = nub $ join lvs ++ join uvs
  return (nodeList, edgeList)

-- maximum cardinality search
maxCardSearch :: Graph -> WithEnv [Identifier]
maxCardSearch graph@(nodeList, edgeList) = do
  weightList <- mapM (initialWeight edgeList) nodeList
  maxCardSearch' graph (zip nodeList weightList)

type WeightList = [(Identifier, Int)]

-- initial weight for a node is the number of neighbors that are precolored
initialWeight :: [Edge] -> Identifier -> WithEnv Int
initialWeight edgeList v = do
  env <- get
  let isAdjRegVar (p, q) = p == v && q `elem` regVarList env
  return $ length $ filter isAdjRegVar edgeList

maxCardSearch' :: Graph -> WeightList -> WithEnv [Identifier]
maxCardSearch' ([], _) _ = return []
maxCardSearch' (nodeList, edgeList) weightList = do
  let v = fst $ maximumBy (\(_, i) (_, j) -> compare i j) weightList
  let adj = map snd $ filter (\(p, _) -> p == v) edgeList
  let weightList' = updateWeightList adj v weightList
  let nodeList' = filter (/= v) nodeList
  let edgeList' = removeNodeFromEdgeList v edgeList
  vs <- maxCardSearch' (nodeList', edgeList') weightList'
  return $ v : vs

updateWeightList :: [Identifier] -> Identifier -> WeightList -> WeightList
updateWeightList _ _ [] = []
updateWeightList adj v ((w, i):xs) = do
  let i' =
        if w `elem` adj
          then i + 1
          else i
  let xs' = updateWeightList adj v xs
  if v == w
    then xs'
    else (w, i') : xs'

color :: Int -> Graph -> [Identifier] -> WithEnv ()
color _ _ [] = return ()
color i graph@(_, edgeList) (x:xs) = do
  color i graph xs
  mj <- lookupRegEnv x
  case mj of
    Just _ -> return () -- precolored variable
    Nothing -> do
      let adj = map snd $ filter (\(p, _) -> p == x) edgeList
      colorList <- toRegNumList adj
      let min = unusedMinimumRegNum colorList
      if min <= i
        then insRegEnv x min
        else insSpill x

unusedMinimumRegNum :: [Int] -> Int
unusedMinimumRegNum = unusedMinimumRegNum' 0

unusedMinimumRegNum' :: Int -> [Int] -> Int
unusedMinimumRegNum' i xs =
  if i `notElem` xs
    then i
    else unusedMinimumRegNum' (i + 1) xs

-- minimumRegNum :: Int -> [Int] -> Int
removeNodeFromEdgeList :: Identifier -> [Edge] -> [Edge]
removeNodeFromEdgeList _ [] = []
removeNodeFromEdgeList x ((p, _):rest)
  | p == x = removeNodeFromEdgeList x rest
removeNodeFromEdgeList x ((_, q):rest)
  | q == x = removeNodeFromEdgeList x rest
removeNodeFromEdgeList x ((p, q):rest) = (p, q) : removeNodeFromEdgeList x rest

liveInfo :: Asm -> WithEnv [[Identifier]]
liveInfo (meta :< AsmReturn _) = return [asmMetaLive meta]
liveInfo (meta :< AsmLet _ _ cont) = do
  info <- liveInfo cont
  return $ asmMetaLive meta : info
liveInfo (meta :< AsmExtractValue _ _ _ cont) = do
  info <- liveInfo cont
  return $ asmMetaLive meta : info
liveInfo (meta :< AsmInsertValue _ _ _ cont) = do
  info <- liveInfo cont
  return $ asmMetaLive meta : info
liveInfo (meta :< AsmCall _ _ _ cont) = do
  info <- liveInfo cont
  return $ asmMetaLive meta : info
liveInfo (meta :< AsmCompare _ _ cont) = do
  info <- liveInfo cont
  return $ asmMetaDef meta : info
liveInfo (meta :< AsmJumpIfZero (_, body) cont) = do
  info1 <- liveInfo cont
  info2 <- liveInfo body
  return $ asmMetaDef meta : info1 ++ info2
liveInfo (meta :< AsmJump (_, body)) = do
  info <- liveInfo body
  return $ asmMetaDef meta : info
liveInfo (meta :< AsmPush _ cont) = do
  info <- liveInfo cont
  return $ asmMetaLive meta : info
liveInfo (meta :< AsmPop _ cont) = do
  info <- liveInfo cont
  return $ asmMetaLive meta : info
liveInfo (meta :< AsmAddInt64 _ _ cont) = do
  info <- liveInfo cont
  return $ asmMetaLive meta : info
liveInfo (meta :< AsmSubInt64 _ _ cont) = do
  info <- liveInfo cont
  return $ asmMetaLive meta : info

defInfo :: Asm -> WithEnv [[Identifier]]
defInfo (meta :< AsmReturn _) = return [asmMetaDef meta]
defInfo (meta :< AsmLet _ _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info
defInfo (meta :< AsmExtractValue _ _ _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info
defInfo (meta :< AsmInsertValue _ _ _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info
defInfo (meta :< AsmCall _ _ _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info
defInfo (meta :< AsmCompare _ _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info
defInfo (meta :< AsmJumpIfZero (_, body) cont) = do
  info1 <- defInfo cont
  info2 <- defInfo body
  return $ asmMetaDef meta : info1 ++ info2
defInfo (meta :< AsmJump (_, body)) = do
  info <- defInfo body
  return $ asmMetaDef meta : info
defInfo (meta :< AsmPush _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info
defInfo (meta :< AsmPop _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info
defInfo (meta :< AsmAddInt64 _ _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info
defInfo (meta :< AsmSubInt64 _ _ cont) = do
  info <- defInfo cont
  return $ asmMetaDef meta : info

insertSpill :: Asm -> Identifier -> WithEnv Asm
insertSpill (meta :< AsmReturn ans) x =
  insertPop x [ans] $ meta :< AsmReturn ans
insertSpill (meta :< AsmLet dest src cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x (varsInAsmData src) $ meta :< AsmLet dest src cont''
insertSpill (meta :< AsmExtractValue dest base i cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x [base] $ meta :< AsmExtractValue dest base i cont''
insertSpill (meta :< AsmInsertValue val base i cont) x = do
  cont' <- insertSpill cont x
  insertPop x [base] $ meta :< AsmInsertValue val base i cont'
insertSpill (meta :< AsmCall dest fun args cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x (varsInAsmData fun ++ args) $ meta :< AsmCall dest fun args cont''
insertSpill (meta :< AsmCompare p q cont) x = do
  cont' <- insertSpill cont x
  insertPop x [p, q] $ meta :< AsmCompare p q cont'
insertSpill (meta :< AsmJumpIfZero (label, body) cont) x = do
  cont' <- insertSpill cont x
  body' <- insertSpill body x
  return $ meta :< AsmJumpIfZero (label, body') cont'
insertSpill (meta :< AsmJump (label, body)) x = do
  body' <- insertSpill body x
  return $ meta :< AsmJump (label, body')
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
  insertPop x (varsInAsmData arg) $ meta :< AsmAddInt64 arg dest cont''
insertSpill (meta :< AsmSubInt64 arg dest cont) x = do
  cont' <- insertSpill cont x
  cont'' <- insertPush x [dest] cont'
  insertPop x (varsInAsmData arg) $ meta :< AsmSubInt64 arg dest cont''

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
