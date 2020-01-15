{-# LANGUAGE OverloadedStrings #-}

module Clarify.Utility where

import Control.Monad.Except
import Control.Monad.State

import Data.Basic
import Data.Code
import Data.Env
import Data.Term

import qualified Data.HashMap.Strict as Map

type Context = [(Identifier, TermPlus)]

-- toAffineApp meta x t ~>
--   bind exp := t in
--   let (aff, rel) := exp in
--   aff @ x
--
-- {} toAffineApp {}
toAffineApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toAffineApp m x t = do
  (expVarName, expVar) <- newDataUpsilonWith "aff-app-exp"
  (affVarName, affVar) <- newDataUpsilonWith "aff-app-aff"
  (relVarName, _) <- newDataUpsilonWith "aff-app-rel"
  retImmType <- returnCartesianImmediate
  return
    ( m
    , CodeUpElim
        expVarName
        t
        ( emptyMeta
        , CodeSigmaElim
            Nothing
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            (m, CodePiElimDownElim affVar [toDataUpsilon (x, m)])))

-- toRelevantApp meta x t ~>
--   bind exp := t in
--   let (aff, rel) := exp in
--   rel @ x
--
-- {} toRelevantApp {}
toRelevantApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toRelevantApp m x t = do
  (expVarName, expVar) <- newDataUpsilonWith "rel-app-exp"
  (affVarName, _) <- newDataUpsilonWith "rel-app-aff"
  (relVarName, relVar) <- newDataUpsilonWith "rel-app-rel"
  retImmType <- returnCartesianImmediate
  return
    ( m
    , CodeUpElim
        expVarName
        t
        ( m
        , CodeSigmaElim
            Nothing
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            (m, CodePiElimDownElim relVar [toDataUpsilon (x, m)])))

-- {each x in xes is used linearly in cont} bindLet {each x in xes is used linearly in cont}
bindLet :: [(Identifier, CodePlus)] -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = (fst e, CodeUpElim x e $ bindLet xes cont)

returnUpsilon :: Identifier -> CodePlus
returnUpsilon x = (emptyMeta, CodeUpIntro (emptyMeta, DataUpsilon x))

-- {} returnCartesianImmediate {v is the aff-rel pair off imm}
returnCartesianImmediate :: WithEnv CodePlus
returnCartesianImmediate = do
  v <- cartesianImmediate emptyMeta
  return (emptyMeta, CodeUpIntro v)

-- {} returnCartesianUniv {v is the aff-rel pair of univ}
returnCartesianUniv :: WithEnv CodePlus
returnCartesianUniv = do
  v <- cartesianUniv emptyMeta
  return (emptyMeta, CodeUpIntro v)

cartesianImmediate :: Meta -> WithEnv DataPlus
cartesianImmediate m = do
  aff <- affineImmediate m
  rel <- relevantImmediate m
  return (m, DataSigmaIntro [aff, rel])

affineImmediate :: Meta -> WithEnv DataPlus
affineImmediate m = do
  cenv <- gets codeEnv
  let thetaName = "affine-immediate"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      immVarName <- newNameWith "arg"
      insCodeEnv
        thetaName
        [immVarName]
        (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro []))
      return theta

relevantImmediate :: Meta -> WithEnv DataPlus
relevantImmediate m = do
  cenv <- gets codeEnv
  let thetaName = "relevant-immediate"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (immVarName, immVar) <- newDataUpsilonWith "arg"
      insCodeEnv
        thetaName
        [immVarName]
        (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro [immVar, immVar]))
      return theta

cartesianUniv :: Meta -> WithEnv DataPlus
cartesianUniv m = do
  aff <- affineUniv m
  rel <- relevantUniv m
  return (m, DataSigmaIntro [aff, rel])

-- \x -> let (_, _) := x in unit
affineUniv :: Meta -> WithEnv DataPlus
affineUniv m = do
  cenv <- gets codeEnv
  let thetaName = "affine-univ"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (univVarName, univVar) <- newDataUpsilonWith "univ"
      affVarName <- newNameWith "aff-univ"
      relVarName <- newNameWith "rel-univ"
      retImmType <- returnCartesianImmediate
      insCodeEnv
        thetaName
        [univVarName]
        -- let (a, b) := x in return ()
        ( emptyMeta
        , CodeSigmaElim
            Nothing
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro [])))
      return theta

relevantUniv :: Meta -> WithEnv DataPlus
relevantUniv m = do
  cenv <- gets codeEnv
  let thetaName = "relevant-univ"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (univVarName, univVar) <- newDataUpsilonWith "univ"
      (affVarName, affVar) <- newDataUpsilonWith "aff-univ"
      (relVarName, relVar) <- newDataUpsilonWith "rel-univ"
      retImmType <- returnCartesianImmediate
      insCodeEnv
        thetaName
        [univVarName]
        -- let (a, b) := x in return ((a, b), (a, b))
        ( emptyMeta
        , CodeSigmaElim
            Nothing
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            ( emptyMeta
            , CodeUpIntro
                ( emptyMeta
                , DataSigmaIntro
                    [ (emptyMeta, DataSigmaIntro [affVar, relVar])
                    , (emptyMeta, DataSigmaIntro [affVar, relVar])
                    ])))
      return theta

-- cartesianInnerArray :: Meta -> ArrayKind -> DataPlus -> WithEnv DataPlus
-- cartesianInnerArray m k size = do
--   aff <- affineInnerArray m
--   rel <- relevantInnerArray m k size
--   return (m, DataSigmaIntro [aff, rel])
-- affineInnerArray :: Meta -> WithEnv DataPlus
-- affineInnerArray _ = undefined
--   -- cenv <- gets codeEnv
--   -- let thetaName = "affine-inner-array"
--   -- let theta = (m, DataTheta thetaName)
--   -- case Map.lookup thetaName cenv of
--   --   Just _ -> return theta
--   --   Nothing -> do
--   --     (arrVarName, arrVar) <- newDataUpsilonWith "inner-array"
--   --     -- arrayはふつうにfreeできる
--   --     insCodeEnv thetaName [arrVarName] (emptyMeta, CodeFree arrVar)
--   --     return theta
-- relevantInnerArray :: Meta -> ArrayKind -> DataPlus -> WithEnv DataPlus
-- relevantInnerArray _ _ _ = do
--   undefined
--   -- cenv <- gets codeEnv
--   -- let thetaName = "relevant-inner-array"
--   -- let theta = (m, DataTheta thetaName)
--   -- case Map.lookup thetaName cenv of
--   --   Just _ -> return theta
--   --   Nothing -> do
--   --     (arrVarName, arrVar) <- newDataUpsilonWith "inner-array"
--   --     -- elemSize : u8 ~> 1, u9 ~> 2, u16 ~> 2, u17 ~> 3, etc.
--   --     let elemSize = (emptyMeta, DataIntU 64 $ arrayKindToSize k)
--   --     -- retAllocSize = return (size * num)
--   --     let retAllocSize = thetaMul elemSize num
--   --     (sizeVarName, sizeVar) <- newDataUpsilonWith "size"
--   --     (destVarName, destVar) <- newDataUpsilonWith "dest"
--   --     holeVarName <- newNameWith "hole"
--   --     let m' = emptyMeta
--   --     insCodeEnv
--   --       thetaName
--   --       [arrVarName]
--   --       ( m'
--   --       -- calculate the allocation size
--   --       , CodeUpElim
--   --           sizeVarName
--   --           retAllocSize
--   --           ( m'
--   --           -- allocate region
--   --           , CodeUpElim
--   --               destVarName
--   --               (m', CodeUpIntro (m', DataAlloc sizeVar))
--   --               ( m'
--   --               -- copy data
--   --               , CodeUpElim
--   --                   holeVarName
--   --                   (m', CodeMemCpy destVar arrVar sizeVar)
--   --                   -- return result
--   --                   (m', CodeUpIntro (m', DataSigmaIntro [destVar, arrVar])))))
--   --     return theta
thetaMul :: DataPlus -> DataPlus -> CodePlus
thetaMul d1 d2 =
  (emptyMeta, CodeTheta $ ThetaBinaryOp BinaryOpMul (LowTypeIntU 64) d1 d2)

renameData :: DataPlus -> WithEnv DataPlus
renameData (m, DataTheta x) = return (m, DataTheta x)
renameData (m, DataUpsilon x) = do
  x' <- lookupNameEnv x
  return (m, DataUpsilon x')
renameData (m, DataSigmaIntro ds) = do
  ds' <- mapM renameData ds
  return (m, DataSigmaIntro ds')
renameData (m, DataIntS size x) = return (m, DataIntS size x)
renameData (m, DataIntU size x) = return (m, DataIntU size x)
renameData (m, DataFloat16 x) = return (m, DataFloat16 x)
renameData (m, DataFloat32 x) = return (m, DataFloat32 x)
renameData (m, DataFloat64 x) = return (m, DataFloat64 x)
renameData (m, DataEnumIntro x) = return (m, DataEnumIntro x)
renameData (m, DataArrayIntro kind les) = do
  les' <-
    forM les $ \(l, body) -> do
      body' <- renameData body
      return (l, body')
  return (m, DataArrayIntro kind les')

renameCode :: CodePlus -> WithEnv CodePlus
renameCode (m, CodeTheta theta) = do
  theta' <- renameTheta theta
  return (m, CodeTheta theta')
renameCode (m, CodePiElimDownElim v vs) = do
  v' <- renameData v
  vs' <- mapM renameData vs
  return (m, CodePiElimDownElim v' vs')
renameCode (m, CodeSigmaElim mk xts d e) = do
  d' <- renameData d
  (xts', e') <- renameBinderWithBody xts e
  return (m, CodeSigmaElim mk xts' d' e')
renameCode (m, CodeUpIntro d) = do
  d' <- renameData d
  return (m, CodeUpIntro d')
renameCode (m, CodeUpElim x e1 e2) = do
  e1' <- renameCode e1
  local $ do
    x' <- newNameWith x
    e2' <- renameCode e2
    return (m, CodeUpElim x' e1' e2')
renameCode (m, CodeEnumElim d les) = do
  d' <- renameData d
  les' <- renameCaseList les
  return (m, CodeEnumElim d' les')
renameCode (m, CodeArrayElim k d1 d2) = do
  d1' <- renameData d1
  d2' <- renameData d2
  return (m, CodeArrayElim k d1' d2')

renameBinderWithBody ::
     [(Identifier, CodePlus)]
  -> CodePlus
  -> WithEnv ([(Identifier, CodePlus)], CodePlus)
renameBinderWithBody [] e = do
  e' <- renameCode e
  return ([], e')
renameBinderWithBody ((x, t):xts) e = do
  t' <- renameCode t
  local $ do
    x' <- newNameWith x
    (xts', e') <- renameBinderWithBody xts e
    return ((x', t') : xts', e')

renameCaseList :: [(Case, CodePlus)] -> WithEnv [(Case, CodePlus)]
renameCaseList les =
  forM les $ \(l, body) ->
    local $ do
      body' <- renameCode body
      return (l, body')

renameTheta :: Theta -> WithEnv Theta
renameTheta (ThetaUnaryOp op t d) = do
  d' <- renameData d
  return $ ThetaUnaryOp op t d'
renameTheta (ThetaBinaryOp op t d1 d2) = do
  d1' <- renameData d1
  d2' <- renameData d2
  return $ ThetaBinaryOp op t d1' d2'
renameTheta (ThetaSysCall c ds) = do
  ds' <- mapM renameData ds
  return $ ThetaSysCall c ds'

local :: WithEnv a -> WithEnv a
local comp = do
  env <- get
  x <- comp
  modify (\e -> env {count = count e})
  return x

insCodeEnv :: Identifier -> [Identifier] -> CodePlus -> WithEnv ()
insCodeEnv name args e = do
  args' <- mapM newNameWith args
  -- e' <- reduceCodePlus e
  e' <- renameCode e
  -- Since LLVM doesn't allow variable shadowing, we must explicitly
  -- rename variables here.
  modify (\env -> env {codeEnv = Map.insert name (args', e') (codeEnv env)})

lookupContext :: Identifier -> Context -> WithEnv TermPlus
lookupContext z ctx = do
  case lookup z ctx of
    Nothing -> throwError "lookupContext"
    Just t -> return t

insTypeEnv :: Identifier -> TermPlus -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = Map.insert i t (typeEnv e)})

isClosedChain :: [(Identifier, CodePlus)] -> Bool
isClosedChain xts = null (isClosedChain' xts)

isClosedChain' :: [(Identifier, CodePlus)] -> [Identifier]
isClosedChain' [] = []
isClosedChain' ((x, t):xts) =
  varCode t ++ (filter ((/=) x) $ isClosedChain' xts)
