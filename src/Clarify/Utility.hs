{-# LANGUAGE OverloadedStrings #-}

module Clarify.Utility where

import Control.Monad.Except
import Control.Monad.State

import Data.Basic
import Data.Code
import Data.Env
import Data.Term
import Reduce.Code

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
            arrVoidPtr
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
            arrVoidPtr
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
  return (m, DataSigmaIntro arrVoidPtr [aff, rel])

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
        (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro arrVoidPtr []))
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
        ( emptyMeta
        , CodeUpIntro (emptyMeta, DataSigmaIntro arrVoidPtr [immVar, immVar]))
      return theta

cartesianUniv :: Meta -> WithEnv DataPlus
cartesianUniv m = do
  aff <- affineUniv m
  rel <- relevantUniv m
  return (m, DataSigmaIntro arrVoidPtr [aff, rel])

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
            arrVoidPtr
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro arrVoidPtr [])))
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
            arrVoidPtr
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            ( emptyMeta
            , CodeUpIntro
                ( emptyMeta
                , DataSigmaIntro
                    arrVoidPtr
                    [ (emptyMeta, DataSigmaIntro arrVoidPtr [affVar, relVar])
                    , (emptyMeta, DataSigmaIntro arrVoidPtr [affVar, relVar])
                    ])))
      return theta

cartesianStruct :: Meta -> [ArrayKind] -> WithEnv DataPlus
cartesianStruct m ks = do
  aff <- affineStruct m ks
  rel <- relevantStruct m ks
  return (m, DataSigmaIntro arrVoidPtr [aff, rel])

affineStruct :: Meta -> [ArrayKind] -> WithEnv DataPlus
affineStruct m ks = do
  cenv <- gets codeEnv
  let thetaName = "affine-struct"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (structVarName, structVar) <- newDataUpsilonWith "struct"
      xs <- mapM (const $ newNameWith "var") ks
      insCodeEnv
        thetaName
        [structVarName]
        ( emptyMeta
        , CodeStructElim
            (zip xs ks)
            structVar
            (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro arrVoidPtr [])))
      return theta

relevantStruct :: Meta -> [ArrayKind] -> WithEnv DataPlus
relevantStruct m ks = do
  cenv <- gets codeEnv
  let thetaName = "relevant-struct"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (structVarName, structVar) <- newDataUpsilonWith "struct"
      xs <- mapM (const $ newNameWith "var") ks
      let vs = map (\y -> (emptyMeta, DataUpsilon y)) xs
      let vks = zip vs ks
      insCodeEnv
        thetaName
        [structVarName]
        ( emptyMeta
        , CodeStructElim
            (zip xs ks)
            structVar
            ( emptyMeta
            , CodeUpIntro
                ( emptyMeta
                , DataSigmaIntro
                    arrVoidPtr
                    [ (emptyMeta, DataStructIntro vks)
                    , (emptyMeta, DataStructIntro vks)
                    ])))
      return theta

renameData :: DataPlus -> WithEnv DataPlus
renameData (m, DataTheta x) = return (m, DataTheta x)
renameData (m, DataUpsilon x) = do
  x' <- lookupNameEnv x
  return (m, DataUpsilon x')
renameData (m, DataSigmaIntro mk ds) = do
  ds' <- mapM renameData ds
  return (m, DataSigmaIntro mk ds')
renameData (m, DataIntS size x) = return (m, DataIntS size x)
renameData (m, DataIntU size x) = return (m, DataIntU size x)
renameData (m, DataFloat16 x) = return (m, DataFloat16 x)
renameData (m, DataFloat32 x) = return (m, DataFloat32 x)
renameData (m, DataFloat64 x) = return (m, DataFloat64 x)
renameData (m, DataEnumIntro x) = return (m, DataEnumIntro x)
renameData (m, DataStructIntro dks) = do
  let (ds, ks) = unzip dks
  ds' <- mapM renameData ds
  return (m, DataStructIntro $ zip ds' ks)

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
renameCode (m, CodeStructElim xks d e) = do
  d' <- renameData d
  (xks', e') <- renameStruct xks e
  return (m, CodeStructElim xks' d' e')

renameStruct ::
     [(Identifier, ArrayKind)]
  -> CodePlus
  -> WithEnv ([(Identifier, ArrayKind)], CodePlus)
renameStruct [] e = do
  e' <- renameCode e
  return ([], e')
renameStruct ((x, t):xts) e = do
  local $ do
    x' <- newNameWith x
    (xts', e') <- renameStruct xts e
    return ((x', t) : xts', e')

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
renameTheta (ThetaArrayAccess t d1 d2) = do
  d1' <- renameData d1
  d2' <- renameData d2
  return $ ThetaArrayAccess t d1' d2'
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
  e' <- reduceCodePlus e
  e'' <- renameCode e'
  -- Since LLVM doesn't allow variable shadowing, we must explicitly
  -- rename variables here.
  modify (\env -> env {codeEnv = Map.insert name (args', e'') (codeEnv env)})

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
