module LLVM
  ( toLLVM
  ) where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.List (sortBy)

import Data.Basic
import Data.Code
import Data.Env
import Data.LLVM

toLLVM :: CodePlus -> WithEnv LLVM
toLLVM mainTerm = do
  penv <- gets codeEnv
  forM_ penv $ \(name, (args, e)) -> do
    llvm <- llvmCode e
    insLLVMEnv name args llvm
  llvmCode mainTerm

llvmCode :: CodePlus -> WithEnv LLVM
llvmCode (m, CodeTheta theta) = llvmCodeTheta m theta
llvmCode (_, CodeEpsilonElim v branchList) = llvmCodeEpsilonElim v branchList
llvmCode (_, CodePiElimDownElim v ds) = do
  xs <- mapM (const (newNameWith "arg")) ds
  (fun, castThen) <- llvmCast v $ toFunPtrType ds
  cont <- castThen $ LLVMCall fun (map LLVMDataLocal xs)
  llvmDataLet' (zip xs ds) $ cont
llvmCode (_, CodeSigmaElim xs v e) = do
  let structPtrType = toStructPtrType $ length xs
  let idxList = map (LLVMDataIntS 64) [0 ..]
  loadContent v structPtrType (zip idxList xs) voidPtr e
llvmCode (_, CodeUpIntro d) = do
  result <- newNameWith "ans"
  llvmDataLet result d $ LLVMReturn $ LLVMDataLocal result
llvmCode (_, CodeUpElim x e1 e2) = do
  e1' <- llvmCode e1
  e2' <- llvmCode e2
  return $ LLVMLet x e1' e2'
llvmCode (_, CodeArrayElim k d1 d2) = do
  (idxName, idx) <- newDataLocal "idx"
  result <- newNameWith "ans"
  let elemType = arrayKindToLowType k
  let arrayPtrType = LowTypeArrayPtr 0 elemType
  l <- loadContent d1 arrayPtrType [(idx, result)] elemType (retUp result)
  llvmDataLet' [(idxName, d2)] l

retUp :: Identifier -> CodePlus
retUp result = (Nothing, CodeUpIntro (Nothing, DataUpsilon result))

loadContent ::
     DataPlus -- base pointer
  -> LowType -- the type of base pointer
  -> [(LLVMData, Identifier)] -- [(the index of an element, the variable to load the element)]
  -> LowType -- the type of elements
  -> CodePlus -- continuation
  -> WithEnv LLVM
loadContent v bt ixs et cont = do
  (bp, castThen) <- llvmCast v bt
  cont' <- llvmCode cont
  extractThenFreeThenCont <- loadContent' bp bt et ixs cont'
  castThen extractThenFreeThenCont

loadContent' ::
     LLVMData -- base pointer
  -> LowType -- the type of base pointer
  -> LowType -- the type of elements
  -> [(LLVMData, Identifier)] -- [(the index of an element, the variable to keep the loaded content)]
  -> LLVM -- continuation
  -> WithEnv LLVM
loadContent' bp bt _ [] cont = do
  l <- llvmUncast bp bt
  tmp <- newNameWith "base"
  hole <- newNameWith "hole"
  return $ LLVMLet tmp l $ LLVMLet hole (LLVMFree (LLVMDataLocal tmp)) cont
loadContent' bp bt et ((i, x):xis) cont = do
  cont' <- loadContent' bp bt et xis cont
  (posName, pos) <- newDataLocal "pos"
  return $
    LLVMLet posName (LLVMGetElementPtr (bp, bt) i) $
    LLVMLet x (LLVMLoad pos et) cont'

llvmCodeTheta :: CodeMeta -> Theta -> WithEnv LLVM
llvmCodeTheta _ (ThetaUnaryOp op lowType v)
  | UnaryOpNeg <- op = llvmCodeUnaryOp op lowType lowType v
  | Just codType <- getCodType op = llvmCodeUnaryOp op lowType codType v
  | otherwise = throwError "llvmCodeTheta.ThetaUnaryOp"
llvmCodeTheta _ (ThetaBinaryOp op lowType v1 v2)
  | isArithOp op = llvmCodeBinaryOp op lowType lowType v1 v2
  | isCompareOp op = llvmCodeBinaryOp op lowType (LowTypeSignedInt 1) v1 v2
  | otherwise = throwError "llvmCodeTheta.ThetaBinaryOp"
llvmCodeTheta _ (ThetaPrint v) = do
  let t = LowTypeSignedInt 64
  (pName, p) <- newDataLocal "arg"
  c <- newNameWith "cast"
  llvmDataLet pName v $
    LLVMLet c (LLVMPointerToInt p voidPtr t) $ LLVMPrint t (LLVMDataLocal c)

llvmCodeUnaryOp :: UnaryOp -> LowType -> LowType -> DataPlus -> WithEnv LLVM
llvmCodeUnaryOp op domType codType d = do
  (x, castThen) <- llvmCast d domType
  result <- newNameWith "result"
  uncast <- llvmUncast (LLVMDataLocal result) codType
  castThen $ LLVMLet result (LLVMUnaryOp (op, domType) x) uncast

llvmCodeBinaryOp ::
     BinaryOp -> LowType -> LowType -> DataPlus -> DataPlus -> WithEnv LLVM
llvmCodeBinaryOp op domType codType v1 v2 = do
  (x1, cast1then) <- llvmCast v1 domType
  (x2, cast2then) <- llvmCast v2 domType
  result <- newNameWith "result"
  uncast <- llvmUncast (LLVMDataLocal result) codType
  (cast1then >=> cast2then) $
    LLVMLet result (LLVMBinaryOp (op, domType) x1 x2) uncast

llvmCast :: DataPlus -> LowType -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCast v lowType@(LowTypeSignedInt _) = llvmCastInt v lowType
llvmCast v lowType@(LowTypeUnsignedInt _) = llvmCastInt v lowType
llvmCast v (LowTypeFloat i) = llvmCastFloat v i
llvmCast v ptrType = do
  x <- newNameWith "var"
  return
    ( LLVMDataLocal x
    , \cont -> do
        tmp <- newNameWith "var"
        llvmDataLet tmp v $
          LLVMLet x (LLVMBitcast (LLVMDataLocal tmp) voidPtr ptrType) cont)

llvmCastInt :: DataPlus -> LowType -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastInt v lowType = do
  x <- newNameWith "arg"
  y <- newNameWith "cast"
  return
    ( LLVMDataLocal y
    , \cont -> do
        llvmDataLet x v $
          LLVMLet y (LLVMPointerToInt (LLVMDataLocal x) voidPtr lowType) $ cont)

llvmCastFloat ::
     DataPlus -> FloatSize -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastFloat v size = do
  let floatType = LowTypeFloat size
  let intType = LowTypeSignedInt $ sizeAsInt size
  (xName, x) <- newDataLocal "arg"
  (yName, y) <- newDataLocal "tmp"
  z <- newNameWith "cast"
  return
    ( LLVMDataLocal z
    , \cont -> do
        llvmDataLet xName v $
          LLVMLet yName (LLVMPointerToInt x voidPtr intType) $
          LLVMLet z (LLVMBitcast y intType floatType) cont)

-- uncast: {some-concrete-type} -> voidPtr
llvmUncast :: LLVMData -> LowType -> WithEnv LLVM
llvmUncast result lowType@(LowTypeSignedInt _) =
  return $ llvmUncastInt result lowType
llvmUncast result lowType@(LowTypeUnsignedInt _) =
  return $ llvmUncastInt result lowType
llvmUncast result (LowTypeFloat i) = llvmUncastFloat result i
llvmUncast result ptrType = return $ LLVMBitcast result ptrType voidPtr

llvmUncastInt :: LLVMData -> LowType -> LLVM
llvmUncastInt result lowType = LLVMIntToPointer result lowType voidPtr

llvmUncastFloat :: LLVMData -> FloatSize -> WithEnv LLVM
llvmUncastFloat floatResult i = do
  let floatType = LowTypeFloat i
  let intType = LowTypeSignedInt $ sizeAsInt i
  tmp <- newNameWith "tmp"
  return $
    LLVMLet tmp (LLVMBitcast floatResult floatType intType) $
    LLVMIntToPointer (LLVMDataLocal tmp) intType voidPtr

llvmUncastLet :: Identifier -> LLVMData -> LowType -> LLVM -> WithEnv LLVM
llvmUncastLet x d lowType cont = do
  l <- llvmUncast d lowType
  return $ LLVMLet x l cont

-- `llvmDataLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
llvmDataLet :: Identifier -> DataPlus -> LLVM -> WithEnv LLVM
llvmDataLet x (_, DataTheta y) cont = do
  penv <- gets codeEnv
  case lookup y penv of
    Nothing -> lift $ throwE $ "no such global label defined: " ++ y -- FIXME
    Just (args, _) ->
      llvmUncastLet x (LLVMDataGlobal y) (toFunPtrType args) cont
llvmDataLet x (_, DataUpsilon y) cont =
  llvmUncastLet x (LLVMDataLocal y) voidPtr cont
llvmDataLet x (m, DataEpsilonIntro label) cont = do
  i <- getEpsilonNum label
  llvmDataLet x (m, DataIntS 64 (toInteger i)) cont
llvmDataLet reg (_, DataSigmaIntro ds) cont = do
  storeContent reg voidPtr (toStructPtrType $ length ds) ds cont
llvmDataLet x (_, DataIntS j i) cont =
  llvmUncastLet x (LLVMDataIntS j i) (LowTypeSignedInt j) cont
llvmDataLet x (_, DataIntU j i) cont =
  llvmUncastLet x (LLVMDataIntU j i) (LowTypeUnsignedInt j) cont
llvmDataLet x (_, DataFloat16 f) cont =
  llvmUncastLet x (LLVMDataFloat16 f) (LowTypeFloat FloatSize16) cont
llvmDataLet x (_, DataFloat32 f) cont =
  llvmUncastLet x (LLVMDataFloat32 f) (LowTypeFloat FloatSize32) cont
llvmDataLet x (_, DataFloat64 f) cont =
  llvmUncastLet x (LLVMDataFloat64 f) (LowTypeFloat FloatSize64) cont
llvmDataLet x (_, DataArrayIntro k lds) cont = do
  ds <- reorder lds
  let elemType = arrayKindToLowType k
  let arrayType = LowTypeArrayPtr (length ds) elemType
  storeContent x elemType arrayType ds cont

reorder :: [(Identifier, a)] -> WithEnv [a]
reorder lds = do
  let (ls, ds) = unzip lds
  is <- mapM getEpsilonNum ls
  return $ map snd $ sortBy (\(i, _) (j, _) -> i `compare` j) $ zip is ds

llvmDataLet' :: [(Identifier, DataPlus)] -> LLVM -> WithEnv LLVM
llvmDataLet' [] cont = return cont
llvmDataLet' ((x, d):rest) cont = do
  cont' <- llvmDataLet' rest cont
  llvmDataLet x d cont'

-- returns Nothing iff the branch list is empty
constructSwitch :: [(Case, CodePlus)] -> WithEnv (Maybe (LLVM, [(Int, LLVM)]))
constructSwitch [] = return Nothing
constructSwitch [(CaseLabel _, code)] = do
  code' <- llvmCode code
  return $ Just (code', [])
constructSwitch ((CaseLabel x, code):rest) = do
  i <- getEpsilonNum x
  code' <- llvmCode code
  m <- constructSwitch rest
  return $ do
    (defaultCase, caseList) <- m
    return (defaultCase, (i, code') : caseList)
constructSwitch ((CaseDefault, code):_) = do
  code' <- llvmCode code
  return $ Just (code', [])

llvmCodeEpsilonElim :: DataPlus -> [(Case, CodePlus)] -> WithEnv LLVM
llvmCodeEpsilonElim v branchList = do
  m <- constructSwitch branchList
  case m of
    Nothing -> return LLVMUnreachable
    Just (defaultCase, caseList) -> do
      let t = LowTypeSignedInt 64
      (cast, castThen) <- llvmCast v t
      castThen $ LLVMSwitch (cast, t) defaultCase caseList

storeContent ::
     Identifier -> LowType -> LowType -> [DataPlus] -> LLVM -> WithEnv LLVM
storeContent reg elemType aggPtrType ds cont = do
  (cast, castThen) <- llvmCast (Nothing, DataUpsilon reg) aggPtrType
  cont' <- storeContent' cast aggPtrType elemType (zip [0 ..] ds) cont
  cont'' <- castThen $ cont'
  let size = lowTypeToAllocSize aggPtrType
  return $ LLVMLet reg (LLVMAlloc size) cont''

storeContent' ::
     LLVMData -- base pointer
  -> LowType -- the type of base pointer (like [n x u8], {i8*, i8*}, etc.)
  -> LowType -- the type of elements (like u8, i8*, etc.)
  -> [(Integer, DataPlus)] -- [(the index of an element, the element to be stored)]
  -> LLVM -- continuation
  -> WithEnv LLVM
storeContent' _ _ _ [] cont = return cont
storeContent' bp bt et ((i, d):ids) cont = do
  cont' <- storeContent' bp bt et ids cont
  (locName, loc) <- newDataLocal "loc"
  hole <- newNameWith "tmp"
  (cast, castThen) <- llvmCast d et
  castThen $
    LLVMLet locName (LLVMGetElementPtr (bp, bt) (LLVMDataIntS 64 i)) $
    LLVMLet hole (LLVMStore (cast, et) (loc, et)) cont'

toFunPtrType :: [a] -> LowType
toFunPtrType xs = do
  LowTypeFunctionPtr (map (const voidPtr) xs) voidPtr

toStructPtrType :: Int -> LowType
toStructPtrType i = LowTypeStructPtr $ map (const voidPtr) [1 .. i]

newDataLocal :: Identifier -> WithEnv (Identifier, LLVMData)
newDataLocal name = do
  x <- newNameWith name
  return $ (x, LLVMDataLocal x)

lowTypeToAllocSize :: LowType -> AllocSize
lowTypeToAllocSize (LowTypeSignedInt i) = AllocSizeExact $ lowTypeToAllocSize' i
lowTypeToAllocSize (LowTypeUnsignedInt i) =
  AllocSizeExact $ lowTypeToAllocSize' i
lowTypeToAllocSize (LowTypeFloat size) =
  AllocSizeExact $ lowTypeToAllocSize' $ sizeAsInt size
lowTypeToAllocSize LowTypeVoidPtr = AllocSizePtrList 1
lowTypeToAllocSize (LowTypeFunctionPtr _ _) = AllocSizePtrList 1
lowTypeToAllocSize (LowTypeStructPtr ts) = AllocSizePtrList $ length ts
lowTypeToAllocSize (LowTypeArrayPtr i t) =
  case lowTypeToAllocSize t of
    AllocSizeExact s -> AllocSizeExact $ s * i
    AllocSizePtrList s -> AllocSizePtrList $ s * i -- shouldn't occur

lowTypeToAllocSize' :: Int -> Int
lowTypeToAllocSize' i = do
  let (q, r) = quotRem i 8
  if r == 0
    then q
    else q + 1
