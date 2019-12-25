module LLVM
  ( toLLVM
  ) where

import Control.Monad.Except
import Control.Monad.State
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
  l <- llvmCode mainTerm
  (result, resultVar) <- newDataLocal "result"
  (cast, castVar) <- newDataLocal "cast-result"
  let intType = LowTypeIntS 64
  return $
    commConv result l $
    LLVMLet cast (LLVMOpPointerToInt resultVar voidPtr intType) $
    LLVMReturn castVar

llvmCode :: CodePlus -> WithEnv LLVM
llvmCode (m, CodeTheta theta) = llvmCodeTheta m theta
llvmCode (_, CodePiElimDownElim v ds) = do
  (xs, vs) <- unzip <$> mapM (const $ newDataLocal "pi-elim-arg") ds
  (fun, castThen) <- llvmCast v $ toFunPtrType ds
  castThenCall <- castThen $ LLVMCall fun vs
  llvmDataLet' (zip xs ds) $ castThenCall
llvmCode (_, CodeSigmaElim xs v e) = do
  let structPtrType = toStructPtrType $ length xs
  let idxList = map (\i -> (LLVMDataInt i, i32)) [0 ..]
  loadContent v structPtrType (zip idxList xs) voidPtr e
llvmCode (_, CodeUpIntro d) = do
  result <- newNameWith "up-intro-ans"
  llvmDataLet result d $ LLVMReturn $ LLVMDataLocal result
llvmCode (_, CodeUpElim x e1 e2) = do
  e1' <- llvmCode e1
  e2' <- llvmCode e2
  return $ commConv x e1' e2'
llvmCode (_, CodeEnumElim v branchList) = llvmCodeEnumElim v branchList
llvmCode (_, CodeArrayElim k d1 d2) = do
  result <- newNameWith "array-elim-ans"
  let et = arrayKindToLowType k -- elem type
  let bt = LowTypeArrayPtr 0 et -- base pointer type
  (cast, castThen) <- llvmCast d2 $ LowTypeIntS 64 -- enum ~> i64
  loadThenFreeThenCont <-
    loadContent d1 bt [((cast, i64), result)] et (retUp result)
  castThen loadThenFreeThenCont

retUp :: Identifier -> CodePlus
retUp result = (Nothing, CodeUpIntro (Nothing, DataUpsilon result))

loadContent ::
     DataPlus -- base pointer
  -> LowType -- the type of base pointer
  -> [((LLVMData, LowType), Identifier)] -- [(the index of an element, the variable to load the element)]
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
  -> [((LLVMData, LowType), Identifier)] -- [(the index of an element, the variable to keep the loaded content)]
  -> LLVM -- continuation
  -> WithEnv LLVM
loadContent' bp bt _ [] cont = do
  l <- llvmUncast bp bt
  tmp <- newNameWith "load-content-base"
  return $ commConv tmp l $ LLVMCont (LLVMOpFree (LLVMDataLocal tmp)) cont
loadContent' bp bt et ((i, x):xis) cont = do
  cont' <- loadContent' bp bt et xis cont
  (posName, pos) <- newDataLocal "load-content-pos"
  return $
    LLVMLet
      posName
      (LLVMOpGetElementPtr (bp, bt) [(LLVMDataInt 0, LowTypeIntS 32), i]) $
    LLVMLet x (LLVMOpLoad pos et) cont'

llvmCodeTheta :: CodeMeta -> Theta -> WithEnv LLVM
llvmCodeTheta _ (ThetaUnaryOp op lowType v)
  | UnaryOpNeg <- op = llvmCodeUnaryOp op lowType lowType v
  | Just codType <- getCodType op = llvmCodeUnaryOp op lowType codType v
  | otherwise = throwError "llvmCodeTheta.ThetaUnaryOp"
llvmCodeTheta _ (ThetaBinaryOp op lowType v1 v2)
  | isArithOp op = llvmCodeBinaryOp op lowType lowType v1 v2
  | isCompareOp op = llvmCodeBinaryOp op lowType (LowTypeIntS 1) v1 v2
  | otherwise = throwError "llvmCodeTheta.ThetaBinaryOp"
llvmCodeTheta _ (ThetaSysCall num args) = do
  (xs, vs) <- unzip <$> mapM (const $ newDataLocal "sys-call-arg") args
  res <- newNameWith "result"
  num' <- sysCallNumAsInt num
  llvmDataLet' (zip xs args) $
    LLVMLet res (LLVMOpSysCall $ num' : vs) $ LLVMReturn (LLVMDataLocal res)

llvmCodeUnaryOp :: UnaryOp -> LowType -> LowType -> DataPlus -> WithEnv LLVM
llvmCodeUnaryOp op domType codType d = do
  (x, castThen) <- llvmCast d domType
  result <- newNameWith "unary-op-result"
  uncast <- llvmUncast (LLVMDataLocal result) codType
  castThen $ LLVMLet result (LLVMOpUnaryOp (op, domType) x) uncast

llvmCodeBinaryOp ::
     BinaryOp -> LowType -> LowType -> DataPlus -> DataPlus -> WithEnv LLVM
llvmCodeBinaryOp op domType codType v1 v2 = do
  (x1, cast1then) <- llvmCast v1 domType
  (x2, cast2then) <- llvmCast v2 domType
  result <- newNameWith "binary-op-result"
  uncast <- llvmUncast (LLVMDataLocal result) codType
  (cast1then >=> cast2then) $
    LLVMLet result (LLVMOpBinaryOp (op, domType) x1 x2) uncast

llvmCast :: DataPlus -> LowType -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCast v lowType@(LowTypeIntS _) = llvmCastInt v lowType
llvmCast v lowType@(LowTypeIntU _) = llvmCastInt v lowType
llvmCast v (LowTypeFloat i) = llvmCastFloat v i
llvmCast v ptrType = do
  x <- newNameWith "cast-var"
  return
    ( LLVMDataLocal x
    , \cont -> do
        tmp <- newNameWith "cast-tmp-var"
        llvmDataLet tmp v $
          LLVMLet x (LLVMOpBitcast (LLVMDataLocal tmp) voidPtr ptrType) cont)

llvmCastInt :: DataPlus -> LowType -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastInt v lowType = do
  x <- newNameWith "cast-int-arg"
  y <- newNameWith "cast-int"
  return
    ( LLVMDataLocal y
    , \cont -> do
        llvmDataLet x v $
          LLVMLet y (LLVMOpPointerToInt (LLVMDataLocal x) voidPtr lowType) $
          cont)

llvmCastFloat ::
     DataPlus -> FloatSize -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastFloat v size = do
  let floatType = LowTypeFloat size
  let intType = LowTypeIntS $ sizeAsInt size
  (xName, x) <- newDataLocal "cast-float-arg"
  (yName, y) <- newDataLocal "cast-float-tmp"
  z <- newNameWith "cast-float"
  return
    ( LLVMDataLocal z
    , \cont -> do
        llvmDataLet xName v $
          LLVMLet yName (LLVMOpPointerToInt x voidPtr intType) $
          LLVMLet z (LLVMOpBitcast y intType floatType) cont)

-- uncast: {some-concrete-type} -> voidPtr
llvmUncast :: LLVMData -> LowType -> WithEnv LLVM
llvmUncast result lowType@(LowTypeIntS _) = llvmUncastInt result lowType
llvmUncast result lowType@(LowTypeIntU _) = llvmUncastInt result lowType
llvmUncast result (LowTypeFloat i) = llvmUncastFloat result i
llvmUncast result ptrType = do
  x <- newNameWith "uncast-result"
  return $
    LLVMLet x (LLVMOpBitcast result ptrType voidPtr) $
    LLVMReturn (LLVMDataLocal x)

llvmUncastInt :: LLVMData -> LowType -> WithEnv LLVM
llvmUncastInt result lowType = do
  x <- newNameWith "uncast-int-result"
  return $
    LLVMLet x (LLVMOpIntToPointer result lowType voidPtr) $
    LLVMReturn (LLVMDataLocal x)

llvmUncastFloat :: LLVMData -> FloatSize -> WithEnv LLVM
llvmUncastFloat floatResult i = do
  let floatType = LowTypeFloat i
  let intType = LowTypeIntS $ sizeAsInt i
  tmp <- newNameWith "uncast-float-tmp"
  x <- newNameWith "uncast-float-result"
  return $
    LLVMLet tmp (LLVMOpBitcast floatResult floatType intType) $
    LLVMLet x (LLVMOpIntToPointer (LLVMDataLocal tmp) intType voidPtr) $
    LLVMReturn (LLVMDataLocal x)

llvmUncastLet :: Identifier -> LLVMData -> LowType -> LLVM -> WithEnv LLVM
llvmUncastLet x d lowType cont = do
  l <- llvmUncast d lowType
  return $ commConv x l cont

-- LLVMLet x e1' e2'
-- `llvmDataLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
llvmDataLet :: Identifier -> DataPlus -> LLVM -> WithEnv LLVM
llvmDataLet x (_, DataTheta y) cont = do
  penv <- gets codeEnv
  case lookup y penv of
    Nothing -> throwError $ "no such global label defined: " ++ y -- FIXME
    Just (args, _) ->
      llvmUncastLet x (LLVMDataGlobal y) (toFunPtrType args) cont
llvmDataLet x (_, DataUpsilon y) cont =
  llvmUncastLet x (LLVMDataLocal y) voidPtr cont
llvmDataLet reg (_, DataSigmaIntro ds) cont = do
  storeContent reg voidPtr (toStructPtrType $ length ds) ds cont
llvmDataLet x (_, DataIntS j i) cont =
  llvmUncastLet x (LLVMDataInt i) (LowTypeIntS j) cont
llvmDataLet x (_, DataIntU j i) cont =
  llvmUncastLet x (LLVMDataInt i) (LowTypeIntU j) cont
llvmDataLet x (_, DataFloat16 f) cont =
  llvmUncastLet x (LLVMDataFloat16 f) (LowTypeFloat FloatSize16) cont
llvmDataLet x (_, DataFloat32 f) cont =
  llvmUncastLet x (LLVMDataFloat32 f) (LowTypeFloat FloatSize32) cont
llvmDataLet x (_, DataFloat64 f) cont =
  llvmUncastLet x (LLVMDataFloat64 f) (LowTypeFloat FloatSize64) cont
llvmDataLet x (m, DataEnumIntro labelOrNat) cont = do
  i <- enumValueToInteger labelOrNat
  llvmDataLet x (m, DataIntS 64 i) cont
llvmDataLet x (_, DataArrayIntro k lds) cont = do
  ds <- reorder lds
  let elemType = arrayKindToLowType k
  let arrayType = LowTypeArrayPtr (length ds) elemType
  storeContent x elemType arrayType ds cont

reorder :: [(EnumValue, a)] -> WithEnv [a]
reorder lds = do
  let (ls, ds) = unzip lds
  is <- mapM enumValueToInteger ls
  return $ map snd $ sortBy (\(i, _) (j, _) -> i `compare` j) $ zip is ds

enumValueToInteger :: EnumValue -> WithEnv Integer
enumValueToInteger labelOrNat =
  case labelOrNat of
    EnumValueLabel l -> toInteger <$> getEnumNum l
    EnumValueNatNum _ j -> return $ toInteger j

sysCallNumAsInt :: SysCall -> WithEnv LLVMData
sysCallNumAsInt num = do
  targetOS <- getOS
  case targetOS of
    OSLinux ->
      case num of
        SysCallWrite -> return $ LLVMDataInt 1
    OSDarwin ->
      case num of
        SysCallWrite -> return $ LLVMDataInt 0x2000004

llvmDataLet' :: [(Identifier, DataPlus)] -> LLVM -> WithEnv LLVM
llvmDataLet' [] cont = return cont
llvmDataLet' ((x, d):rest) cont = do
  cont' <- llvmDataLet' rest cont
  llvmDataLet x d cont'

-- returns Nothing iff the branch list is empty
constructSwitch :: [(Case, CodePlus)] -> WithEnv (Maybe (LLVM, [(Int, LLVM)]))
constructSwitch [] = return Nothing
constructSwitch [(CaseValue _, code)] = do
  code' <- llvmCode code
  return $ Just (code', [])
constructSwitch ((CaseValue l, code):rest) = do
  i <- fromInteger <$> enumValueToInteger l
  code' <- llvmCode code
  m <- constructSwitch rest
  return $ do
    (defaultCase, caseList) <- m
    return (defaultCase, (i, code') : caseList)
constructSwitch ((CaseDefault, code):_) = do
  code' <- llvmCode code
  return $ Just (code', [])

llvmCodeEnumElim :: DataPlus -> [(Case, CodePlus)] -> WithEnv LLVM
llvmCodeEnumElim v branchList = do
  m <- constructSwitch branchList
  case m of
    Nothing -> return LLVMUnreachable
    Just (defaultCase, caseList) -> do
      let t = LowTypeIntS 64
      (cast, castThen) <- llvmCast v t
      castThen $ LLVMSwitch (cast, t) defaultCase caseList

storeContent ::
     Identifier -> LowType -> LowType -> [DataPlus] -> LLVM -> WithEnv LLVM
storeContent reg elemType aggPtrType ds cont = do
  (cast, castThen) <- llvmCast (Nothing, DataUpsilon reg) aggPtrType
  storeThenCont <- storeContent' cast aggPtrType elemType (zip [0 ..] ds) cont
  castThenStoreThenCont <- castThen $ storeThenCont
  -- FIXME: getelementptrでsizeofを実現する方式を使えばallocsizeを計算する必要はそもそもないはず？
  case lowTypeToAllocSize aggPtrType of
    AllocSizeExact i ->
      return $
      LLVMLet
        reg
        (LLVMOpAlloc (LLVMDataInt (toInteger i)))
        castThenStoreThenCont
    AllocSizePtrList n -> do
      (c, cVar) <- newDataLocal "store-ptr-cast"
      (i, iVar) <- newDataLocal "store-ptr-size"
      -- Use getelementptr to realize `sizeof`. More info:
      --   http://nondot.org/sabre/LLVMNotes/SizeOf-OffsetOf-VariableSizedStructs.txt
      return $
        LLVMLet
          c
          (LLVMOpGetElementPtr
             (LLVMDataNull, LowTypeIntS64Ptr)
             [(LLVMDataInt (toInteger n), i64)]) $
        LLVMLet i (LLVMOpPointerToInt cVar LowTypeIntS64Ptr (LowTypeIntS 64)) $
        LLVMLet reg (LLVMOpAlloc iVar) castThenStoreThenCont

storeContent' ::
     LLVMData -- base pointer
  -> LowType -- the type of base pointer (like [n x u8]*, {i8*, i8*}*, etc.)
  -> LowType -- the type of elements (like u8, i8*, etc.)
  -> [(Integer, DataPlus)] -- [(the index of an element, the element to be stored)]
  -> LLVM -- continuation
  -> WithEnv LLVM
storeContent' _ _ _ [] cont = return cont
storeContent' bp bt et ((i, d):ids) cont = do
  cont' <- storeContent' bp bt et ids cont
  (locName, loc) <- newDataLocal "store-content-location"
  (cast, castThen) <- llvmCast d et
  let it = indexTypeOf bt
  castThen $
    LLVMLet
      locName
      (LLVMOpGetElementPtr (bp, bt) [(LLVMDataInt 0, i32), (LLVMDataInt i, it)]) $
    LLVMCont (LLVMOpStore et cast loc) cont'

indexTypeOf :: LowType -> LowType
indexTypeOf (LowTypeStructPtr _) = LowTypeIntS 32
indexTypeOf _ = LowTypeIntS 64

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
lowTypeToAllocSize (LowTypeIntS i) = AllocSizeExact $ lowTypeToAllocSize' i
lowTypeToAllocSize (LowTypeIntU i) = AllocSizeExact $ lowTypeToAllocSize' i
lowTypeToAllocSize (LowTypeFloat size) =
  AllocSizeExact $ lowTypeToAllocSize' $ sizeAsInt size
lowTypeToAllocSize LowTypeVoidPtr = AllocSizePtrList 1
lowTypeToAllocSize (LowTypeFunctionPtr _ _) = AllocSizePtrList 1
lowTypeToAllocSize (LowTypeStructPtr ts) = AllocSizePtrList $ length ts
lowTypeToAllocSize (LowTypeArrayPtr i t) =
  case lowTypeToAllocSize t of
    AllocSizeExact s -> AllocSizeExact $ s * i
    AllocSizePtrList s -> AllocSizePtrList $ s * i -- shouldn't occur
lowTypeToAllocSize LowTypeIntS64Ptr = AllocSizePtrList 1

lowTypeToAllocSize' :: Int -> Int
lowTypeToAllocSize' i = do
  let (q, r) = quotRem i 8
  if r == 0
    then q
    else q + 1

i64 :: LowType
i64 = LowTypeIntS 64

i32 :: LowType
i32 = LowTypeIntS 32
