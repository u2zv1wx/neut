{-# LANGUAGE OverloadedStrings #-}

module LLVM
  ( toLLVM
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

import Data.Basic
import Data.Code
import Data.Env
import Data.LLVM

toLLVM :: CodePlus -> WithEnv LLVM
toLLVM mainTerm = do
  penv <- gets codeEnv
  forM_ (Map.toList penv) $ \(name, (args, e)) -> do
    llvm <- llvmCode e
    insLLVMEnv name args llvm
  l <- llvmCode mainTerm
  -- the result of "main" must be i64, not i8*
  (result, resultVar) <- newDataUpsilonWith "result"
  (cast, castThen) <- llvmCast (Just "cast") resultVar (LowTypeIntS 64)
  castResult <- castThen (LLVMReturn cast)
  -- let result: i8* := (main-term) in {cast result to i64}
  return $ commConv result l $ castResult

llvmCode :: CodePlus -> WithEnv LLVM
llvmCode (m, CodeTheta theta) = llvmCodeTheta m theta
llvmCode (_, CodePiElimDownElim v ds) = do
  (xs, vs) <- unzip <$> mapM (\d -> newDataLocal $ takeBaseName d) ds
  (fun, castThen) <- llvmCast (Just $ takeBaseName v) v $ toFunPtrType ds
  castThenCall <- castThen $ LLVMCall fun vs
  llvmDataLet' (zip xs ds) $ castThenCall
llvmCode (_, CodeSigmaElim Nothing xts v e) = do
  let xs = map fst xts
  let structPtrType = toStructPtrType $ length xs
  let idxList = map (\i -> (LLVMDataInt i, i32)) [0 ..]
  ys <- mapM newNameWith xs
  loadContent v structPtrType (zip idxList (zip ys xs)) voidPtr e
llvmCode (_, CodeSigmaElim (Just k) xts v e) = do
  let xs = map fst xts
  let et = arrayKindToLowType k -- elem type
  let bt = LowTypeArrayPtr (toInteger $ length xs) et -- base pointer type  ([(length xs) x ARRAY_ELEM_TYPE])
  let idxList = map (\i -> (LLVMDataInt i, i32)) [0 ..]
  ys <- mapM newNameWith xs
  loadContent v bt (zip idxList (zip ys xs)) et e
llvmCode (_, CodeUpIntro d) = do
  result <- newNameWith $ takeBaseName d
  llvmDataLet result d $ LLVMReturn $ LLVMDataLocal result
llvmCode (_, CodeUpElim x e1 e2) = do
  e1' <- llvmCode e1
  e2' <- llvmCode e2
  return $ commConv x e1' e2'
llvmCode (_, CodeEnumElim v branchList) = llvmCodeEnumElim v branchList
llvmCode (_, CodeArrayElim k d1 d2) = do
  result <- newNameWith "array-elim-ans"
  resultTmp <- newNameWith "array-elim-ans-tmp"
  let et = arrayKindToLowType k -- elem type
  let bt = LowTypeArrayPtr 0 et -- base pointer type (e.g. [0 x u8]*)
  (cast, castThen) <- llvmCast (Just "array-idx") d2 $ LowTypeIntS 64 -- enum ~> i64
  loadThenFreeThenCont <-
    loadContent d1 bt [((cast, i64), (resultTmp, result))] et (retUp result)
  castThen loadThenFreeThenCont

uncastList :: LowType -> [(Identifier, Identifier)] -> CodePlus -> WithEnv LLVM
uncastList _ [] e = llvmCode e
uncastList et ((y, x):yxs) e = do
  e' <- uncastList et yxs e
  llvmUncastLet x (LLVMDataLocal y) et e'

-- llvmUncastLet :: Identifier -> LLVMData -> LowType -> LLVM -> WithEnv LLVM
-- llvmUncast :: Maybe Identifier -> LLVMData -> LowType -> WithEnv LLVM
takeBaseName :: DataPlus -> Identifier
takeBaseName (_, DataTheta x) = x
takeBaseName (_, DataUpsilon x) = x
takeBaseName (_, DataSigmaIntro Nothing []) = "unit"
takeBaseName (_, DataSigmaIntro Nothing ds) =
  "struct" <> T.pack (show (length ds))
takeBaseName (_, DataSigmaIntro (Just _) ds) =
  "array" <> T.pack (show (length ds))
takeBaseName (_, DataIntS size _) = "i" <> T.pack (show size)
takeBaseName (_, DataIntU size _) = "u" <> T.pack (show size)
takeBaseName (_, DataFloat16 _) = "half"
takeBaseName (_, DataFloat32 _) = "float"
takeBaseName (_, DataFloat64 _) = "double"
takeBaseName (_, DataEnumIntro _) = "i64"

-- takeBaseName (_, DataArrayIntro _ ds) = "array" <> T.pack (show (length ds))
takeBaseName' :: LLVMData -> Identifier
takeBaseName' (LLVMDataLocal x) = x
takeBaseName' (LLVMDataGlobal x) = x
takeBaseName' (LLVMDataInt _) = "int"
takeBaseName' (LLVMDataFloat16 _) = "half"
takeBaseName' (LLVMDataFloat32 _) = "float"
takeBaseName' (LLVMDataFloat64 _) = "double"
takeBaseName' LLVMDataNull = "null"

retUp :: Identifier -> CodePlus
retUp result = (emptyMeta, CodeUpIntro (emptyMeta, DataUpsilon result))

loadContent ::
     DataPlus -- base pointer
  -> LowType -- the type of base pointer
  -> [((LLVMData, LowType), (Identifier, Identifier))] -- [(the index of an element, the variable to load the element)]
  -> LowType -- the type of elements
  -> CodePlus -- continuation
  -> WithEnv LLVM
loadContent v bt iyxs et cont = do
  let ixs = map (\(i, (y, _)) -> (i, y)) iyxs
  (bp, castThen) <- llvmCast (Just $ takeBaseName v) v bt
  let yxs = map (\(_, yx) -> yx) iyxs
  uncastThenCont <- uncastList et yxs cont
  extractThenFreeThenUncastThenCont <- loadContent' bp bt et ixs uncastThenCont
  castThen extractThenFreeThenUncastThenCont

loadContent' ::
     LLVMData -- base pointer
  -> LowType -- the type of base pointer
  -> LowType -- the type of elements
  -> [((LLVMData, LowType), Identifier)] -- [(the index of an element, the variable to keep the loaded content)]
  -> LLVM -- continuation
  -> WithEnv LLVM
loadContent' bp bt _ [] cont = do
  l <- llvmUncast (Just $ takeBaseName' bp) bp bt
  tmp <- newNameWith' $ Just $ takeBaseName' bp
  return $ commConv tmp l $ LLVMCont (LLVMOpFree (LLVMDataLocal tmp)) cont
loadContent' bp bt et ((i, x):xis) cont = do
  cont' <- loadContent' bp bt et xis cont
  (posName, pos) <- newDataLocal' (Just x)
  return $
    LLVMLet
      posName
      (LLVMOpGetElementPtr (bp, bt) [(LLVMDataInt 0, LowTypeIntS 32), i]) $
    LLVMLet x (LLVMOpLoad pos et) cont'

llvmCodeTheta :: Meta -> Theta -> WithEnv LLVM
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
    LLVMLet res (LLVMOpSysCall num' vs) $ LLVMReturn (LLVMDataLocal res)

llvmCodeUnaryOp :: UnaryOp -> LowType -> LowType -> DataPlus -> WithEnv LLVM
llvmCodeUnaryOp op domType codType d = do
  (x, castThen) <- llvmCast (Just "unary-op") d domType
  result <- newNameWith "unary-op-result"
  uncast <- llvmUncast (Just result) (LLVMDataLocal result) codType
  castThen $ LLVMLet result (LLVMOpUnaryOp (op, domType) x) uncast

llvmCodeBinaryOp ::
     BinaryOp -> LowType -> LowType -> DataPlus -> DataPlus -> WithEnv LLVM
llvmCodeBinaryOp op domType codType v1 v2 = do
  (x1, cast1then) <- llvmCast (Just "binary-op-fst") v1 domType
  (x2, cast2then) <- llvmCast (Just "binary-op-snd") v2 domType
  result <- newNameWith "binary-op-result"
  uncast <- llvmUncast (Just result) (LLVMDataLocal result) codType
  (cast1then >=> cast2then) $
    LLVMLet result (LLVMOpBinaryOp (op, domType) x1 x2) uncast

llvmCast ::
     Maybe Identifier
  -> DataPlus
  -> LowType
  -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCast mName v lowType@(LowTypeIntS _) = llvmCastInt mName v lowType
llvmCast mName v lowType@(LowTypeIntU _) = llvmCastInt mName v lowType
llvmCast mName v (LowTypeFloat i) = llvmCastFloat mName v i
llvmCast mName v ptrType = do
  tmp <- newNameWith' mName
  x <- newNameWith' mName
  return
    ( LLVMDataLocal x
    , \cont -> do
        llvmDataLet tmp v $
          LLVMLet x (LLVMOpBitcast (LLVMDataLocal tmp) voidPtr ptrType) cont)

llvmCastInt ::
     Maybe Identifier -- base name for newly created variables
  -> DataPlus
  -> LowType
  -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastInt mName v lowType = do
  x <- newNameWith' mName
  y <- newNameWith' mName
  return
    ( LLVMDataLocal y
    , \cont -> do
        llvmDataLet x v $
          LLVMLet y (LLVMOpPointerToInt (LLVMDataLocal x) voidPtr lowType) $
          cont)

llvmCastFloat ::
     Maybe Identifier -- base name for newly created variables
  -> DataPlus
  -> FloatSize
  -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastFloat mName v size = do
  let floatType = LowTypeFloat size
  let intType = LowTypeIntS $ sizeAsInt size
  (xName, x) <- newDataLocal' mName
  (yName, y) <- newDataLocal' mName
  z <- newNameWith' mName
  return
    ( LLVMDataLocal z
    , \cont -> do
        llvmDataLet xName v $
          LLVMLet yName (LLVMOpPointerToInt x voidPtr intType) $
          LLVMLet z (LLVMOpBitcast y intType floatType) cont)

-- uncast: {some-concrete-type} -> voidPtr
llvmUncast :: Maybe Identifier -> LLVMData -> LowType -> WithEnv LLVM
llvmUncast mName result lowType@(LowTypeIntS _) =
  llvmUncastInt mName result lowType
llvmUncast mName result lowType@(LowTypeIntU _) =
  llvmUncastInt mName result lowType
llvmUncast mName result (LowTypeFloat i) = llvmUncastFloat mName result i
llvmUncast mName result ptrType = do
  x <- newNameWith' mName
  return $
    LLVMLet x (LLVMOpBitcast result ptrType voidPtr) $
    LLVMReturn (LLVMDataLocal x)

llvmUncastInt :: Maybe Identifier -> LLVMData -> LowType -> WithEnv LLVM
llvmUncastInt mName result lowType = do
  x <- newNameWith' mName
  return $
    LLVMLet x (LLVMOpIntToPointer result lowType voidPtr) $
    LLVMReturn (LLVMDataLocal x)

llvmUncastFloat :: Maybe Identifier -> LLVMData -> FloatSize -> WithEnv LLVM
llvmUncastFloat mName floatResult i = do
  let floatType = LowTypeFloat i
  let intType = LowTypeIntS $ sizeAsInt i
  tmp <- newNameWith' mName
  x <- newNameWith' mName
  return $
    LLVMLet tmp (LLVMOpBitcast floatResult floatType intType) $
    LLVMLet x (LLVMOpIntToPointer (LLVMDataLocal tmp) intType voidPtr) $
    LLVMReturn (LLVMDataLocal x)

llvmUncastLet :: Identifier -> LLVMData -> LowType -> LLVM -> WithEnv LLVM
llvmUncastLet x d lowType cont = do
  l <- llvmUncast (Just x) d lowType
  return $ commConv x l cont

-- LLVMLet x e1' e2'
-- `llvmDataLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
llvmDataLet :: Identifier -> DataPlus -> LLVM -> WithEnv LLVM
llvmDataLet x (_, DataTheta y) cont = do
  cenv <- gets codeEnv
  case Map.lookup y cenv of
    Nothing
      | y == "fork" -> llvmUncastLet x (LLVMDataGlobal y) (toFunPtrType []) cont
    Nothing -> throwError $ "no such global label defined: " <> y
    Just (args, _) ->
      llvmUncastLet x (LLVMDataGlobal y) (toFunPtrType args) cont
llvmDataLet x (_, DataUpsilon y) cont =
  llvmUncastLet x (LLVMDataLocal y) voidPtr cont
llvmDataLet reg (_, DataSigmaIntro Nothing ds) cont =
  storeContent reg voidPtr (toStructPtrType $ length ds) ds cont
llvmDataLet x (_, DataSigmaIntro (Just k) ds) cont = do
  let elemType = arrayKindToLowType k
  let arrayType = LowTypeArrayPtr (toInteger $ length ds) elemType
  storeContent x elemType arrayType ds cont
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

sysCallNumAsInt :: SysCall -> WithEnv Integer
sysCallNumAsInt num = do
  targetOS <- getOS
  case targetOS of
    OSLinux ->
      case num of
        SysCallRead -> return 0
        SysCallWrite -> return 1
        SysCallExit -> return 60
        SysCallOpen -> return 2
        SysCallClose -> return 3
        SysCallFork -> return 57
    OSDarwin ->
      case num of
        SysCallRead -> return 0x2000003
        SysCallWrite -> return 0x2000004
        SysCallExit -> return 0x2000001
        SysCallOpen -> return 0x2000005
        SysCallClose -> return 0x2000006
        SysCallFork -> return 0x2000002

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
      (cast, castThen) <- llvmCast (Just "enum-base") v t
      castThen $ LLVMSwitch (cast, t) defaultCase caseList

storeContent ::
     Identifier -> LowType -> LowType -> [DataPlus] -> LLVM -> WithEnv LLVM
storeContent reg elemType aggPtrType ds cont = do
  (cast, castThen) <-
    llvmCast (Just reg) (emptyMeta, DataUpsilon reg) aggPtrType
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
      (c, cVar) <- newDataLocal $ "sizeof-" <> reg
      (i, iVar) <- newDataLocal $ "sizeof-" <> reg
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
  (locName, loc) <- newDataLocal $ takeBaseName d <> "-location"
  (cast, castThen) <- llvmCast (Just $ takeBaseName d) d et
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

newDataLocal' :: Maybe Identifier -> WithEnv (Identifier, LLVMData)
newDataLocal' mName = do
  x <- newNameWith' mName
  return $ (x, LLVMDataLocal x)

lowTypeToAllocSize :: LowType -> AllocSize
lowTypeToAllocSize (LowTypeIntS i) = AllocSizeExact $ lowTypeToAllocSize' i
lowTypeToAllocSize (LowTypeIntU i) = AllocSizeExact $ lowTypeToAllocSize' i
lowTypeToAllocSize (LowTypeFloat size) =
  AllocSizeExact $ lowTypeToAllocSize' $ sizeAsInt size
lowTypeToAllocSize LowTypeVoidPtr = AllocSizePtrList 1
lowTypeToAllocSize (LowTypeFunctionPtr _ _) = AllocSizePtrList 1
lowTypeToAllocSize (LowTypeStructPtr ts) =
  AllocSizePtrList $ toInteger $ length ts
lowTypeToAllocSize (LowTypeArrayPtr i t) =
  case lowTypeToAllocSize t of
    AllocSizeExact s -> AllocSizeExact $ s * i
    AllocSizePtrList s -> AllocSizePtrList $ s * i -- shouldn't occur
lowTypeToAllocSize LowTypeIntS64Ptr = AllocSizePtrList 1

i64 :: LowType
i64 = LowTypeIntS 64

i32 :: LowType
i32 = LowTypeIntS 32

newNameWith' :: Maybe Identifier -> WithEnv Identifier
newNameWith' Nothing = newNameWith "var"
newNameWith' (Just name) = newNameWith name

insLLVMEnv :: Identifier -> [Identifier] -> LLVM -> WithEnv ()
insLLVMEnv funName args e =
  modify (\env -> env {llvmEnv = Map.insert funName (args, e) (llvmEnv env)})

getCodType :: UnaryOp -> Maybe LowType
getCodType (UnaryOpTrunc lowType) = Just lowType
getCodType (UnaryOpZext lowType) = Just lowType
getCodType (UnaryOpSext lowType) = Just lowType
getCodType (UnaryOpFpExt lowType) = Just lowType
getCodType (UnaryOpTo lowType) = Just lowType
getCodType _ = Nothing

isArithOp :: BinaryOp -> Bool
isArithOp BinaryOpAdd = True
isArithOp BinaryOpSub = True
isArithOp BinaryOpMul = True
isArithOp BinaryOpDiv = True
isArithOp BinaryOpRem = True
isArithOp BinaryOpShl = True
isArithOp BinaryOpLshr = True
isArithOp BinaryOpAshr = True
isArithOp BinaryOpAnd = True
isArithOp BinaryOpOr = True
isArithOp BinaryOpXor = True
isArithOp _ = False

isCompareOp :: BinaryOp -> Bool
isCompareOp BinaryOpEQ = True
isCompareOp BinaryOpNE = True
isCompareOp BinaryOpGT = True
isCompareOp BinaryOpGE = True
isCompareOp BinaryOpLT = True
isCompareOp BinaryOpLE = True
isCompareOp _ = False

-- commutative conversion
commConv :: Identifier -> LLVM -> LLVM -> LLVM
commConv x (LLVMReturn d) cont =
  LLVMLet x (LLVMOpBitcast d voidPtr voidPtr) cont -- nop
commConv x (LLVMLet y op cont1) cont2 = LLVMLet y op $ commConv x cont1 cont2
commConv x (LLVMCont op cont1) cont2 = LLVMCont op $ commConv x cont1 cont2
commConv x (LLVMSwitch (d, t) defaultCase caseList) cont2 = do
  let (ds, es) = unzip caseList
  let es' = map (\e -> commConv x e cont2) es
  let caseList' = zip ds es'
  let defaultCase' = commConv x defaultCase cont2
  LLVMSwitch (d, t) defaultCase' caseList'
commConv x (LLVMCall d ds) cont2 = LLVMLet x (LLVMOpCall d ds) cont2
commConv _ LLVMUnreachable _ = LLVMUnreachable
