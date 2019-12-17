module LLVM
  ( toLLVM
  ) where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.List (elemIndex)

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
llvmCode (_, CodeEpsilonElim xt v branchList) =
  llvmCodeEpsilonElim xt v branchList
llvmCode (_, CodePiElimDownElim v ds) = do
  f <- newNameWith "fun"
  xs <- mapM (const (newNameWith "arg")) ds
  cast <- newNameWith "cast"
  let funPtrType = toFunPtrType ds
  llvmDataLet' ((f, v) : zip xs ds) $
    LLVMLet cast (LLVMBitcast (LLVMDataLocal f) voidPtr funPtrType) $
    LLVMCall (LLVMDataLocal cast) (map LLVMDataLocal xs)
llvmCode (_, CodeSigmaElim xs v e) = do
  basePointer <- newNameWith "base"
  castedBasePointer <- newNameWith "castedBase"
  extractAndCont <-
    llvmCodeSigmaElim
      basePointer
      (zip xs [0 ..])
      castedBasePointer
      (length xs)
      e
  llvmDataLet basePointer v $
    LLVMLet
      castedBasePointer
      (LLVMBitcast
         (LLVMDataLocal basePointer)
         voidPtr
         (toStructPtrType [1 .. (length xs)]))
      extractAndCont
llvmCode (_, CodeUpIntro d) = do
  result <- newNameWith "ans"
  llvmDataLet result d $ LLVMReturn $ LLVMDataLocal result
llvmCode (_, CodeUpElim x e1 e2) = do
  e1' <- llvmCode e1
  e2' <- llvmCode e2
  return $ LLVMLet x e1' e2'

llvmCodeSigmaElim ::
     Identifier
  -> [(Identifier, Int)]
  -> Identifier
  -> Int
  -> CodePlus
  -> WithEnv LLVM
llvmCodeSigmaElim basePointer [] _ _ cont = do
  hole <- newNameWith "hole"
  cont' <- llvmCode cont
  return $ LLVMLet hole (LLVMFree (LLVMDataLocal basePointer)) cont'
llvmCodeSigmaElim basePointer ((x, i):xis) castedBasePointer n cont = do
  cont' <- llvmCodeSigmaElim basePointer xis castedBasePointer n cont
  loader <- newNameWith "loader"
  return $
    LLVMLet loader (LLVMGetElementPtr (LLVMDataLocal castedBasePointer) (i, n)) $
    LLVMLet x (LLVMLoad (LLVMDataLocal loader)) cont'

llvmCodeTheta :: CodeMeta -> Theta -> WithEnv LLVM
llvmCodeTheta _ (ThetaUnaryOp op lowType v) =
  case lowType of
    LowTypeFloat _
      | UnaryOpNeg <- op -> llvmCodeUnaryOp op lowType lowType v
      | Just codType <- getCodType op -> llvmCodeUnaryOp op lowType codType v
    _ -> throwError "llvmCodeTheta.ThetaUnaryOp"
llvmCodeTheta _ (ThetaBinaryOp op lowType v1 v2)
  | isArithOp op = llvmCodeBinaryOp op lowType lowType v1 v2
  | isCompareOp op = llvmCodeBinaryOp op lowType (LowTypeSignedInt 1) v1 v2
  | otherwise = throwError "llvmCodeTheta.ThetaBinaryOp"
llvmCodeTheta _ (ThetaPrint v) = do
  let t = LowTypeSignedInt 64
  p <- newNameWith "arg"
  c <- newNameWith "cast"
  llvmDataLet p v $
    LLVMLet c (LLVMPointerToInt (LLVMDataLocal p) voidPtr t) $
    LLVMPrint t (LLVMDataLocal c)

llvmCodeUnaryOp :: UnaryOp -> LowType -> LowType -> DataPlus -> WithEnv LLVM
llvmCodeUnaryOp op domType codType d = do
  (x, castThen) <- llvmCast d domType
  result <- newNameWith "result"
  uncast <- llvmUncast result codType
  castThen $ LLVMLet result (LLVMUnaryOp (op, domType) x) uncast

llvmCodeBinaryOp ::
     BinaryOp -> LowType -> LowType -> DataPlus -> DataPlus -> WithEnv LLVM
llvmCodeBinaryOp op domType codType v1 v2 = do
  (x1, cast1then) <- llvmCast v1 domType
  (x2, cast2then) <- llvmCast v2 domType
  result <- newNameWith "result"
  uncast <- llvmUncast result codType
  (cast1then >=> cast2then) $
    LLVMLet result (LLVMBinaryOp (op, domType) x1 x2) uncast

llvmCast :: DataPlus -> LowType -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCast v lowType@(LowTypeSignedInt _) = llvmCastToInt v lowType
llvmCast v lowType@(LowTypeUnsignedInt _) = llvmCastToInt v lowType
llvmCast v (LowTypeFloat i) = llvmCastToFloat v i
llvmCast _ _ = throwError "llvmCast"

llvmCastToInt :: DataPlus -> LowType -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastToInt v lowType = do
  x <- newNameWith "arg"
  y <- newNameWith "cast"
  return
    ( LLVMDataLocal y
    , \cont -> do
        llvmDataLet x v $
          LLVMLet y (LLVMPointerToInt (LLVMDataLocal x) voidPtr lowType) $ cont)

llvmCastToFloat :: DataPlus -> Int -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastToFloat v size = do
  let floatType = LowTypeFloat size
  let intType = LowTypeSignedInt size
  x <- newNameWith "arg"
  y <- newNameWith "tmp"
  z <- newNameWith "cast"
  return
    ( LLVMDataLocal z
    , \cont -> do
        llvmDataLet x v $
          LLVMLet y (LLVMPointerToInt (LLVMDataLocal x) voidPtr intType) $
          LLVMLet z (LLVMBitcast (LLVMDataLocal y) intType floatType) cont)

llvmUncast :: Identifier -> LowType -> WithEnv LLVM
llvmUncast result lowType@(LowTypeSignedInt _) =
  return $ llvmUncastInt result lowType
llvmUncast result lowType@(LowTypeUnsignedInt _) =
  return $ llvmUncastInt result lowType
llvmUncast result (LowTypeFloat i) = llvmUncastFloat result i
llvmUncast _ _ = throwError "llvmUncast"

llvmUncastInt :: Identifier -> LowType -> LLVM
llvmUncastInt result lowType =
  LLVMIntToPointer (LLVMDataLocal result) lowType voidPtr

llvmUncastFloat :: Identifier -> Int -> WithEnv LLVM
llvmUncastFloat floatResult i = do
  let floatType = LowTypeFloat i
  let intType = LowTypeSignedInt i
  tmp <- newNameWith "tmp"
  return $
    LLVMLet tmp (LLVMBitcast (LLVMDataLocal floatResult) floatType intType) $
    LLVMIntToPointer (LLVMDataLocal tmp) intType voidPtr

-- `llvmDataLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
llvmDataLet :: Identifier -> DataPlus -> LLVM -> WithEnv LLVM
llvmDataLet x (_, DataTheta y) cont = do
  penv <- gets codeEnv
  case lookup y penv of
    Nothing -> lift $ throwE $ "no such global label defined: " ++ y -- FIXME
    Just (args, _) -> do
      let funPtrType = toFunPtrType args
      return $
        LLVMLet x (LLVMBitcast (LLVMDataGlobal y) funPtrType voidPtr) cont
llvmDataLet x (_, DataUpsilon y) cont =
  return $ LLVMLet x (LLVMBitcast (LLVMDataLocal y) voidPtr voidPtr) cont
llvmDataLet x (m, DataEpsilonIntro label (LowTypeSignedInt j)) cont = do
  mi <- getEpsilonNum label
  case mi of
    Nothing -> lift $ throwE $ "no such epsilon is defined: " ++ show label
    Just i -> llvmDataLet x (m, DataInt i (LowTypeSignedInt j)) cont
llvmDataLet _ (_, DataEpsilonIntro _ _) _ =
  throwError "llvmDataLet.DataEpsilonIntro"
llvmDataLet reg (_, DataSigmaIntro ds) cont = do
  xs <- mapM (const $ newNameWith "cursor") ds
  cast <- newNameWith "cast"
  let size = length ds
  let structPtrType = toStructPtrType ds
  cont'' <- setContent cast (length xs) (zip [0 ..] xs) cont
  llvmStruct (zip xs ds) $
    LLVMLet reg (LLVMAlloc size) $ -- the result of malloc is i8*
    LLVMLet cast (LLVMBitcast (LLVMDataLocal reg) voidPtr structPtrType) cont''
llvmDataLet x (_, DataInt i (LowTypeSignedInt j)) cont =
  return $
  LLVMLet
    x
    (LLVMIntToPointer (LLVMDataInt i j) (LowTypeSignedInt j) voidPtr)
    cont
llvmDataLet _ (_, DataInt _ _) _ = throwError "llvmDataLet.DataInt"
llvmDataLet x (_, DataFloat f (LowTypeFloat j)) cont = do
  cast <- newNameWith "cast"
  let ft = LowTypeFloat j
  let st = LowTypeSignedInt j
  return $
    LLVMLet cast (LLVMBitcast (LLVMDataFloat f j) ft st) $
    LLVMLet x (LLVMIntToPointer (LLVMDataLocal cast) st voidPtr) cont
llvmDataLet _ (_, DataFloat _ _) _ = throwError "llvmDataLet.DataFloat"

llvmDataLet' :: [(Identifier, DataPlus)] -> LLVM -> WithEnv LLVM
llvmDataLet' [] cont = return cont
llvmDataLet' ((x, d):rest) cont = do
  cont' <- llvmDataLet' rest cont
  llvmDataLet x d cont'

-- returns Nothing iff the branch list is empty
constructSwitch :: [(Case, CodePlus)] -> WithEnv (Maybe (LLVM, [(Int, LLVM)]))
constructSwitch [] = return Nothing
constructSwitch [(CaseLabel _, code)] -- 最後のlabelだからdefault確定
 = do
  code' <- llvmCode code
  return $ Just (code', [])
constructSwitch ((CaseLabel x, code):rest) = do
  set <- lookupEpsilonSet x
  case elemIndex x set of
    Nothing -> lift $ throwE $ "no such index defined: " ++ show x
    Just i -> do
      code' <- llvmCode code
      m <- constructSwitch rest
      case m of
        Nothing -> return Nothing
        Just (defaultCase, caseList) ->
          return $ Just (defaultCase, (i, code') : caseList)
constructSwitch ((CaseDefault, code):_) = do
  code' <- llvmCode code
  return $ Just (code', [])

-- floatかどうかで場合分けする必要がありそう？
llvmCodeEpsilonElim ::
     (Identifier, LowType) -> DataPlus -> [(Case, CodePlus)] -> WithEnv LLVM
llvmCodeEpsilonElim (x, t) v branchList = do
  m <- constructSwitch branchList
  case m of
    Nothing -> llvmDataLet' [(x, v)] LLVMUnreachable
    Just (defaultCase, caseList) -> do
      cast <- newNameWith "cast"
      llvmDataLet' [(x, v)] $
        LLVMLet cast (LLVMPointerToInt (LLVMDataLocal x) voidPtr t) $
        LLVMSwitch (LLVMDataLocal cast, t) defaultCase caseList

setContent :: Identifier -> Int -> [(Int, Identifier)] -> LLVM -> WithEnv LLVM
setContent _ _ [] cont = return cont
setContent basePointer lengthOfStruct ((index, dataAtEpsilon):sizeDataList) cont = do
  cont' <- setContent basePointer lengthOfStruct sizeDataList cont
  loader <- newNameWith "loader"
  hole <- newNameWith "tmp"
  let bp = LLVMDataLocal basePointer
  let voidPtrPtr = LowTypePointer voidPtr
  return $
    LLVMLet loader (LLVMGetElementPtr bp (index, lengthOfStruct)) $
    LLVMLet
      hole
      (LLVMStore
         (LLVMDataLocal dataAtEpsilon, voidPtr)
         (LLVMDataLocal loader, voidPtrPtr))
      cont'

llvmStruct :: [(Identifier, DataPlus)] -> LLVM -> WithEnv LLVM
llvmStruct [] cont = return cont
llvmStruct ((x, d):xds) cont = do
  cont' <- llvmStruct xds cont
  llvmDataLet x d cont'

toStructPtrType :: [a] -> LowType
toStructPtrType xs = do
  let structType = LowTypeStruct $ map (const voidPtr) xs
  LowTypePointer structType

toFunPtrType :: [a] -> LowType
toFunPtrType xs = do
  let funType = LowTypeFunction (map (const voidPtr) xs) voidPtr
  LowTypePointer funType
