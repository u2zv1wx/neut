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
llvmCodeTheta _ (ThetaArith op lowType v1 v2) =
  case lowType of
    LowTypeSignedInt _ -> do
      (x1, cast1then) <- llvmCastToInt v1 lowType
      (x2, cast2then) <- llvmCastToInt v2 lowType
      result <- newNameWith "result"
      (cast1then >=> cast2then) $
        LLVMLet result (LLVMArith (op, lowType) x1 x2) $
        LLVMIntToPointer (LLVMDataLocal result) lowType voidPtr
    LowTypeFloat i -> do
      (x1, cast1then) <- llvmCastToFloat v1 lowType i
      (x2, cast2then) <- llvmCastToFloat v2 lowType i
      tmp <- newNameWith "arith"
      result <- newNameWith "result"
      y <- newNameWith "uny"
      let si = LowTypeSignedInt i
      (cast1then >=> cast2then) $
        LLVMLet tmp (LLVMArith (op, lowType) x1 x2) $
        -- cast the result from float to i8*
        LLVMLet y (LLVMBitcast (LLVMDataLocal tmp) (LowTypeFloat i) si) $
        LLVMLet result (LLVMIntToPointer (LLVMDataLocal y) si voidPtr) $
        LLVMReturn $ LLVMDataLocal result
    _ -> throwError "llvmCodeTheta.ThetaArith"
llvmCodeTheta _ (ThetaCompare op lowType v1 v2) =
  case lowType of
    LowTypeSignedInt _ -> llvmCodeThetaCompareInt op lowType v1 v2
    LowTypeUnsignedInt _ -> llvmCodeThetaCompareInt op lowType v1 v2
    LowTypeFloat i -> llvmCodeThetaCompareFloat op i v1 v2
    _ -> throwError "llvmCodeTheta.ThetaCompare"
llvmCodeTheta _ (ThetaPrint v) = do
  let t = LowTypeSignedInt 64
  p <- newNameWith "arg"
  c <- newNameWith "cast"
  llvmDataLet p v $
    LLVMLet c (LLVMPointerToInt (LLVMDataLocal p) voidPtr t) $
    LLVMPrint t (LLVMDataLocal c)

llvmCodeThetaCompareInt ::
     Compare -> LowType -> DataPlus -> DataPlus -> WithEnv LLVM
llvmCodeThetaCompareInt op lowType v1 v2 = do
  let boolType = LowTypeSignedInt 1
  (x1, cast1then) <- llvmCastToInt v1 lowType
  (x2, cast2then) <- llvmCastToInt v2 lowType
  result <- newNameWith "result"
  (cast1then >=> cast2then) $
    LLVMLet result (LLVMCompare (op, lowType) x1 x2) $
    LLVMIntToPointer (LLVMDataLocal result) boolType voidPtr

llvmCastToInt :: DataPlus -> LowType -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastToInt v lowType = do
  x <- newNameWith "arg"
  y <- newNameWith "cast"
  return
    ( LLVMDataLocal y
    , \cont -> do
        llvmDataLet x v $
          LLVMLet y (LLVMPointerToInt (LLVMDataLocal x) voidPtr lowType) $ cont)

-- castToFloatのほうがわかりやすいか。
llvmCastToFloat ::
     DataPlus -> LowType -> Int -> WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastToFloat v lowType size = do
  x <- newNameWith "arg"
  y <- newNameWith "tmp"
  z <- newNameWith "cast"
  let si = LowTypeSignedInt size
  return
    ( LLVMDataLocal z
    , \cont -> do
        llvmDataLet x v $
          LLVMLet y (LLVMPointerToInt (LLVMDataLocal x) voidPtr si) $
          LLVMLet z (LLVMBitcast (LLVMDataLocal y) si lowType) cont)

llvmCodeThetaCompareFloat ::
     Compare -> Int -> DataPlus -> DataPlus -> WithEnv LLVM
llvmCodeThetaCompareFloat op i v1 v2 = do
  (x1, cast1then) <- llvmCastToFloat v1 (LowTypeFloat i) i
  (x2, cast2then) <- llvmCastToFloat v2 (LowTypeFloat i) i
  result <- newNameWith "result"
  let boolType = LowTypeSignedInt 1
  (cast1then >=> cast2then) $
    LLVMLet result (LLVMCompare (op, LowTypeFloat i) x1 x2) $
    LLVMIntToPointer (LLVMDataLocal result) boolType voidPtr

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
