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

-- FIXME: freeすること。baseCaseでbasePointerをfreeすればいいだけっぽい？
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
      x0 <- newNameWith "arg"
      x1 <- newNameWith "arg"
      cast1 <- newNameWith "cast"
      let op1 = LLVMDataLocal cast1
      cast2 <- newNameWith "cast"
      let op2 = LLVMDataLocal cast2
      result <- newNameWith "result"
      llvmStruct [(x0, v1), (x1, v2)] $
        LLVMLet cast1 (LLVMPointerToInt (LLVMDataLocal x0) voidPtr lowType) $
        LLVMLet cast2 (LLVMPointerToInt (LLVMDataLocal x1) voidPtr lowType) $
        LLVMLet result (LLVMArith (op, lowType) op1 op2) $
        LLVMIntToPointer (LLVMDataLocal result) lowType voidPtr
    LowTypeFloat i -> do
      x0 <- newNameWith "arg"
      x1 <- newNameWith "arg"
      y11 <- newNameWith "y"
      y12 <- newNameWith "float"
      y21 <- newNameWith "y"
      y22 <- newNameWith "float"
      tmp <- newNameWith "arith"
      result <- newNameWith "result"
      y <- newNameWith "uny"
      let si = LowTypeSignedInt i
      let op' = (op, LowTypeFloat i)
      llvmStruct [(x0, v1), (x1, v2)] $
        -- cast the first argument from i8* to float
        LLVMLet y11 (LLVMPointerToInt (LLVMDataLocal x0) voidPtr si) $
        LLVMLet y12 (LLVMBitcast (LLVMDataLocal y11) si (LowTypeFloat i)) $
        -- cast the second argument from i8* to float
        LLVMLet y21 (LLVMPointerToInt (LLVMDataLocal x1) voidPtr si) $
        LLVMLet y22 (LLVMBitcast (LLVMDataLocal y21) si (LowTypeFloat i)) $
        -- compute
        LLVMLet tmp (LLVMArith op' (LLVMDataLocal y12) (LLVMDataLocal y22)) $
        -- cast the result from float to i8*
        LLVMLet y (LLVMBitcast (LLVMDataLocal tmp) (LowTypeFloat i) si) $
        LLVMLet result (LLVMIntToPointer (LLVMDataLocal y) si voidPtr) $
        LLVMReturn $ LLVMDataLocal result
    _ -> throwError "llvmCodeTheta.ThetaArith"
llvmCodeTheta _ (ThetaPrint v) = do
  let t = LowTypeSignedInt 64
  p <- newNameWith "arg"
  c <- newNameWith "cast"
  llvmDataLet p v $
    LLVMLet c (LLVMPointerToInt (LLVMDataLocal p) voidPtr t) $
    LLVMPrint t (LLVMDataLocal c)

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
llvmDataLet x (_, DataEpsilonIntro (LiteralInteger i) (LowTypeSignedInt j)) cont =
  return $
  LLVMLet
    x
    (LLVMIntToPointer (LLVMDataInt i j) (LowTypeSignedInt j) voidPtr)
    cont
llvmDataLet x (_, DataEpsilonIntro (LiteralFloat f) (LowTypeFloat j)) cont = do
  cast <- newNameWith "cast"
  let ft = LowTypeFloat j
  let st = LowTypeSignedInt j
  return $
    LLVMLet cast (LLVMBitcast (LLVMDataFloat f j) ft st) $
    LLVMLet x (LLVMIntToPointer (LLVMDataLocal cast) st voidPtr) cont
llvmDataLet x (m, DataEpsilonIntro (LiteralLabel label) _) cont = do
  mi <- getEpsilonNum label
  case mi of
    Nothing -> lift $ throwE $ "no such epsilon is defined: " ++ show label
    Just i ->
      llvmDataLet
        x
        (m, DataEpsilonIntro (LiteralInteger i) (LowTypeSignedInt 64))
        cont
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

llvmDataLet' :: [(Identifier, DataPlus)] -> LLVM -> WithEnv LLVM
llvmDataLet' [] cont = return cont
llvmDataLet' ((x, d):rest) cont = do
  cont' <- llvmDataLet' rest cont
  llvmDataLet x d cont'

constructSwitch :: [(Case, CodePlus)] -> WithEnv (Maybe (LLVM, [(Int, LLVM)]))
constructSwitch [] = return Nothing
constructSwitch [(CaseLiteral (LiteralLabel _), code)] -- 最後のlabelだからdefault確定
 = do
  code' <- llvmCode code
  return $ Just (code', [])
constructSwitch ((CaseLiteral (LiteralLabel x), code):rest) = do
  set <- lookupEpsilonSet x
  case elemIndex x set of
    Nothing -> lift $ throwE $ "no such index defined: " ++ show x
    Just i -> constructSwitch ((CaseLiteral (LiteralInteger i), code) : rest)
constructSwitch ((CaseDefault, code):_) = do
  code' <- llvmCode code
  return $ Just (code', [])
constructSwitch ((CaseLiteral (LiteralInteger i), code):rest) = do
  code' <- llvmCode code
  m <- constructSwitch rest
  case m of
    Just (defaultCase, caseList) ->
      return $ Just (defaultCase, (i, code') : caseList)
    Nothing -> return Nothing
constructSwitch ((CaseLiteral (LiteralFloat _), _):_) = undefined -- IEEE754 float equality!

-- floatかどうかで場合分けする必要がありそう？
llvmCodeEpsilonElim ::
     (Identifier, LowType) -> DataPlus -> [(Case, CodePlus)] -> WithEnv LLVM
llvmCodeEpsilonElim (_, LowTypeFloat _) _ _ = undefined
llvmCodeEpsilonElim (x, LowTypeUnsignedInt i) v branchList =
  llvmCodeEpsilonElim (x, LowTypeSignedInt i) v branchList
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
