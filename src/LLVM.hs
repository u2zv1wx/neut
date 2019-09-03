module LLVM
  ( toLLVM
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.List                  (elemIndex)
import qualified Text.Show.Pretty           as Pr

import           Data.Basic
import           Data.Env
import           Data.LLVM
import           Data.LowCode

toLLVM :: LowCodePlus -> WithEnv LLVM
toLLVM mainTerm = do
  penv <- gets lowCodeEnv
  forM_ penv $ \(name, (args, e)) -> do
    llvm <- llvmLowCode e
    -- mainTermの中で必要になったものだけinsLLVMEnvするようにしたほうがよさそう。
    insLLVMEnv name args llvm
  llvmLowCode mainTerm

llvmLowCode :: LowCodePlus -> WithEnv LLVM
llvmLowCode (m, LowCodeTheta theta) = llvmLowCodeTheta m theta
llvmLowCode (_, LowCodeEpsilonElim x v branchList) =
  llvmLowCodeEpsilonElim x v branchList
llvmLowCode (_, LowCodePiElimDownElim v es) = do
  f <- newNameWith "fun"
  es' <- mapM llvmLowCode es
  xs <- mapM (const (newNameWith "arg")) es'
  cast <- newNameWith "cast"
  let funPtrType = toFunPtrType es
  llvmLowDataLet' [(f, v)] $
    llvmLowCodeLet (zip xs es') $
    LLVMLet cast (LLVMBitcast (LLVMDataLocal f) voidPtr funPtrType) $
    LLVMCall (LLVMDataLocal cast) (map LLVMDataLocal xs)
llvmLowCode (_, LowCodeSigmaElim xs v e) = do
  basePointer <- newNameWith "base"
  castedBasePointer <- newNameWith "castedBase"
  extractAndCont <-
    llvmLowCodeSigmaElim
      basePointer
      (zip xs [0 ..])
      castedBasePointer
      (length xs)
      e
  llvmLowDataLet basePointer v $
    LLVMLet
      castedBasePointer
      (LLVMBitcast
         (LLVMDataLocal basePointer)
         voidPtr
         (toStructPtrType [1 .. (length xs)]))
      extractAndCont
llvmLowCode (_, LowCodeUpIntro d) = do
  result <- newNameWith "ans"
  llvmLowDataLet result d $ LLVMReturn $ LLVMDataLocal result
llvmLowCode (_, LowCodeCopyN _ _) = undefined
llvmLowCode (_, LowCodeTransposeN _ _) = undefined

llvmLowCodeSigmaElim ::
     Identifier
  -> [(Identifier, Int)]
  -> Identifier
  -> Int
  -> LowCodePlus
  -> WithEnv LLVM
llvmLowCodeSigmaElim _ [] _ _ cont = llvmLowCode cont
llvmLowCodeSigmaElim basePointer ((x, i):xis) castedBasePointer n cont = do
  cont' <- llvmLowCodeSigmaElim basePointer xis castedBasePointer n cont
  loader <- newNameWith "loader"
  return $
    LLVMLet loader (LLVMGetElementPtr (LLVMDataLocal castedBasePointer) (i, n)) $
    LLVMLet x (LLVMLoad (LLVMDataLocal loader)) cont'

llvmLowCodeTheta :: LowCodeMeta -> LowDataTheta -> WithEnv LLVM
llvmLowCodeTheta _ (LowDataThetaArith op lowType v1 v2) =
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
    _ -> throwError "llvmLowCodeTheta.ThetaArith"
llvmLowCodeTheta _ (LowDataThetaPrint v) = do
  let t = LowTypeSignedInt 64
  p <- newNameWith "arg"
  c <- newNameWith "cast"
  llvmLowDataLet p v $
    LLVMLet c (LLVMPointerToInt (LLVMDataLocal p) voidPtr t) $
    LLVMPrint t (LLVMDataLocal c)

llvmLowCodeLet :: [(Identifier, LLVM)] -> LLVM -> LLVM
llvmLowCodeLet [] cont           = cont
llvmLowCodeLet ((x, e):xes) cont = LLVMLet x e $ llvmLowCodeLet xes cont

-- `llvmLowDataLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
llvmLowDataLet :: Identifier -> LowDataPlus -> LLVM -> WithEnv LLVM
llvmLowDataLet x (_, LowDataTheta y) cont = do
  penv <- gets lowCodeEnv
  case lookup y penv of
    Nothing -> lift $ throwE $ "no such global label defined: " ++ y -- FIXME
    Just (args, _) -> do
      let funPtrType = toFunPtrType args
      return $
        LLVMLet x (LLVMBitcast (LLVMDataGlobal y) funPtrType voidPtr) cont
llvmLowDataLet x (_, LowDataUpsilon y) cont =
  return $ LLVMLet x (LLVMBitcast (LLVMDataLocal y) voidPtr voidPtr) cont
llvmLowDataLet x (_, LowDataEpsilonIntro (LiteralInteger i) (LowTypeSignedInt j)) cont =
  return $
  LLVMLet
    x
    (LLVMIntToPointer (LLVMDataInt i j) (LowTypeSignedInt j) voidPtr)
    cont
llvmLowDataLet x (_, LowDataEpsilonIntro (LiteralFloat f) (LowTypeFloat j)) cont = do
  cast <- newNameWith "cast"
  let ft = LowTypeFloat j
  let st = LowTypeSignedInt j
  return $
    LLVMLet cast (LLVMBitcast (LLVMDataFloat f j) ft st) $
    LLVMLet x (LLVMIntToPointer (LLVMDataLocal cast) st voidPtr) cont
llvmLowDataLet x (m, LowDataEpsilonIntro (LiteralLabel label) _) cont = do
  mi <- getEpsilonNum label
  case mi of
    Nothing -> lift $ throwE $ "no such epsilon is defined: " ++ show label
    Just i ->
      llvmLowDataLet
        x
        (m, LowDataEpsilonIntro (LiteralInteger i) (LowTypeSignedInt 64))
        cont
llvmLowDataLet _ (_, LowDataEpsilonIntro _ _) _ =
  throwError "llvmLowDataLet.LowDataEpsilonIntro"
llvmLowDataLet reg (_, LowDataSigmaIntro ds) cont = do
  xs <- mapM (const $ newNameWith "cursor") ds
  cast <- newNameWith "cast"
  let ts = map (const voidPtr) ds
  let structPtrType = toStructPtrType ds
  cont'' <- setContent cast (length xs) (zip [0 ..] xs) cont
  llvmStruct (zip xs ds) $
    LLVMLet reg (LLVMAlloc ts) $ -- the result of malloc is i8*
    LLVMLet cast (LLVMBitcast (LLVMDataLocal reg) voidPtr structPtrType) cont''

llvmLowDataLet' :: [(Identifier, LowDataPlus)] -> LLVM -> WithEnv LLVM
llvmLowDataLet' [] cont = return cont
llvmLowDataLet' ((x, d):rest) cont = do
  cont' <- llvmLowDataLet' rest cont
  llvmLowDataLet x d cont'

constructSwitch ::
     LowDataPlus -> [(Case, LowCodePlus)] -> WithEnv (LLVM, [(Int, LLVM)])
constructSwitch _ [] = lift $ throwE "empty branch"
constructSwitch name ((CaseLiteral (LiteralLabel x), code):rest) = do
  set <- lookupEpsilonSet x
  case elemIndex x set of
    Nothing -> lift $ throwE $ "no such index defined: " ++ show name
    Just i ->
      constructSwitch name ((CaseLiteral (LiteralInteger i), code) : rest)
constructSwitch _ ((CaseDefault, code):_) = do
  code' <- llvmLowCode code
  return (code', [])
constructSwitch name ((CaseLiteral (LiteralInteger i), code):rest) = do
  code' <- llvmLowCode code
  (defaultCase, caseList) <- constructSwitch name rest
  return (defaultCase, (i, code') : caseList)
constructSwitch _ ((CaseLiteral (LiteralFloat _), _):_) = undefined -- IEEE754 float equality!

llvmLowCodeEpsilonElim ::
     Identifier -> LowDataPlus -> [(Case, LowCodePlus)] -> WithEnv LLVM
llvmLowCodeEpsilonElim x v branchList = do
  (defaultCase, caseList) <- constructSwitch v branchList
  cast <- newNameWith "cast"
  llvmLowDataLet' [(x, v)] $
    LLVMLet
      cast
      (LLVMPointerToInt (LLVMDataLocal x) voidPtr (LowTypeSignedInt 64)) $
    LLVMSwitch (LLVMDataLocal cast) defaultCase caseList

setContent :: Identifier -> Int -> [(Int, Identifier)] -> LLVM -> WithEnv LLVM
setContent _ _ [] cont = return cont
setContent basePointer lengthOfStruct ((index, dataAtEpsilon):sizeLowDataList) cont = do
  cont' <- setContent basePointer lengthOfStruct sizeLowDataList cont
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

llvmStruct :: [(Identifier, LowDataPlus)] -> LLVM -> WithEnv LLVM
llvmStruct [] cont = return cont
llvmStruct ((x, d):xds) cont = do
  cont' <- llvmStruct xds cont
  llvmLowDataLet x d cont'

toStructPtrType :: [a] -> LowType
toStructPtrType xs = do
  let structType = LowTypeStruct $ map (const voidPtr) xs
  LowTypePointer structType
