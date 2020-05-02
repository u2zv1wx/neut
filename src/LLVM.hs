module LLVM
  ( toLLVM,
  )
where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Code
import Data.EnumCase
import Data.Env hiding (newNameWith'')
import qualified Data.HashMap.Lazy as Map
import Data.Ident
import Data.LLVM
import Data.LowType
import Data.Meta
import Data.Primitive
import qualified Data.Set as S
import Data.Size
import Data.Syscall
import Data.Term
import qualified Data.Text as T
import Data.WeakTerm hiding (i64)
import Reduce.Code

toLLVM :: CodePlus -> WithEnv LLVM
toLLVM mainTerm@(m, _) = do
  modify (\env -> env {nameSet = S.empty})
  mainTerm' <- reduceCodePlus mainTerm
  modify (\env -> env {nameSet = S.empty})
  mainTerm'' <- llvmCode mainTerm'
  -- the result of "main" must be i64, not i8*
  (result, resultVar) <- newDataUpsilonWith m "result"
  (cast, castThen) <- llvmCast (Just "cast") resultVar (LowTypeInt 64)
  castResult <- castThen (LLVMReturn cast)
  -- let result: i8* := (main-term) in {cast result to i64}
  commConv result mainTerm'' castResult

llvmCode :: CodePlus -> WithEnv LLVM
llvmCode term =
  case term of
    (m, CodePrimitive theta) ->
      llvmCodePrimitive m theta
    (_, CodePiElimDownElim v ds) -> do
      (xs, vs) <- unzip <$> mapM (newDataLocal . takeBaseName) ds
      (fun, castThen) <- llvmCast (Just $ takeBaseName v) v $ toFunPtrType ds
      castThenCall <- castThen $ LLVMCall fun vs
      llvmDataLet' (zip xs ds) castThenCall
    (_, CodeSigmaElim k xs v e) -> do
      let et = arrayKindToLowType k -- elem type
      let bt = LowTypePtr $ LowTypeArray (length xs) et -- base pointer type  ([(length xs) x ARRAY_ELEM_TYPE])
      let idxList = map (\i -> (LLVMDataInt i, i32)) [0 ..]
      ys <- mapM newNameWith xs
      let xts' = zip xs (repeat et)
      loadContent v bt (zip idxList (zip ys xts')) e
    (_, CodeUpIntro d) -> do
      result <- newNameWith' $ takeBaseName d
      llvmDataLet result d $ LLVMReturn $ LLVMDataLocal result
    (_, CodeUpElim x e1 e2) -> do
      e1' <- llvmCode e1
      e2' <- llvmCode e2
      commConv x e1' e2'
    (_, CodeEnumElim sub v branchList) ->
      prepareBranch sub branchList >>= llvmCodeEnumElim v
    (_, CodeStructElim xks v e) -> do
      let (xs, ks) = unzip xks
      let ts = map arrayKindToLowType ks
      let xts = zip xs ts
      let bt = LowTypePtr $ LowTypeStruct ts
      let idxList = map (\i -> (LLVMDataInt i, i32)) [0 ..]
      ys <- mapM newNameWith xs
      loadContent v bt (zip idxList (zip ys xts)) e

prepareBranch :: SubstDataPlus -> [(a, CodePlus)] -> WithEnv [(a, CodePlus)]
prepareBranch sub branchList = do
  let (ls, es) = unzip branchList
  let es' = map (substCodePlus sub) es
  ns <- gets nameSet
  modify (\env -> env {nameSet = S.empty})
  es'' <- mapM reduceCodePlus es'
  modify (\env -> env {nameSet = ns})
  return $ zip ls es''

uncastList :: [(Ident, (Ident, LowType))] -> CodePlus -> WithEnv LLVM
uncastList args e =
  case args of
    [] ->
      llvmCode e
    ((y, (x, et)) : yxs) -> do
      e' <- uncastList yxs e
      llvmUncastLet x (LLVMDataLocal y) et e'

takeBaseName :: DataPlus -> T.Text
takeBaseName term =
  case term of
    (_, DataConst s) ->
      s
    (_, DataUpsilon (I (s, _))) ->
      s
    (_, DataSigmaIntro _ ds) ->
      "array" <> T.pack (show (length ds))
    (_, DataInt size _) ->
      "i" <> T.pack (show size)
    (_, DataFloat FloatSize16 _) ->
      "half"
    (_, DataFloat FloatSize32 _) ->
      "float"
    (_, DataFloat FloatSize64 _) ->
      "double"
    (_, DataEnumIntro _) ->
      "i64"
    (_, DataStructIntro dks) ->
      "struct" <> T.pack (show (length dks))

takeBaseName' :: LLVMData -> T.Text
takeBaseName' llvmData =
  case llvmData of
    LLVMDataLocal (I (s, _)) ->
      s
    LLVMDataGlobal s ->
      s
    LLVMDataInt _ ->
      "int"
    LLVMDataFloat FloatSize16 _ ->
      "half"
    LLVMDataFloat FloatSize32 _ ->
      "float"
    LLVMDataFloat FloatSize64 _ ->
      "double"
    LLVMDataNull ->
      "null"

loadContent ::
  DataPlus -> -- base pointer
  LowType -> -- the type of base pointer
  [((LLVMData, LowType), (Ident, (Ident, LowType)))] -> -- [(the index of an element, the variable to load the element)]
  CodePlus -> -- continuation
  WithEnv LLVM
loadContent v bt iyxs cont =
  case iyxs of
    [] ->
      llvmCode cont
    _ -> do
      let ixs = map (\(i, (y, (_, k))) -> (i, (y, k))) iyxs
      (bp, castThen) <- llvmCast (Just $ takeBaseName v) v bt
      let yxs = map (\(_, yx) -> yx) iyxs
      uncastThenCont <- uncastList yxs cont
      extractThenFreeThenUncastThenCont <- loadContent' bp bt ixs uncastThenCont
      castThen extractThenFreeThenUncastThenCont

loadContent' ::
  LLVMData -> -- base pointer
  LowType -> -- the type of base pointer
  [((LLVMData, LowType), (Ident, LowType))] -> -- [(the index of an element, the variable to keep the loaded content)]
  LLVM -> -- continuation
  WithEnv LLVM
loadContent' bp bt values cont =
  case values of
    [] -> do
      l <- llvmUncast (Just $ takeBaseName' bp) bp bt
      tmp <- newNameWith'' $ Just $ takeBaseName' bp
      j <- newCount
      commConv tmp l $ LLVMCont (LLVMOpFree (LLVMDataLocal tmp) bt j) cont
    (i, (x, et)) : xis -> do
      cont' <- loadContent' bp bt xis cont
      (posName, pos) <- newDataLocal' (Just $ asText x)
      return
        $ LLVMLet
          posName
          (LLVMOpGetElementPtr (bp, bt) [(LLVMDataInt 0, LowTypeInt 32), i])
        $ LLVMLet x (LLVMOpLoad pos et) cont'

llvmCodePrimitive :: Meta -> Primitive -> WithEnv LLVM
llvmCodePrimitive _ codeOp =
  case codeOp of
    PrimitiveUnaryOp op v ->
      llvmCodeUnaryOp op v
    PrimitiveBinaryOp op v1 v2 ->
      llvmCodeBinaryOp op v1 v2
    PrimitiveArrayAccess lowType arr idx -> do
      let arrayType = LowTypePtr $ LowTypeArray 0 lowType
      (arrVar, castArrThen) <- llvmCast (Just $ takeBaseName arr) arr arrayType
      (idxVar, castIdxThen) <- llvmCast (Just $ takeBaseName idx) idx i64
      (resPtrName, resPtr) <- newDataLocal "result-ptr"
      resName <- newNameWith' "result"
      uncast <- llvmUncast (Just $ asText resName) (LLVMDataLocal resName) lowType
      (castArrThen >=> castIdxThen) $
        LLVMLet
          resPtrName
          ( LLVMOpGetElementPtr
              (arrVar, arrayType)
              [(LLVMDataInt 0, i32), (idxVar, i64)]
          )
          (LLVMLet resName (LLVMOpLoad resPtr lowType) uncast)
    PrimitiveSyscall syscall args -> do
      (xs, vs) <- unzip <$> mapM (const $ newDataLocal "sys-call-arg") args
      call <- syscallToLLVM syscall vs
      llvmDataLet' (zip xs args) call

llvmCodeUnaryOp :: UnaryOp -> DataPlus -> WithEnv LLVM
llvmCodeUnaryOp op d = do
  let (domType, codType) = unaryOpToDomCod op
  (x, castThen) <- llvmCast (Just "unary-op") d domType
  result <- newNameWith' "unary-op-result"
  uncast <- llvmUncast (Just $ asText result) (LLVMDataLocal result) codType
  castThen $ LLVMLet result (LLVMOpUnaryOp op x) uncast

llvmCodeBinaryOp :: BinaryOp -> DataPlus -> DataPlus -> WithEnv LLVM
llvmCodeBinaryOp op v1 v2 = do
  let (domType, codType) = binaryOpToDomCod op
  (x1, cast1then) <- llvmCast (Just "binary-op-fst") v1 domType
  (x2, cast2then) <- llvmCast (Just "binary-op-snd") v2 domType
  result <- newNameWith' "binary-op-result"
  uncast <- llvmUncast (Just $ asText result) (LLVMDataLocal result) codType
  (cast1then >=> cast2then) $ LLVMLet result (LLVMOpBinaryOp op x1 x2) uncast

llvmCast ::
  Maybe T.Text ->
  DataPlus ->
  LowType ->
  WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCast mName v lowType =
  case lowType of
    LowTypeInt _ ->
      llvmCastInt mName v lowType
    LowTypeBool ->
      llvmCastInt mName v (LowTypeInt 1)
    LowTypeFloat i ->
      llvmCastFloat mName v i
    _ -> do
      tmp <- newNameWith'' mName
      x <- newNameWith'' mName
      return
        ( LLVMDataLocal x,
          llvmDataLet tmp v
            . LLVMLet x (LLVMOpBitcast (LLVMDataLocal tmp) voidPtr lowType)
        )

llvmCastInt ::
  Maybe T.Text -> -- base name for newly created variables
  DataPlus ->
  LowType ->
  WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastInt mName v lowType = do
  x <- newNameWith'' mName
  y <- newNameWith'' mName
  return
    ( LLVMDataLocal y,
      llvmDataLet x v
        . LLVMLet
          y
          (LLVMOpPointerToInt (LLVMDataLocal x) voidPtr lowType)
    )

llvmCastFloat ::
  Maybe T.Text -> -- base name for newly created variables
  DataPlus ->
  FloatSize ->
  WithEnv (LLVMData, LLVM -> WithEnv LLVM)
llvmCastFloat mName v size = do
  let floatType = LowTypeFloat size
  let intType = LowTypeInt $ sizeAsInt size
  (xName, x) <- newDataLocal' mName
  (yName, y) <- newDataLocal' mName
  z <- newNameWith'' mName
  return
    ( LLVMDataLocal z,
      llvmDataLet xName v
        . LLVMLet yName (LLVMOpPointerToInt x voidPtr intType)
        . LLVMLet z (LLVMOpBitcast y intType floatType)
    )

-- uncast: {some-concrete-type} -> voidPtr
llvmUncast :: Maybe T.Text -> LLVMData -> LowType -> WithEnv LLVM
llvmUncast mName result lowType =
  case lowType of
    LowTypeInt _ ->
      llvmUncastInt mName result lowType
    LowTypeBool ->
      llvmUncastInt mName result (LowTypeInt 1)
    LowTypeFloat i ->
      llvmUncastFloat mName result i
    _ -> do
      x <- newNameWith'' mName
      return
        $ LLVMLet x (LLVMOpBitcast result lowType voidPtr)
        $ LLVMReturn (LLVMDataLocal x)

llvmUncastInt :: Maybe T.Text -> LLVMData -> LowType -> WithEnv LLVM
llvmUncastInt mName result lowType = do
  x <- newNameWith'' mName
  return
    $ LLVMLet x (LLVMOpIntToPointer result lowType voidPtr)
    $ LLVMReturn (LLVMDataLocal x)

llvmUncastFloat :: Maybe T.Text -> LLVMData -> FloatSize -> WithEnv LLVM
llvmUncastFloat mName floatResult i = do
  let floatType = LowTypeFloat i
  let intType = LowTypeInt $ sizeAsInt i
  tmp <- newNameWith'' mName
  x <- newNameWith'' mName
  return
    $ LLVMLet tmp (LLVMOpBitcast floatResult floatType intType)
    $ LLVMLet x (LLVMOpIntToPointer (LLVMDataLocal tmp) intType voidPtr)
    $ LLVMReturn (LLVMDataLocal x)

llvmUncastLet :: Ident -> LLVMData -> LowType -> LLVM -> WithEnv LLVM
llvmUncastLet x@(I (s, _)) d lowType cont = do
  l <- llvmUncast (Just s) d lowType
  commConv x l cont

-- `llvmDataLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
llvmDataLet :: Ident -> DataPlus -> LLVM -> WithEnv LLVM
llvmDataLet x llvmData cont =
  case llvmData of
    (m, DataConst y) -> do
      cenv <- gets codeEnv
      lenv <- gets llvmEnv
      case Map.lookup y cenv of
        Nothing -> do
          mt <- lookupTypeEnvMaybe m y
          case mt of
            Just (_, TermPi xts _) -> do
              let y' = "llvm_" <> y
              denv <- gets declEnv
              let argType = map (const voidPtr) xts
              modify (\env -> env {declEnv = Map.insert y' (argType, voidPtr) denv})
              llvmUncastLet x (LLVMDataGlobal y') (toFunPtrType xts) cont
            Just t ->
              raiseError m $
                "external constants must have pi-type, but the type of `"
                  <> y
                  <> "` is:\n"
                  <> toText (weaken t)
            Nothing ->
              raiseCritical m $ "no such global label defined: " <> y
        Just (Definition _ args e)
          | not (Map.member y lenv) -> do
            insLLVMEnv y args LLVMUnreachable
            llvm <- llvmCode e
            insLLVMEnv y args llvm
            llvmUncastLet x (LLVMDataGlobal y) (toFunPtrType args) cont
          | otherwise ->
            llvmUncastLet x (LLVMDataGlobal y) (toFunPtrType args) cont
    (_, DataUpsilon y) ->
      llvmUncastLet x (LLVMDataLocal y) voidPtr cont
    (m, DataSigmaIntro k ds) -> do
      let elemType = arrayKindToLowType k
      let arrayType = AggPtrTypeArray (length ds) elemType
      let dts = zip ds (repeat elemType)
      storeContent m x arrayType dts cont
    (_, DataInt size l) ->
      llvmUncastLet x (LLVMDataInt l) (LowTypeInt size) cont
    (_, DataFloat size f) ->
      llvmUncastLet x (LLVMDataFloat size f) (LowTypeFloat size) cont
    (m, DataEnumIntro l) -> do
      i <- toInteger <$> getEnumNum m l
      llvmUncastLet x (LLVMDataInt i) (LowTypeInt 64) cont
    (m, DataStructIntro dks) -> do
      let (ds, ks) = unzip dks
      let ts = map arrayKindToLowType ks
      let structType = AggPtrTypeStruct ts
      storeContent m x structType (zip ds ts) cont

syscallToLLVM :: Syscall -> [LLVMData] -> WithEnv LLVM
syscallToLLVM syscall ds =
  case syscall of
    Left name -> do
      denv <- gets declEnv
      when (not $ name `Map.member` denv) $ do
        let dom = map (const voidPtr) ds
        let cod = voidPtr
        modify (\env -> env {declEnv = Map.insert name (dom, cod) denv})
      return $ LLVMCall (LLVMDataGlobal name) ds
    Right (_, num) -> do
      res <- newNameWith' "result"
      return
        $ LLVMLet res (LLVMOpSyscall num ds)
        $ LLVMReturn (LLVMDataLocal res)

llvmDataLet' :: [(Ident, DataPlus)] -> LLVM -> WithEnv LLVM
llvmDataLet' binder cont =
  case binder of
    [] ->
      return cont
    (x, d) : rest -> do
      cont' <- llvmDataLet' rest cont
      llvmDataLet x d cont'

-- returns Nothing iff the branch list is empty
constructSwitch :: [(EnumCase, CodePlus)] -> WithEnv (Maybe (LLVM, [(Int, LLVM)]))
constructSwitch switch =
  case switch of
    [] ->
      return Nothing
    [(EnumCaseLabel _, code)] -> do
      code' <- llvmCode code
      return $ Just (code', [])
    (EnumCaseLabel l, code@(m, _)) : rest -> do
      i <- fromInteger <$> enumValueToInteger m l
      code' <- llvmCode code
      mSwitch <- constructSwitch rest
      return $ do
        (defaultCase, caseList) <- mSwitch
        return (defaultCase, (i, code') : caseList)
    (EnumCaseDefault, code) : _ -> do
      code' <- llvmCode code
      return $ Just (code', [])

llvmCodeEnumElim :: DataPlus -> [(EnumCase, CodePlus)] -> WithEnv LLVM
llvmCodeEnumElim v branchList = do
  m <- constructSwitch branchList
  case m of
    Nothing ->
      return LLVMUnreachable
    Just (defaultCase, caseList) -> do
      let t = LowTypeInt 64
      (cast, castThen) <- llvmCast (Just "enum-base") v t
      castThen $ LLVMSwitch (cast, t) defaultCase caseList

data AggPtrType
  = AggPtrTypeArray Int LowType
  | AggPtrTypeStruct [LowType]

toLowType :: AggPtrType -> LowType
toLowType aggPtrType =
  case aggPtrType of
    AggPtrTypeArray i t ->
      LowTypePtr $ LowTypeArray i t
    AggPtrTypeStruct ts ->
      LowTypePtr $ LowTypeStruct ts

storeContent ::
  Meta ->
  Ident ->
  AggPtrType ->
  [(DataPlus, LowType)] ->
  LLVM ->
  WithEnv LLVM
storeContent m reg aggPtrType dts cont = do
  let lowType = toLowType aggPtrType
  (cast, castThen) <- llvmCast (Just $ asText reg) (m, DataUpsilon reg) lowType
  storeThenCont <- storeContent' cast lowType (zip [0 ..] dts) cont
  castThenStoreThenCont <- castThen storeThenCont
  -- Use getelementptr to realize `sizeof`. More info:
  --   http://nondot.org/sabre/LLVMNotes/SizeOf-OffsetOf-VariableSizedStructs.txt
  case aggPtrType of
    AggPtrTypeStruct ts ->
      storeContent'' reg (LowTypeStruct ts) lowType 1 castThenStoreThenCont
    AggPtrTypeArray len t ->
      storeContent'' reg t lowType len castThenStoreThenCont

storeContent' ::
  LLVMData -> -- base pointer
  LowType -> -- the type of base pointer (like [n x u8]*, {i8*, i8*}*, etc.)
  [(Integer, (DataPlus, LowType))] -> -- [(the index of an element, the element to be stored)]
  LLVM -> -- continuation
  WithEnv LLVM
storeContent' bp bt values cont =
  case values of
    [] ->
      return cont
    (i, (d, et)) : ids -> do
      cont' <- storeContent' bp bt ids cont
      (locName, loc) <- newDataLocal $ takeBaseName d <> "-location"
      (cast, castThen) <- llvmCast (Just $ takeBaseName d) d et
      let it = indexTypeOf bt
      castThen
        $ LLVMLet
          locName
          (LLVMOpGetElementPtr (bp, bt) [(LLVMDataInt 0, i32), (LLVMDataInt i, it)])
        $ LLVMCont (LLVMOpStore et cast loc) cont'

storeContent'' :: Ident -> LowType -> SizeInfo -> Int -> LLVM -> WithEnv LLVM
storeContent'' reg elemType sizeInfo len cont = do
  (c, cVar) <- newDataLocal $ "sizeof-" <> asText reg
  (i, iVar) <- newDataLocal $ "sizeof-" <> asText reg
  return
    $ LLVMLet
      c
      ( LLVMOpGetElementPtr
          (LLVMDataNull, LowTypePtr elemType)
          [(LLVMDataInt (toInteger len), i64)]
      )
    $ LLVMLet i (LLVMOpPointerToInt cVar (LowTypePtr elemType) (LowTypeInt 64))
    $ LLVMLet reg (LLVMOpAlloc iVar sizeInfo) cont

indexTypeOf :: LowType -> LowType
indexTypeOf lowType =
  case lowType of
    LowTypePtr (LowTypeStruct _) ->
      LowTypeInt 32
    _ ->
      LowTypeInt 64

toFunPtrType :: [a] -> LowType
toFunPtrType xs =
  LowTypeFunctionPtr (map (const voidPtr) xs) voidPtr

newDataLocal :: T.Text -> WithEnv (Ident, LLVMData)
newDataLocal name = do
  x <- newNameWith' name
  return (x, LLVMDataLocal x)

newDataLocal' :: Maybe T.Text -> WithEnv (Ident, LLVMData)
newDataLocal' mName = do
  x <- newNameWith'' mName
  return (x, LLVMDataLocal x)

i64 :: LowType
i64 =
  LowTypeInt 64

i32 :: LowType
i32 =
  LowTypeInt 32

newNameWith'' :: Maybe T.Text -> WithEnv Ident
newNameWith'' mName =
  case mName of
    Nothing ->
      newNameWith' "var"
    Just name ->
      newNameWith' name

enumValueToInteger :: Meta -> T.Text -> WithEnv Integer
enumValueToInteger m l =
  toInteger <$> getEnumNum m l

getEnumNum :: Meta -> T.Text -> WithEnv Int
getEnumNum m label = do
  renv <- gets revEnumEnv
  case Map.lookup label renv of
    Nothing ->
      raiseCritical m $ "no such enum is defined: " <> label
    Just (_, i) ->
      return i

insLLVMEnv :: T.Text -> [Ident] -> LLVM -> WithEnv ()
insLLVMEnv funName args e =
  modify (\env -> env {llvmEnv = Map.insert funName (args, e) (llvmEnv env)})

commConv :: Ident -> LLVM -> LLVM -> WithEnv LLVM
commConv x llvm cont2 =
  case llvm of
    LLVMReturn d ->
      return $ LLVMLet x (LLVMOpBitcast d voidPtr voidPtr) cont2 -- nop
    LLVMLet y op cont1 -> do
      cont <- commConv x cont1 cont2
      return $ LLVMLet y op cont
    LLVMCont op cont1 -> do
      cont <- commConv x cont1 cont2
      return $ LLVMCont op cont
    LLVMSwitch (d, t) defaultCase caseList -> do
      let (ds, es) = unzip caseList
      es' <- mapM (\e -> commConv x e cont2) es
      let caseList' = zip ds es'
      defaultCase' <- commConv x defaultCase cont2
      return $ LLVMSwitch (d, t) defaultCase' caseList'
    LLVMBranch d onTrue onFalse -> do
      onTrue' <- commConv x onTrue cont2
      onFalse' <- commConv x onFalse cont2
      return $ LLVMBranch d onTrue' onFalse'
    LLVMCall d ds ->
      return $ LLVMLet x (LLVMOpCall d ds) cont2
    LLVMUnreachable ->
      return LLVMUnreachable

lookupTypeEnvMaybe :: Meta -> T.Text -> WithEnv (Maybe TermPlus)
lookupTypeEnvMaybe m x =
  catch (lookupConstTypeEnv m x >>= \e -> return (Just e)) (\(_ :: Error) -> return Nothing)
