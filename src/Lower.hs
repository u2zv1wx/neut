module Lower
  ( lower,
  )
where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Comp
import Data.EnumCase
import Data.Env hiding (newNameWith'')
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import Data.LLVM
import Data.LowType
import Data.Primitive
import Data.Size
import Data.Syscall
import Data.Term
import qualified Data.Text as T
import Data.WeakTerm hiding (i64)
import Reduce.Comp

lower :: CompPlus -> WithEnv LLVM
lower mainTerm@(m, _) = do
  mainTerm'' <- reduceCompPlus mainTerm >>= lowerComp
  -- the result of "main" must be i64, not i8*
  (result, resultVar) <- newValueUpsilonWith m "result"
  (cast, castThen) <- llvmCast (Just "cast") resultVar (LowTypeInt 64)
  castResult <- castThen (LLVMReturn cast)
  -- let result: i8* := (main-term) in {cast result to i64}
  commConv result mainTerm'' castResult

lowerComp :: CompPlus -> WithEnv LLVM
lowerComp term =
  case term of
    (m, CompPrimitive theta) ->
      lowerCompPrimitive m theta
    (_, CompPiElimDownElim v ds) -> do
      (xs, vs) <- unzip <$> mapM (newValueLocal . takeBaseName) ds
      (fun, castThen) <- llvmCast (Just $ takeBaseName v) v $ toFunPtrType ds
      castThenCall <- castThen $ LLVMCall fun vs
      lowerValueLet' (zip xs ds) castThenCall
    (_, CompSigmaElim k xs v e) -> do
      let et = arrayKindToLowType k -- elem type
      let bt = LowTypePtr $ LowTypeArray (length xs) et -- base pointer type  ([(length xs) x ARRAY_ELEM_TYPE])
      let idxList = map (\i -> (LLVMValueInt i, i32)) [0 ..]
      ys <- mapM newNameWith xs
      let xts' = zip xs (repeat et)
      loadContent v bt (zip idxList (zip ys xts')) e
    (_, CompUpIntro d) -> do
      result <- newNameWith' $ takeBaseName d
      lowerValueLet result d $ LLVMReturn $ LLVMValueLocal result
    (_, CompUpElim x e1 e2) -> do
      e1' <- lowerComp e1
      e2' <- lowerComp e2
      commConv x e1' e2'
    (_, CompEnumElim v branchList) -> do
      m <- constructSwitch branchList
      case m of
        Nothing ->
          return LLVMUnreachable
        Just (defaultCase, caseList) -> do
          let t = LowTypeInt 64
          (cast, castThen) <- llvmCast (Just "enum-base") v t
          castThen $ LLVMSwitch (cast, t) defaultCase caseList
    (_, CompStructElim xks v e) -> do
      let (xs, ks) = unzip xks
      let ts = map arrayKindToLowType ks
      let xts = zip xs ts
      let bt = LowTypePtr $ LowTypeStruct ts
      let idxList = map (\i -> (LLVMValueInt i, i32)) [0 ..]
      ys <- mapM newNameWith xs
      loadContent v bt (zip idxList (zip ys xts)) e

uncastList :: [(Ident, (Ident, LowType))] -> CompPlus -> WithEnv LLVM
uncastList args e =
  case args of
    [] ->
      lowerComp e
    ((y, (x, et)) : yxs) -> do
      e' <- uncastList yxs e
      llvmUncastLet x (LLVMValueLocal y) et e'

takeBaseName :: ValuePlus -> T.Text
takeBaseName term =
  case term of
    (_, ValueConst s) ->
      s
    (_, ValueUpsilon (I (s, _))) ->
      s
    (_, ValueSigmaIntro _ ds) ->
      "array" <> T.pack (show (length ds))
    (_, ValueInt size _) ->
      "i" <> T.pack (show size)
    (_, ValueFloat FloatSize16 _) ->
      "half"
    (_, ValueFloat FloatSize32 _) ->
      "float"
    (_, ValueFloat FloatSize64 _) ->
      "double"
    (_, ValueEnumIntro _) ->
      "i64"
    (_, ValueStructIntro dks) ->
      "struct" <> T.pack (show (length dks))

takeBaseName' :: LLVMValue -> T.Text
takeBaseName' lowerValue =
  case lowerValue of
    LLVMValueLocal (I (s, _)) ->
      s
    LLVMValueGlobal s ->
      s
    LLVMValueInt _ ->
      "int"
    LLVMValueFloat FloatSize16 _ ->
      "half"
    LLVMValueFloat FloatSize32 _ ->
      "float"
    LLVMValueFloat FloatSize64 _ ->
      "double"
    LLVMValueNull ->
      "null"

loadContent ::
  ValuePlus -> -- base pointer
  LowType -> -- the type of base pointer
  [((LLVMValue, LowType), (Ident, (Ident, LowType)))] -> -- [(the index of an element, the variable to load the element)]
  CompPlus -> -- continuation
  WithEnv LLVM
loadContent v bt iyxs cont =
  case iyxs of
    [] ->
      lowerComp cont
    _ -> do
      let ixs = map (\(i, (y, (_, k))) -> (i, (y, k))) iyxs
      (bp, castThen) <- llvmCast (Just $ takeBaseName v) v bt
      let yxs = map (\(_, yx) -> yx) iyxs
      uncastThenCont <- uncastList yxs cont
      extractThenFreeThenUncastThenCont <- loadContent' bp bt ixs uncastThenCont
      castThen extractThenFreeThenUncastThenCont

loadContent' ::
  LLVMValue -> -- base pointer
  LowType -> -- the type of base pointer
  [((LLVMValue, LowType), (Ident, LowType))] -> -- [(the index of an element, the variable to keep the loaded content)]
  LLVM -> -- continuation
  WithEnv LLVM
loadContent' bp bt values cont =
  case values of
    [] -> do
      l <- llvmUncast (Just $ takeBaseName' bp) bp bt
      tmp <- newNameWith'' $ Just $ takeBaseName' bp
      j <- newCount
      commConv tmp l $ LLVMCont (LLVMOpFree (LLVMValueLocal tmp) bt j) cont
    (i, (x, et)) : xis -> do
      cont' <- loadContent' bp bt xis cont
      (posName, pos) <- newValueLocal' (Just $ asText x)
      return $
        LLVMLet
          posName
          (LLVMOpGetElementPtr (bp, bt) [(LLVMValueInt 0, LowTypeInt 32), i])
          $ LLVMLet x (LLVMOpLoad pos et) cont'

lowerCompPrimitive :: Hint -> Primitive -> WithEnv LLVM
lowerCompPrimitive _ codeOp =
  case codeOp of
    PrimitiveUnaryOp op v ->
      lowerCompUnaryOp op v
    PrimitiveBinaryOp op v1 v2 ->
      lowerCompBinaryOp op v1 v2
    PrimitiveArrayAccess lowType arr idx -> do
      let arrayType = LowTypePtr $ LowTypeArray 0 lowType
      (arrVar, castArrThen) <- llvmCast (Just $ takeBaseName arr) arr arrayType
      (idxVar, castIdxThen) <- llvmCast (Just $ takeBaseName idx) idx i64
      (resPtrName, resPtr) <- newValueLocal "result-ptr"
      resName <- newNameWith' "result"
      uncast <- llvmUncast (Just $ asText resName) (LLVMValueLocal resName) lowType
      (castArrThen >=> castIdxThen) $
        LLVMLet
          resPtrName
          ( LLVMOpGetElementPtr
              (arrVar, arrayType)
              [(LLVMValueInt 0, i32), (idxVar, i64)]
          )
          (LLVMLet resName (LLVMOpLoad resPtr lowType) uncast)
    PrimitiveSyscall syscall args -> do
      (xs, vs) <- unzip <$> mapM (const $ newValueLocal "sys-call-arg") args
      call <- syscallToLLVM syscall vs
      lowerValueLet' (zip xs args) call

lowerCompUnaryOp :: UnaryOp -> ValuePlus -> WithEnv LLVM
lowerCompUnaryOp op d = do
  let (domType, codType) = unaryOpToDomCod op
  (x, castThen) <- llvmCast (Just "unary-op") d domType
  result <- newNameWith' "unary-op-result"
  uncast <- llvmUncast (Just $ asText result) (LLVMValueLocal result) codType
  castThen $ LLVMLet result (LLVMOpUnaryOp op x) uncast

lowerCompBinaryOp :: BinaryOp -> ValuePlus -> ValuePlus -> WithEnv LLVM
lowerCompBinaryOp op v1 v2 = do
  let (domType, codType) = binaryOpToDomCod op
  (x1, cast1then) <- llvmCast (Just "binary-op-fst") v1 domType
  (x2, cast2then) <- llvmCast (Just "binary-op-snd") v2 domType
  result <- newNameWith' "binary-op-result"
  uncast <- llvmUncast (Just $ asText result) (LLVMValueLocal result) codType
  (cast1then >=> cast2then) $ LLVMLet result (LLVMOpBinaryOp op x1 x2) uncast

llvmCast ::
  Maybe T.Text ->
  ValuePlus ->
  LowType ->
  WithEnv (LLVMValue, LLVM -> WithEnv LLVM)
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
        ( LLVMValueLocal x,
          lowerValueLet tmp v
            . LLVMLet x (LLVMOpBitcast (LLVMValueLocal tmp) voidPtr lowType)
        )

llvmCastInt ::
  Maybe T.Text -> -- base name for newly created variables
  ValuePlus ->
  LowType ->
  WithEnv (LLVMValue, LLVM -> WithEnv LLVM)
llvmCastInt mName v lowType = do
  x <- newNameWith'' mName
  y <- newNameWith'' mName
  return
    ( LLVMValueLocal y,
      lowerValueLet x v
        . LLVMLet
          y
          (LLVMOpPointerToInt (LLVMValueLocal x) voidPtr lowType)
    )

llvmCastFloat ::
  Maybe T.Text -> -- base name for newly created variables
  ValuePlus ->
  FloatSize ->
  WithEnv (LLVMValue, LLVM -> WithEnv LLVM)
llvmCastFloat mName v size = do
  let floatType = LowTypeFloat size
  let intType = LowTypeInt $ sizeAsInt size
  (xName, x) <- newValueLocal' mName
  (yName, y) <- newValueLocal' mName
  z <- newNameWith'' mName
  return
    ( LLVMValueLocal z,
      lowerValueLet xName v
        . LLVMLet yName (LLVMOpPointerToInt x voidPtr intType)
        . LLVMLet z (LLVMOpBitcast y intType floatType)
    )

-- uncast: {some-concrete-type} -> voidPtr
llvmUncast :: Maybe T.Text -> LLVMValue -> LowType -> WithEnv LLVM
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
      return $
        LLVMLet x (LLVMOpBitcast result lowType voidPtr) $
          LLVMReturn (LLVMValueLocal x)

llvmUncastInt :: Maybe T.Text -> LLVMValue -> LowType -> WithEnv LLVM
llvmUncastInt mName result lowType = do
  x <- newNameWith'' mName
  return $
    LLVMLet x (LLVMOpIntToPointer result lowType voidPtr) $
      LLVMReturn (LLVMValueLocal x)

llvmUncastFloat :: Maybe T.Text -> LLVMValue -> FloatSize -> WithEnv LLVM
llvmUncastFloat mName floatResult i = do
  let floatType = LowTypeFloat i
  let intType = LowTypeInt $ sizeAsInt i
  tmp <- newNameWith'' mName
  x <- newNameWith'' mName
  return $
    LLVMLet tmp (LLVMOpBitcast floatResult floatType intType) $
      LLVMLet x (LLVMOpIntToPointer (LLVMValueLocal tmp) intType voidPtr) $
        LLVMReturn (LLVMValueLocal x)

llvmUncastLet :: Ident -> LLVMValue -> LowType -> LLVM -> WithEnv LLVM
llvmUncastLet x@(I (s, _)) d lowType cont = do
  l <- llvmUncast (Just s) d lowType
  commConv x l cont

-- `lowerValueLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
lowerValueLet :: Ident -> ValuePlus -> LLVM -> WithEnv LLVM
lowerValueLet x lowerValue cont =
  case lowerValue of
    (m, ValueConst y) -> do
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
              llvmUncastLet x (LLVMValueGlobal y') (toFunPtrType xts) cont
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
            llvm <- reduceCompPlus e >>= lowerComp
            insLLVMEnv y args llvm
            llvmUncastLet x (LLVMValueGlobal y) (toFunPtrType args) cont
          | otherwise ->
            llvmUncastLet x (LLVMValueGlobal y) (toFunPtrType args) cont
    (_, ValueUpsilon y) ->
      llvmUncastLet x (LLVMValueLocal y) voidPtr cont
    (m, ValueSigmaIntro k ds) -> do
      let elemType = arrayKindToLowType k
      let arrayType = AggPtrTypeArray (length ds) elemType
      let dts = zip ds (repeat elemType)
      storeContent m x arrayType dts cont
    (_, ValueInt size l) ->
      llvmUncastLet x (LLVMValueInt l) (LowTypeInt size) cont
    (_, ValueFloat size f) ->
      llvmUncastLet x (LLVMValueFloat size f) (LowTypeFloat size) cont
    (m, ValueEnumIntro l) -> do
      i <- toInteger <$> getEnumNum m l
      llvmUncastLet x (LLVMValueInt i) (LowTypeInt 64) cont
    (m, ValueStructIntro dks) -> do
      let (ds, ks) = unzip dks
      let ts = map arrayKindToLowType ks
      let structType = AggPtrTypeStruct ts
      storeContent m x structType (zip ds ts) cont

syscallToLLVM :: Syscall -> [LLVMValue] -> WithEnv LLVM
syscallToLLVM syscall ds =
  case syscall of
    Left name -> do
      denv <- gets declEnv
      when (not $ name `Map.member` denv) $ do
        let dom = map (const voidPtr) ds
        let cod = voidPtr
        modify (\env -> env {declEnv = Map.insert name (dom, cod) denv})
      return $ LLVMCall (LLVMValueGlobal name) ds
    Right (_, num) -> do
      res <- newNameWith' "result"
      return $
        LLVMLet res (LLVMOpSyscall num ds) $
          LLVMReturn (LLVMValueLocal res)

lowerValueLet' :: [(Ident, ValuePlus)] -> LLVM -> WithEnv LLVM
lowerValueLet' binder cont =
  case binder of
    [] ->
      return cont
    (x, d) : rest -> do
      cont' <- lowerValueLet' rest cont
      lowerValueLet x d cont'

-- returns Nothing iff the branch list is empty
constructSwitch :: [(EnumCase, CompPlus)] -> WithEnv (Maybe (LLVM, [(Int, LLVM)]))
constructSwitch switch =
  case switch of
    [] ->
      return Nothing
    [(EnumCaseLabel _, code)] -> do
      code' <- lowerComp code
      return $ Just (code', [])
    (EnumCaseLabel l, code@(m, _)) : rest -> do
      i <- fromInteger <$> enumValueToInteger m l
      code' <- lowerComp code
      mSwitch <- constructSwitch rest
      return $ do
        (defaultCase, caseList) <- mSwitch
        return (defaultCase, (i, code') : caseList)
    (EnumCaseDefault, code) : _ -> do
      code' <- lowerComp code
      return $ Just (code', [])

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
  Hint ->
  Ident ->
  AggPtrType ->
  [(ValuePlus, LowType)] ->
  LLVM ->
  WithEnv LLVM
storeContent m reg aggPtrType dts cont = do
  let lowType = toLowType aggPtrType
  (cast, castThen) <- llvmCast (Just $ asText reg) (m, ValueUpsilon reg) lowType
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
  LLVMValue -> -- base pointer
  LowType -> -- the type of base pointer (like [n x u8]*, {i8*, i8*}*, etc.)
  [(Integer, (ValuePlus, LowType))] -> -- [(the index of an element, the element to be stored)]
  LLVM -> -- continuation
  WithEnv LLVM
storeContent' bp bt values cont =
  case values of
    [] ->
      return cont
    (i, (d, et)) : ids -> do
      cont' <- storeContent' bp bt ids cont
      (locName, loc) <- newValueLocal $ takeBaseName d <> "-location"
      (cast, castThen) <- llvmCast (Just $ takeBaseName d) d et
      let it = indexTypeOf bt
      castThen $
        LLVMLet
          locName
          (LLVMOpGetElementPtr (bp, bt) [(LLVMValueInt 0, i32), (LLVMValueInt i, it)])
          $ LLVMCont (LLVMOpStore et cast loc) cont'

storeContent'' :: Ident -> LowType -> SizeInfo -> Int -> LLVM -> WithEnv LLVM
storeContent'' reg elemType sizeInfo len cont = do
  (c, cVar) <- newValueLocal $ "sizeof-" <> asText reg
  (i, iVar) <- newValueLocal $ "sizeof-" <> asText reg
  return $
    LLVMLet
      c
      ( LLVMOpGetElementPtr
          (LLVMValueNull, LowTypePtr elemType)
          [(LLVMValueInt (toInteger len), i64)]
      )
      $ LLVMLet i (LLVMOpPointerToInt cVar (LowTypePtr elemType) (LowTypeInt 64)) $
        LLVMLet reg (LLVMOpAlloc iVar sizeInfo) cont

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

newValueLocal :: T.Text -> WithEnv (Ident, LLVMValue)
newValueLocal name = do
  x <- newNameWith' name
  return (x, LLVMValueLocal x)

newValueLocal' :: Maybe T.Text -> WithEnv (Ident, LLVMValue)
newValueLocal' mName = do
  x <- newNameWith'' mName
  return (x, LLVMValueLocal x)

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

enumValueToInteger :: Hint -> T.Text -> WithEnv Integer
enumValueToInteger m l =
  toInteger <$> getEnumNum m l

getEnumNum :: Hint -> T.Text -> WithEnv Int
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
    LLVMCall d ds ->
      return $ LLVMLet x (LLVMOpCall d ds) cont2
    LLVMUnreachable ->
      return LLVMUnreachable

lookupTypeEnvMaybe :: Hint -> T.Text -> WithEnv (Maybe TermPlus)
lookupTypeEnvMaybe m x =
  catch (lookupConstTypeEnv m x >>= \e -> return (Just e)) returnNothing

returnNothing :: Error -> WithEnv (Maybe a)
returnNothing _ =
  return Nothing
