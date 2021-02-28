module Lower
  ( lower,
  )
where

import Control.Monad.State.Lazy
import Data.Comp
import Data.EnumCase
import Data.Env hiding (newNameWith'')
import Data.Exploit
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import Data.Log
import Data.LowComp
import Data.LowType
import Data.Primitive
import Data.Size
import qualified Data.Text as T
import Reduce.Comp

lower :: CompPlus -> WithEnv LowComp
lower mainTerm@(m, _) = do
  mainTerm'' <- reduceCompPlus mainTerm >>= lowerComp
  -- the result of "main" must be i64, not i8*
  (result, resultVar) <- newValueUpsilonWith m "result"
  (cast, castThen) <- llvmCast (Just "cast") resultVar (LowTypeInt 64)
  castResult <- castThen (LowCompReturn cast)
  -- let result: i8* := (main-term) in {cast result to i64}
  commConv result mainTerm'' castResult

lowerComp :: CompPlus -> WithEnv LowComp
lowerComp term =
  case term of
    (m, CompPrimitive theta) ->
      lowerCompPrimitive m theta
    (_, CompPiElimDownElim v ds) -> do
      (xs, vs) <- unzip <$> mapM (newValueLocal . takeBaseName) ds
      (fun, castThen) <- llvmCast (Just $ takeBaseName v) v $ toFunPtrType ds
      castThenCall <- castThen $ LowCompCall fun vs
      lowerValueLet' (zip xs ds) castThenCall
    (_, CompSigmaElim xs v e) -> do
      let basePtrType = LowTypePtr $ LowTypeArray (length xs) voidPtr -- base pointer type  ([(length xs) x ARRAY_ELEM_TYPE])
      let idxList = map (\i -> (LowValueInt i, i32)) [0 ..]
      ys <- mapM newNameWith xs
      let xts' = zip xs (repeat voidPtr)
      loadContent v basePtrType (zip idxList (zip ys xts')) e
    (_, CompUpIntro d) -> do
      result <- newNameWith' $ takeBaseName d
      lowerValueLet result d $ LowCompReturn $ LowValueLocal result
    (_, CompUpElim x e1 e2) -> do
      e1' <- lowerComp e1
      e2' <- lowerComp e2
      commConv x e1' e2'
    (_, CompEnumElim v branchList) -> do
      m <- constructSwitch branchList
      case m of
        Nothing ->
          return LowCompUnreachable
        Just (defaultCase, caseList) -> do
          let t = LowTypeInt 64
          (cast, castThen) <- llvmCast (Just "enum-base") v t
          castThen $ LowCompSwitch (cast, t) defaultCase caseList

uncastList :: [(Ident, (Ident, LowType))] -> CompPlus -> WithEnv LowComp
uncastList args e =
  case args of
    [] ->
      lowerComp e
    ((y, (x, et)) : yxs) -> do
      e' <- uncastList yxs e
      llvmUncastLet x (LowValueLocal y) et e'

takeBaseName :: ValuePlus -> T.Text
takeBaseName term =
  case term of
    (_, ValueConst s) ->
      s
    (_, ValueUpsilon (I (s, _))) ->
      s
    (_, ValueSigmaIntro ds) ->
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

takeBaseName' :: LowValue -> T.Text
takeBaseName' lowerValue =
  case lowerValue of
    LowValueLocal (I (s, _)) ->
      s
    LowValueGlobal s ->
      s
    LowValueInt _ ->
      "int"
    LowValueFloat FloatSize16 _ ->
      "half"
    LowValueFloat FloatSize32 _ ->
      "float"
    LowValueFloat FloatSize64 _ ->
      "double"
    LowValueNull ->
      "null"

loadContent ::
  ValuePlus -> -- base pointer
  LowType -> -- the type of base pointer
  [((LowValue, LowType), (Ident, (Ident, LowType)))] -> -- [(the index of an element, the variable to load the element)]
  CompPlus -> -- continuation
  WithEnv LowComp
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
  LowValue -> -- base pointer
  LowType -> -- the type of base pointer
  [((LowValue, LowType), (Ident, LowType))] -> -- [(the index of an element, the variable to keep the loaded content)]
  LowComp -> -- continuation
  WithEnv LowComp
loadContent' bp bt values cont =
  case values of
    [] -> do
      l <- llvmUncast (Just $ takeBaseName' bp) bp bt
      tmp <- newNameWith'' $ Just $ takeBaseName' bp
      j <- newCount
      commConv tmp l $ LowCompCont (LowOpFree (LowValueLocal tmp) bt j) cont
    (i, (x, et)) : xis -> do
      cont' <- loadContent' bp bt xis cont
      (posName, pos) <- newValueLocal' (Just $ asText x)
      return $
        LowCompLet
          posName
          (LowOpGetElementPtr (bp, bt) [(LowValueInt 0, LowTypeInt 32), i])
          $ LowCompLet x (LowOpLoad pos et) cont'

lowerCompPrimitive :: Hint -> Primitive -> WithEnv LowComp
lowerCompPrimitive _ codeOp =
  case codeOp of
    PrimitiveUnaryOp op v ->
      lowerCompUnaryOp op v
    PrimitiveBinaryOp op v1 v2 ->
      lowerCompBinaryOp op v1 v2
    PrimitiveExploit expKind args -> do
      (xs, vs) <- unzip <$> mapM (const $ newValueLocal "sys-call-arg") args
      case expKind of
        ExploitKindSyscall i -> do
          call <- syscallToLowComp i vs
          lowerValueLet' (zip xs args) call
        ExploitKindExternal name -> do
          call <- externalToLowComp name vs
          lowerValueLet' (zip xs args) call
        ExploitKindLoad valueLowType -> do
          let ptr = args !! 0
          (ptrVar, castPtrThen) <- llvmCast (Just $ takeBaseName ptr) ptr (LowTypePtr valueLowType)
          resName <- newNameWith' "result"
          uncast <- llvmUncast (Just $ asText resName) (LowValueLocal resName) valueLowType
          castPtrThen $
            LowCompLet resName (LowOpLoad ptrVar valueLowType) uncast
        ExploitKindStore valueLowType -> do
          let ptr = args !! 0
          let val = args !! 1
          (ptrVar, castPtrThen) <- llvmCast (Just $ takeBaseName ptr) ptr (LowTypePtr valueLowType)
          (valVar, castValThen) <- llvmCast (Just $ takeBaseName val) val valueLowType
          (castPtrThen >=> castValThen) $
            LowCompCont (LowOpStore valueLowType valVar ptrVar) $
              LowCompReturn (LowValueInt 0)

lowerCompUnaryOp :: UnaryOp -> ValuePlus -> WithEnv LowComp
lowerCompUnaryOp op d = do
  let (domType, codType) = unaryOpToDomCod op
  (x, castThen) <- llvmCast (Just "unary-op") d domType
  result <- newNameWith' "unary-op-result"
  uncast <- llvmUncast (Just $ asText result) (LowValueLocal result) codType
  castThen $ LowCompLet result (LowOpUnaryOp op x) uncast

lowerCompBinaryOp :: BinaryOp -> ValuePlus -> ValuePlus -> WithEnv LowComp
lowerCompBinaryOp op v1 v2 = do
  let (domType, codType) = binaryOpToDomCod op
  (x1, cast1then) <- llvmCast (Just "binary-op-fst") v1 domType
  (x2, cast2then) <- llvmCast (Just "binary-op-snd") v2 domType
  result <- newNameWith' "binary-op-result"
  uncast <- llvmUncast (Just $ asText result) (LowValueLocal result) codType
  (cast1then >=> cast2then) $ LowCompLet result (LowOpBinaryOp op x1 x2) uncast

llvmCast ::
  Maybe T.Text ->
  ValuePlus ->
  LowType ->
  WithEnv (LowValue, LowComp -> WithEnv LowComp)
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
        ( LowValueLocal x,
          lowerValueLet tmp v
            . LowCompLet x (LowOpBitcast (LowValueLocal tmp) voidPtr lowType)
        )

llvmCastInt ::
  Maybe T.Text -> -- base name for newly created variables
  ValuePlus ->
  LowType ->
  WithEnv (LowValue, LowComp -> WithEnv LowComp)
llvmCastInt mName v lowType = do
  x <- newNameWith'' mName
  y <- newNameWith'' mName
  return
    ( LowValueLocal y,
      lowerValueLet x v
        . LowCompLet
          y
          (LowOpPointerToInt (LowValueLocal x) voidPtr lowType)
    )

llvmCastFloat ::
  Maybe T.Text -> -- base name for newly created variables
  ValuePlus ->
  FloatSize ->
  WithEnv (LowValue, LowComp -> WithEnv LowComp)
llvmCastFloat mName v size = do
  let floatType = LowTypeFloat size
  let intType = LowTypeInt $ sizeAsInt size
  (xName, x) <- newValueLocal' mName
  (yName, y) <- newValueLocal' mName
  z <- newNameWith'' mName
  return
    ( LowValueLocal z,
      lowerValueLet xName v
        . LowCompLet yName (LowOpPointerToInt x voidPtr intType)
        . LowCompLet z (LowOpBitcast y intType floatType)
    )

-- uncast: {some-concrete-type} -> voidPtr
llvmUncast :: Maybe T.Text -> LowValue -> LowType -> WithEnv LowComp
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
        LowCompLet x (LowOpBitcast result lowType voidPtr) $
          LowCompReturn (LowValueLocal x)

llvmUncastInt :: Maybe T.Text -> LowValue -> LowType -> WithEnv LowComp
llvmUncastInt mName result lowType = do
  x <- newNameWith'' mName
  return $
    LowCompLet x (LowOpIntToPointer result lowType voidPtr) $
      LowCompReturn (LowValueLocal x)

llvmUncastFloat :: Maybe T.Text -> LowValue -> FloatSize -> WithEnv LowComp
llvmUncastFloat mName floatResult i = do
  let floatType = LowTypeFloat i
  let intType = LowTypeInt $ sizeAsInt i
  tmp <- newNameWith'' mName
  x <- newNameWith'' mName
  return $
    LowCompLet tmp (LowOpBitcast floatResult floatType intType) $
      LowCompLet x (LowOpIntToPointer (LowValueLocal tmp) intType voidPtr) $
        LowCompReturn (LowValueLocal x)

llvmUncastLet :: Ident -> LowValue -> LowType -> LowComp -> WithEnv LowComp
llvmUncastLet x@(I (s, _)) d lowType cont = do
  l <- llvmUncast (Just s) d lowType
  commConv x l cont

-- `lowerValueLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
lowerValueLet :: Ident -> ValuePlus -> LowComp -> WithEnv LowComp
lowerValueLet x lowerValue cont =
  case lowerValue of
    (m, ValueConst y) -> do
      cenv <- gets codeEnv
      lenv <- gets lowCompEnv
      case Map.lookup y cenv of
        Nothing ->
          raiseCritical m $ "no such global label defined: " <> y
        Just (Definition _ args e)
          | not (Map.member y lenv) -> do
            insLowCompEnv y args LowCompUnreachable
            llvm <- reduceCompPlus e >>= lowerComp
            insLowCompEnv y args llvm
            llvmUncastLet x (LowValueGlobal y) (toFunPtrType args) cont
          | otherwise ->
            llvmUncastLet x (LowValueGlobal y) (toFunPtrType args) cont
    (_, ValueUpsilon y) ->
      llvmUncastLet x (LowValueLocal y) voidPtr cont
    (m, ValueSigmaIntro ds) -> do
      let arrayType = AggPtrTypeArray (length ds) voidPtr
      let dts = zip ds (repeat voidPtr)
      storeContent m x arrayType dts cont
    (_, ValueInt size l) ->
      llvmUncastLet x (LowValueInt l) (LowTypeInt size) cont
    (_, ValueFloat size f) ->
      llvmUncastLet x (LowValueFloat size f) (LowTypeFloat size) cont
    (m, ValueEnumIntro l) -> do
      i <- toInteger <$> getEnumNum m l
      llvmUncastLet x (LowValueInt i) (LowTypeInt 64) cont

syscallToLowComp :: Integer -> [LowValue] -> WithEnv LowComp
syscallToLowComp num ds = do
  res <- newNameWith' "result"
  return $
    LowCompLet res (LowOpSyscall num ds) $
      LowCompReturn (LowValueLocal res)

externalToLowComp :: T.Text -> [LowValue] -> WithEnv LowComp
externalToLowComp name ds = do
  denv <- gets declEnv
  when (not $ name `Map.member` denv) $ do
    let dom = map (const voidPtr) ds
    let cod = voidPtr
    modify (\env -> env {declEnv = Map.insert name (dom, cod) denv})
  return $ LowCompCall (LowValueGlobal name) ds

lowerValueLet' :: [(Ident, ValuePlus)] -> LowComp -> WithEnv LowComp
lowerValueLet' binder cont =
  case binder of
    [] ->
      return cont
    (x, d) : rest -> do
      cont' <- lowerValueLet' rest cont
      lowerValueLet x d cont'

-- returns Nothing iff the branch list is empty
constructSwitch :: [(EnumCase, CompPlus)] -> WithEnv (Maybe (LowComp, [(Int, LowComp)]))
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
  LowComp ->
  WithEnv LowComp
storeContent m reg aggPtrType dts cont = do
  let lowType = toLowType aggPtrType
  (cast, castThen) <- llvmCast (Just $ asText reg) (m, ValueUpsilon reg) lowType
  storeThenCont <- storeContent' cast lowType (zip [0 ..] dts) cont
  castThenStoreThenCont <- castThen storeThenCont
  -- Use getelementptr to realize `sizeof`. More info:
  --   http://nondot.org/sabre/LowCompNotes/SizeOf-OffsetOf-VariableSizedStructs.txt
  case aggPtrType of
    AggPtrTypeStruct ts ->
      storeContent'' reg (LowTypeStruct ts) lowType 1 castThenStoreThenCont
    AggPtrTypeArray len t ->
      storeContent'' reg t lowType len castThenStoreThenCont

storeContent' ::
  LowValue -> -- base pointer
  LowType -> -- the type of base pointer (like [n x u8]*, {i8*, i8*}*, etc.)
  [(Integer, (ValuePlus, LowType))] -> -- [(the index of an element, the element to be stored)]
  LowComp -> -- continuation
  WithEnv LowComp
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
        LowCompLet
          locName
          (LowOpGetElementPtr (bp, bt) [(LowValueInt 0, i32), (LowValueInt i, it)])
          $ LowCompCont (LowOpStore et cast loc) cont'

storeContent'' :: Ident -> LowType -> SizeInfo -> Int -> LowComp -> WithEnv LowComp
storeContent'' reg elemType sizeInfo len cont = do
  (c, cVar) <- newValueLocal $ "sizeof-" <> asText reg
  return $
    LowCompLet
      c
      ( LowOpGetElementPtr
          (LowValueNull, LowTypePtr elemType)
          [(LowValueInt (toInteger len), i64)]
      )
      $ LowCompLet reg (LowOpAlloc cVar sizeInfo) cont

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

newValueLocal :: T.Text -> WithEnv (Ident, LowValue)
newValueLocal name = do
  x <- newNameWith' name
  return (x, LowValueLocal x)

newValueLocal' :: Maybe T.Text -> WithEnv (Ident, LowValue)
newValueLocal' mName = do
  x <- newNameWith'' mName
  return (x, LowValueLocal x)

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

insLowCompEnv :: T.Text -> [Ident] -> LowComp -> WithEnv ()
insLowCompEnv funName args e =
  modify (\env -> env {lowCompEnv = Map.insert funName (args, e) (lowCompEnv env)})

commConv :: Ident -> LowComp -> LowComp -> WithEnv LowComp
commConv x llvm cont2 =
  case llvm of
    LowCompReturn d ->
      return $ LowCompLet x (LowOpBitcast d voidPtr voidPtr) cont2 -- nop
    LowCompLet y op cont1 -> do
      cont <- commConv x cont1 cont2
      return $ LowCompLet y op cont
    LowCompCont op cont1 -> do
      cont <- commConv x cont1 cont2
      return $ LowCompCont op cont
    LowCompSwitch (d, t) defaultCase caseList -> do
      let (ds, es) = unzip caseList
      es' <- mapM (\e -> commConv x e cont2) es
      let caseList' = zip ds es'
      defaultCase' <- commConv x defaultCase cont2
      return $ LowCompSwitch (d, t) defaultCase' caseList'
    LowCompCall d ds ->
      return $ LowCompLet x (LowOpCall d ds) cont2
    LowCompUnreachable ->
      return LowCompUnreachable
