module Lower
  ( lower,
  )
where

import Control.Monad
import Data.Basic
import Data.Comp
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.Log
import Data.LowComp
import Data.LowType
import qualified Data.Text as T
import Path

lower :: CompPlus -> IO LowComp
lower mainTerm@(m, _) = do
  mainTerm'' <- lowerComp mainTerm
  -- the result of "main" must be i64, not i8*
  (result, resultVar) <- newValueVarLocalWith m "result"
  (cast, castThen) <- llvmCast (Just "cast") resultVar (LowTypeInt 64)
  castResult <- castThen (LowCompReturn cast)
  -- let result: i8* := (main-term) in {cast result to i64}
  commConv result mainTerm'' castResult

lowerComp :: CompPlus -> IO LowComp
lowerComp term =
  case term of
    (m, CompPrimitive theta) ->
      lowerCompPrimitive m theta
    (_, CompPiElimDownElim v ds) -> do
      (xs, vs) <- unzip <$> mapM (newValueLocal . takeBaseName) ds
      (fun, castThen) <- llvmCast (Just $ takeBaseName v) v $ toFunPtrType ds
      castThenCall <- castThen $ LowCompCall fun vs
      lowerValueLet' (zip xs ds) castThenCall
    (_, CompSigmaElim isNoetic xs v e) -> do
      let basePtrType = LowTypePointer $ LowTypeArray (length xs) voidPtr -- base pointer type  ([(length xs) x ARRAY_ELEM_TYPE])
      let idxList = map (\i -> (LowValueInt i, LowTypeInt 32)) [0 ..]
      ys <- mapM newIdentFromIdent xs
      let xts' = zip xs (repeat voidPtr)
      loadContent isNoetic v basePtrType (zip idxList (zip ys xts')) e
    (_, CompUpIntro d) -> do
      result <- newIdentFromText $ takeBaseName d
      lowerValueLet result d $ LowCompReturn $ LowValueVarLocal result
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
    (_, CompIgnore e) ->
      lowerComp e

uncastList :: [(Ident, (Ident, LowType))] -> CompPlus -> IO LowComp
uncastList args e =
  case args of
    [] ->
      lowerComp e
    ((y, (x, et)) : yxs) -> do
      e' <- uncastList yxs e
      llvmUncastLet x (LowValueVarLocal y) et e'

takeBaseName :: ValuePlus -> T.Text
takeBaseName term =
  case term of
    (_, ValueVarGlobal s) ->
      s
    (_, ValueVarLocal (I (s, _))) ->
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
    (_, ValueEnumIntro {}) ->
      "i64"

takeBaseName' :: LowValue -> T.Text
takeBaseName' lowerValue =
  case lowerValue of
    LowValueVarLocal (I (s, _)) ->
      s
    LowValueVarGlobal s ->
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
  Bool -> -- noetic-or-not
  ValuePlus -> -- base pointer
  LowType -> -- the type of base pointer
  [((LowValue, LowType), (Ident, (Ident, LowType)))] -> -- [(the index of an element, the variable to load the element)]
  CompPlus -> -- continuation
  IO LowComp
loadContent isNoetic v bt iyxs cont =
  case iyxs of
    [] ->
      lowerComp cont
    _ -> do
      let ixs = map (\(i, (y, (_, k))) -> (i, (y, k))) iyxs
      (bp, castThen) <- llvmCast (Just $ takeBaseName v) v bt
      let yxs = map (\(_, yx) -> yx) iyxs
      uncastThenCont <- uncastList yxs cont
      extractThenFreeThenUncastThenCont <- loadContent' isNoetic bp bt ixs uncastThenCont
      castThen extractThenFreeThenUncastThenCont

loadContent' ::
  Bool -> -- noetic-or-not
  LowValue -> -- base pointer
  LowType -> -- the type of base pointer
  [((LowValue, LowType), (Ident, LowType))] -> -- [(the index of an element, the variable to keep the loaded content)]
  LowComp -> -- continuation
  IO LowComp
loadContent' isNoetic bp bt values cont =
  case values of
    []
      | isNoetic ->
        return cont
      | otherwise -> do
        l <- llvmUncast (Just $ takeBaseName' bp) bp bt
        tmp <- newNameWith $ Just $ takeBaseName' bp
        j <- newCount
        commConv tmp l $ LowCompCont (LowOpFree (LowValueVarLocal tmp) bt j) cont
    (i, (x, et)) : xis -> do
      cont' <- loadContent' isNoetic bp bt xis cont
      (posName, pos) <- newValueLocal' (Just $ asText x)
      return $
        LowCompLet
          posName
          (LowOpGetElementPtr (bp, bt) [(LowValueInt 0, LowTypeInt 32), i])
          $ LowCompLet x (LowOpLoad pos et) cont'

lowerCompPrimitive :: Hint -> Primitive -> IO LowComp
lowerCompPrimitive m codeOp =
  case codeOp of
    PrimitivePrimOp op vs ->
      lowerCompPrimOp op vs
    PrimitiveDerangement expKind args -> do
      case expKind of
        DerangementNop -> do
          (x, v) <- newValueLocal "nop-arg"
          lowerValueLet x (args !! 0) $ LowCompReturn v
        DerangementSyscall i -> do
          (xs, vs) <- unzip <$> mapM (const $ newValueLocal "sys-call-arg") args
          res <- newIdentFromText "result"
          lowerValueLet' (zip xs args) $
            LowCompLet res (LowOpSyscall i vs) $
              LowCompReturn (LowValueVarLocal res)
        DerangementExternal name -> do
          (xs, vs) <- unzip <$> mapM (const $ newValueLocal "ext-call-arg") args
          denv <- readIORef declEnv
          when (not $ name `Map.member` denv) $ do
            let dom = map (const voidPtr) vs
            let cod = voidPtr
            modifyIORef' declEnv $ \env -> Map.insert name (dom, cod) env
          lowerValueLet' (zip xs args) $ LowCompCall (LowValueVarGlobal name) vs
        DerangementLoad valueLowType -> do
          let ptr = args !! 0
          (ptrVar, castPtrThen) <- llvmCast (Just $ takeBaseName ptr) ptr (LowTypePointer valueLowType)
          resName <- newIdentFromText "result"
          uncast <- llvmUncast (Just $ asText resName) (LowValueVarLocal resName) valueLowType
          castPtrThen $
            LowCompLet resName (LowOpLoad ptrVar valueLowType) uncast
        DerangementStore valueLowType -> do
          let ptr = args !! 0
          let val = args !! 1
          (ptrVar, castPtrThen) <- llvmCast (Just $ takeBaseName ptr) ptr (LowTypePointer valueLowType)
          (valVar, castValThen) <- llvmCast (Just $ takeBaseName val) val valueLowType
          (castPtrThen >=> castValThen) $
            LowCompCont (LowOpStore valueLowType valVar ptrVar) $
              LowCompReturn LowValueNull
        DerangementCreateArray elemType -> do
          let arrayType = AggPtrTypeArray (length args) elemType
          let argTypeList = zip args (repeat elemType)
          resName <- newIdentFromText "result"
          storeContent m resName arrayType argTypeList (LowCompReturn (LowValueVarLocal resName))
        DerangementCreateStruct elemTypeList -> do
          let structType = AggPtrTypeStruct elemTypeList
          let argTypeList = zip args elemTypeList
          resName <- newIdentFromText "result"
          storeContent m resName structType argTypeList (LowCompReturn (LowValueVarLocal resName))

lowerCompPrimOp :: PrimOp -> [ValuePlus] -> IO LowComp
lowerCompPrimOp op@(PrimOp _ domList cod) vs = do
  (argVarList, castArgsThen) <- llvmCastPrimArgs $ zip vs domList
  result <- newIdentFromText "prim-op-result"
  uncast <- llvmUncast (Just $ asText result) (LowValueVarLocal result) cod
  castArgsThen $ LowCompLet result (LowOpPrimOp op argVarList) uncast

llvmCastPrimArgs :: [(ValuePlus, LowType)] -> IO ([LowValue], LowComp -> IO LowComp)
llvmCastPrimArgs dts =
  case dts of
    [] ->
      return ([], return)
    ((d, t) : rest) -> do
      (argVarList, cont) <- llvmCastPrimArgs rest
      (argVar, castThen) <- llvmCast (Just "prim-op") d t
      return (argVar : argVarList, castThen >=> cont)

llvmCast ::
  Maybe T.Text ->
  ValuePlus ->
  LowType ->
  IO (LowValue, LowComp -> IO LowComp)
llvmCast mName v lowType =
  case lowType of
    LowTypeInt _ ->
      llvmCastInt mName v lowType
    LowTypeFloat i ->
      llvmCastFloat mName v i
    _ -> do
      tmp <- newNameWith mName
      x <- newNameWith mName
      return
        ( LowValueVarLocal x,
          lowerValueLet tmp v
            . LowCompLet x (LowOpBitcast (LowValueVarLocal tmp) voidPtr lowType)
        )

llvmCastInt ::
  Maybe T.Text -> -- base name for newly created variables
  ValuePlus ->
  LowType ->
  IO (LowValue, LowComp -> IO LowComp)
llvmCastInt mName v lowType = do
  x <- newNameWith mName
  y <- newNameWith mName
  return
    ( LowValueVarLocal y,
      lowerValueLet x v
        . LowCompLet
          y
          (LowOpPointerToInt (LowValueVarLocal x) voidPtr lowType)
    )

llvmCastFloat ::
  Maybe T.Text -> -- base name for newly created variables
  ValuePlus ->
  FloatSize ->
  IO (LowValue, LowComp -> IO LowComp)
llvmCastFloat mName v size = do
  let floatType = LowTypeFloat size
  let intType = LowTypeInt $ sizeAsInt size
  (xName, x) <- newValueLocal' mName
  (yName, y) <- newValueLocal' mName
  z <- newNameWith mName
  return
    ( LowValueVarLocal z,
      lowerValueLet xName v
        . LowCompLet yName (LowOpPointerToInt x voidPtr intType)
        . LowCompLet z (LowOpBitcast y intType floatType)
    )

-- uncast: {some-concrete-type} -> voidPtr
llvmUncast :: Maybe T.Text -> LowValue -> LowType -> IO LowComp
llvmUncast mName result lowType =
  case lowType of
    LowTypeInt _ ->
      llvmUncastInt mName result lowType
    LowTypeFloat i ->
      llvmUncastFloat mName result i
    _ -> do
      x <- newNameWith mName
      return $
        LowCompLet x (LowOpBitcast result lowType voidPtr) $
          LowCompReturn (LowValueVarLocal x)

llvmUncastInt :: Maybe T.Text -> LowValue -> LowType -> IO LowComp
llvmUncastInt mName result lowType = do
  x <- newNameWith mName
  return $
    LowCompLet x (LowOpIntToPointer result lowType voidPtr) $
      LowCompReturn (LowValueVarLocal x)

llvmUncastFloat :: Maybe T.Text -> LowValue -> FloatSize -> IO LowComp
llvmUncastFloat mName floatResult i = do
  let floatType = LowTypeFloat i
  let intType = LowTypeInt $ sizeAsInt i
  tmp <- newNameWith mName
  x <- newNameWith mName
  return $
    LowCompLet tmp (LowOpBitcast floatResult floatType intType) $
      LowCompLet x (LowOpIntToPointer (LowValueVarLocal tmp) intType voidPtr) $
        LowCompReturn (LowValueVarLocal x)

llvmUncastLet :: Ident -> LowValue -> LowType -> LowComp -> IO LowComp
llvmUncastLet x@(I (s, _)) d lowType cont = do
  l <- llvmUncast (Just s) d lowType
  commConv x l cont

-- `lowerValueLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
lowerValueLet :: Ident -> ValuePlus -> LowComp -> IO LowComp
lowerValueLet x lowerValue cont =
  case lowerValue of
    (m, ValueVarGlobal y) -> do
      denv <- readIORef defEnv
      lenv <- readIORef lowDefEnv
      case Map.lookup y denv of
        Nothing ->
          raiseCritical m $ "no such global label defined: " <> y
        Just (_, args, e)
          | not (Map.member y lenv) -> do
            insLowDefEnv y args LowCompUnreachable
            llvm <- lowerComp e
            insLowDefEnv y args llvm
            llvmUncastLet x (LowValueVarGlobal y) (toFunPtrType args) cont
          | otherwise ->
            llvmUncastLet x (LowValueVarGlobal y) (toFunPtrType args) cont
    (_, ValueVarLocal y) ->
      llvmUncastLet x (LowValueVarLocal y) voidPtr cont
    (m, ValueSigmaIntro ds) -> do
      let arrayType = AggPtrTypeArray (length ds) voidPtr
      let dts = zip ds (repeat voidPtr)
      storeContent m x arrayType dts cont
    (_, ValueInt size l) ->
      llvmUncastLet x (LowValueInt l) (LowTypeInt size) cont
    (_, ValueFloat size f) ->
      llvmUncastLet x (LowValueFloat size f) (LowTypeFloat size) cont
    (m, ValueEnumIntro path l) -> do
      i <- toInteger <$> getEnumNum m path l
      llvmUncastLet x (LowValueInt i) (LowTypeInt 64) cont

lowerValueLet' :: [(Ident, ValuePlus)] -> LowComp -> IO LowComp
lowerValueLet' binder cont =
  case binder of
    [] ->
      return cont
    (x, d) : rest -> do
      cont' <- lowerValueLet' rest cont
      lowerValueLet x d cont'

-- returns Nothing iff the branch list is empty
constructSwitch :: [(EnumCase, CompPlus)] -> IO (Maybe (LowComp, [(Int, LowComp)]))
constructSwitch switch =
  case switch of
    [] ->
      return Nothing
    (EnumCaseDefault, code) : _ -> do
      code' <- lowerComp code
      return $ Just (code', [])
    [(_, code)] -> do
      constructSwitch [(EnumCaseDefault, code)]
    (EnumCaseLabel path l, code@(m, _)) : rest -> do
      i <- enumValueToInteger m path l
      constructSwitch $ (EnumCaseInt i, code) : rest
    (EnumCaseInt i, code) : rest -> do
      code' <- lowerComp code
      mSwitch <- constructSwitch rest
      return $ do
        (defaultCase, caseList) <- mSwitch
        return (defaultCase, (i, code') : caseList)

data AggPtrType
  = AggPtrTypeArray Int LowType
  | AggPtrTypeStruct [LowType]

toLowType :: AggPtrType -> LowType
toLowType aggPtrType =
  case aggPtrType of
    AggPtrTypeArray i t ->
      LowTypePointer $ LowTypeArray i t
    AggPtrTypeStruct ts ->
      LowTypePointer $ LowTypeStruct ts

storeContent ::
  Hint ->
  Ident ->
  AggPtrType ->
  [(ValuePlus, LowType)] ->
  LowComp ->
  IO LowComp
storeContent m reg aggPtrType dts cont = do
  let lowType = toLowType aggPtrType
  (cast, castThen) <- llvmCast (Just $ asText reg) (m, ValueVarLocal reg) lowType
  storeThenCont <- storeContent' cast lowType (zip [0 ..] dts) cont
  castThenStoreThenCont <- castThen storeThenCont
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
  IO LowComp
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
          (LowOpGetElementPtr (bp, bt) [(LowValueInt 0, LowTypeInt 32), (LowValueInt i, it)])
          $ LowCompCont (LowOpStore et cast loc) cont'

storeContent'' :: Ident -> LowType -> SizeInfo -> Int -> LowComp -> IO LowComp
storeContent'' reg elemType sizeInfo len cont = do
  (tmp, tmpVar) <- newValueLocal $ "sizeof-" <> asText reg
  (c, cVar) <- newValueLocal $ "sizeof-" <> asText reg
  uncastThenAllocThenCont <- llvmUncastLet c tmpVar (LowTypePointer elemType) (LowCompLet reg (LowOpAlloc cVar sizeInfo) cont)
  return $
    LowCompLet
      tmp
      ( LowOpGetElementPtr
          (LowValueNull, LowTypePointer elemType)
          [(LowValueInt (toInteger len), LowTypeInt 64)]
      )
      uncastThenAllocThenCont

indexTypeOf :: LowType -> LowType
indexTypeOf lowType =
  case lowType of
    LowTypePointer (LowTypeStruct _) ->
      LowTypeInt 32
    _ ->
      LowTypeInt 64

toFunPtrType :: [a] -> LowType
toFunPtrType xs =
  LowTypePointer (LowTypeFunction (map (const voidPtr) xs) voidPtr)

newValueLocal :: T.Text -> IO (Ident, LowValue)
newValueLocal name = do
  x <- newIdentFromText name
  return (x, LowValueVarLocal x)

newValueLocal' :: Maybe T.Text -> IO (Ident, LowValue)
newValueLocal' mName = do
  x <- newNameWith mName
  return (x, LowValueVarLocal x)

newNameWith :: Maybe T.Text -> IO Ident
newNameWith mName =
  case mName of
    Nothing ->
      newIdentFromText "var"
    Just name ->
      newIdentFromText name

enumValueToInteger :: Hint -> Path Abs File -> T.Text -> IO Int
enumValueToInteger m path l =
  getEnumNum m path l

getEnumNum :: Hint -> Path Abs File -> T.Text -> IO Int
getEnumNum m path label = do
  renv <- readIORef revEnumEnv
  case Map.lookup label renv of
    Just (fp, _, i)
      | fp == path ->
        return i
    _ ->
      raiseCritical m $ "no such enum is defined: " <> label

insLowDefEnv :: T.Text -> [Ident] -> LowComp -> IO ()
insLowDefEnv funName args e =
  modifyIORef' lowDefEnv $ \env -> Map.insert funName (args, e) env

commConv :: Ident -> LowComp -> LowComp -> IO LowComp
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
