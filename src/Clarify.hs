--
-- clarification == polarization + closure conversion + linearization
--
module Clarify
  ( clarify
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nubBy)

import Clarify.Closure
import Clarify.Sigma
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
import Data.Term
import Reduce.Term

import qualified Text.Show.Pretty as Pr

clarify :: TermPlus -> WithEnv CodePlus
clarify = clarify' []

clarify' :: Context -> TermPlus -> WithEnv CodePlus
clarify' _ (m, TermTau) = do
  v <- cartesianUniv m
  return (m, CodeUpIntro v)
clarify' ctx (m, TermUpsilon x)
  -- enum.n{i} ~> i  (i.e. the size of n{i})
  | Just i <- asEnumNatNumConstant x = clarify' ctx (m, TermIntS 64 i)
  -- i64, f32, u1234, etc ~> cartesianImmediate
  | Just _ <- asLowTypeMaybe x =
    clarify' ctx (m, TermEnum $ EnumTypeLabel "top")
  | otherwise = do
    cenv <- gets constantEnv
    if x `elem` cenv
      then return (m, CodeUpIntro (m, DataTheta x)) -- global
      else return (m, CodeUpIntro (m, DataUpsilon x)) -- local
clarify' _ (m, TermPi _ _) = do
  returnClosureType m
clarify' ctx lam@(m, TermPiIntro xts e) = do
  fvs <- varTermPlus ctx lam
  e' <- clarify' (reverse xts ++ ctx) e
  makeClosure' ctx Nothing fvs m xts e'
clarify' ctx (m, TermPiElim e es) = do
  e' <- clarify' ctx e
  callClosure' ctx m e' es
clarify' ctx mu@(m, TermMu (f, t) e) = do
  fvs <- varTermPlus ctx mu
  let fvs' = map (toTermUpsilon . fst) fvs
  -- set f as a global variable
  modify (\env -> env {constantEnv = f : constantEnv env})
  -- let e' = substTermPlus [(f, (m, TermPiElim (m, TermTheta f) fvs'))] e
  let e' = substTermPlus [(f, (m, TermPiElim (m, TermUpsilon f) fvs'))] e
  e'' <- clarify' ((f, t) : ctx) e'
  cls <- makeClosure' ctx (Just f) [] m fvs e''
  callClosure' ctx m cls fvs'
clarify' _ (m, TermIntS size l) = do
  return (m, CodeUpIntro (m, DataIntS size l))
clarify' _ (m, TermIntU size l) = do
  return (m, CodeUpIntro (m, DataIntU size l))
clarify' _ (m, TermFloat16 l) = do
  return (m, CodeUpIntro (m, DataFloat16 l))
clarify' _ (m, TermFloat32 l) = do
  return (m, CodeUpIntro (m, DataFloat32 l))
clarify' _ (m, TermFloat64 l) = do
  return (m, CodeUpIntro (m, DataFloat64 l))
clarify' _ (m, TermEnum _) = do
  v <- cartesianImmediate m
  return (m, CodeUpIntro v)
clarify' _ (m, TermEnumIntro l) = do
  return (m, CodeUpIntro (m, DataEnumIntro l))
clarify' ctx (m, TermEnumElim e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM (clarify' ctx) es
  (yName, e', y) <- clarifyPlus ctx e
  return $ bindLet [(yName, e')] (m, CodeEnumElim y (zip cs es'))
clarify' _ (m, TermArray _ _) = do
  returnArrayType m
clarify' ctx (m, TermArrayIntro k les) = do
  v <- cartesianImmediate m
  let retKindType = (m, CodeUpIntro v)
  -- arrayType = Sigma [_ : IMMEDIATE, ..., _ : IMMEDIATE]
  name <- newNameWith "array"
  arrayType <-
    cartesianSigma name m $ map Left $ replicate (length les) retKindType
  let (ls, es) = unzip les
  (zs, es', xs) <- unzip3 <$> mapM (clarifyPlus ctx) es
  return $
    bindLet (zip zs es') $
    ( m
    , CodeUpIntro $
      (m, DataSigmaIntro [arrayType, (m, DataArrayIntro k (zip ls xs))]))
clarify' ctx (m, TermArrayElim k e1 e2) = do
  e1' <- clarify' ctx e1
  e2' <- clarify' ctx e2
  (arrVarName, arrVar) <- newDataUpsilonWith "arr"
  (idxVarName, idxVar) <- newDataUpsilonWith "idx"
  affVarName <- newNameWith "aff"
  relVarName <- newNameWith "rel"
  (contentTypeVarName, contentTypeVar) <- newDataUpsilonWith "array-type"
  (contentVarName, contentVar) <- newDataUpsilonWith "array-content"
  retUnivType <- returnCartesianUniv
  retImmType <- returnCartesianImmediate
  let retContentType = (m, CodeUpIntro contentTypeVar)
  -- array : Sigma [content-type : univ, content : content-type]
  return $
    bindLet [(arrVarName, e1'), (idxVarName, e2')] $
    ( m
    , CodeSigmaElim
        [(contentTypeVarName, retUnivType), (contentVarName, retContentType)]
        arrVar
        ( m
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            contentTypeVar
            (m, CodeArrayElim k contentVar idxVar)))

clarifyPlus :: Context -> TermPlus -> WithEnv (Identifier, CodePlus, DataPlus)
clarifyPlus ctx e@(m, _) = do
  e' <- clarify' ctx e
  (varName, var) <- newDataUpsilonWith' "var" m
  return (varName, e', var)

clarifyTheta :: Context -> Meta -> Identifier -> WithEnv CodePlus
clarifyTheta ctx m name
  | Just (lowType, op) <- asUnaryOpMaybe name =
    clarifyUnaryOp ctx name op lowType m
clarifyTheta ctx m name
  | Just (lowType, op) <- asBinaryOpMaybe name =
    clarifyBinaryOp ctx name op lowType m
clarifyTheta ctx m name
  | Just (sysCall, len, idxList) <- asSysCallMaybe name =
    clarifySysCall ctx name sysCall len idxList m
clarifyTheta ctx m name
  | Just _ <- asLowTypeMaybe name =
    clarify' ctx (m, TermEnum $ EnumTypeLabel "top")
clarifyTheta ctx m "is-enum" = clarifyIsEnum ctx m
clarifyTheta ctx m "unsafe.eval-io" = clarifyEvalIO ctx m
clarifyTheta ctx m "file-descriptor" = clarify' ctx (m, TermUpsilon "i64")
clarifyTheta ctx m "stdin" = clarify' ctx (m, TermIntS 64 0)
clarifyTheta ctx m "stdout" = clarify' ctx (m, TermIntS 64 1)
clarifyTheta ctx m "stderr" = clarify' ctx (m, TermIntS 64 2)
clarifyTheta ctx m name = do
  mx <- asEnumConstant name
  case mx of
    Just i -> clarify' ctx (m, TermIntS 64 i) -- enum.top ~> 1, enum.choice ~> 2, etc.
    -- muで導入されたthetaに由来するものもここにくる。
    -- たぶんたんにreturn (DataTheta f)とすればよい。
    Nothing -> throwError $ "clarify.theta: " ++ name

clarifyUnaryOp ::
     Context -> Identifier -> UnaryOp -> LowType -> Meta -> WithEnv CodePlus
clarifyUnaryOp ctx name op lowType m = do
  t <- lookupContext name ctx
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx)] _) -> do
      let varX = toDataUpsilon (x, emptyMeta)
      zts <- complementaryChainOf ctx xts
      makeClosure'
        ctx
        (Just name)
        zts
        m
        [(x, tx)]
        (m, CodeTheta (ThetaUnaryOp op lowType varX))
    _ -> throwError $ "the arity of " ++ name ++ " is wrong"

clarifyBinaryOp ::
     Context -> Identifier -> BinaryOp -> LowType -> Meta -> WithEnv CodePlus
clarifyBinaryOp ctx name op lowType m = do
  t <- lookupContext name ctx
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx), (y, ty)] _) -> do
      let varX = toDataUpsilon (x, emptyMeta)
      let varY = toDataUpsilon (y, emptyMeta)
      zts <- complementaryChainOf ctx xts
      makeClosure'
        ctx
        (Just name)
        zts
        m
        [(x, tx), (y, ty)]
        (m, CodeTheta (ThetaBinaryOp op lowType varX varY))
    _ -> throwError $ "the arity of " ++ name ++ " is wrong"

clarifyIsEnum :: Context -> Meta -> WithEnv CodePlus
clarifyIsEnum ctx m = do
  t <- lookupContext "is-enum" ctx
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx)] _) -> do
      v <- cartesianImmediate m
      let varX = toDataUpsilon (x, emptyMeta)
      aff <- newNameWith "aff"
      rel <- newNameWith "rel"
      retImmType <- returnCartesianImmediate
      zts <- complementaryChainOf ctx xts
      makeClosure'
        ctx
        (Just "is-enum")
        zts
        m
        [(x, tx)]
        ( m
        , CodeSigmaElim
            [(aff, retImmType), (rel, retImmType)]
            varX
            (m, CodeUpIntro v))
    _ -> throwError $ "the type of is-enum is wrong. t :\n" ++ Pr.ppShow t

--    unsafe.eval-io
-- ~> lam x.
--      bind sig := call-closure(x, [0]) in
--      let (resultEnv, value) := sig in
--      return value
--    (as closure)
clarifyEvalIO :: Context -> Meta -> WithEnv CodePlus
clarifyEvalIO ctx m = do
  t <- lookupContext "unsafe.eval-io" ctx
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[arg] _) -> do
      (resultValue, resultValueVar) <- newDataUpsilonWith "result"
      (sig, sigVar) <- newDataUpsilonWith "eval-io-sig"
      resultEnv <- newNameWith "env"
      arg' <- clarify' ctx $ toTermUpsilon $ fst arg
      -- IO Top == Top -> (Bottom, Top)
      evalArgWithZero <- callClosure' ctx m arg' [toTermInt64 0]
      retImmType <- returnCartesianImmediate
      zts <- complementaryChainOf ctx xts
      makeClosure'
        ctx
        (Just "unsafe.eval-io")
        zts
        m
        [arg]
        ( m
        , CodeUpElim
            sig
            evalArgWithZero
            ( m
            , CodeSigmaElim
                -- Since `resultEnv` is evaluated into 0,
                -- we can set resultEnv : retImmType (despite the fact that its actual type is bottom).
                [(resultEnv, retImmType), (resultValue, retImmType)] -- (Bottom, Top)
                sigVar
                (m, CodeUpIntro resultValueVar)))
    _ -> throwError "the type of unsafe.eval-io is wrong"

-- インデックス部分についての説明。たとえばsystem callとしてのwriteは、対象言語では
--   unsafe.write : Pi (A : Univ, out : file-descriptor, str : u8-array a, len : is-enum A). top
-- などと宣言されることになる。他方で実際のsystem callの引数は
--   write(FILE_DESCRIPTOR, STRING_BUFFER, LENGTH)
-- という感じなので、unsafe.writeの引数Aの部分が不要である。この不要な部分と必要な部分を指定するためにclarifySyscallは
-- 引数としてインデックスの情報をとっている。unsafe.writeの例で言えば、長さについての情報は4であり、"used arguments" を
-- 指定する配列は、zero-indexであることに注意して [1, 2, 3] となる。
clarifySysCall ::
     Context
  -> Identifier -- the name of theta
  -> SysCall -- the kind of system call
  -> Int -- the length of the arguments of the theta
  -> [Int] -- used (or, non-discarded) arguments in its actual implementation (index starts from zero)
  -> Meta -- the meta of the theta
  -> WithEnv CodePlus
clarifySysCall ctx name sysCall argLen argIdxList m = do
  t <- lookupContext name ctx
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts _)
      | length xts == argLen -> do
        let ys = map (\i -> toVar $ fst $ xts !! i) argIdxList
        zts <- complementaryChainOf ctx xts
        makeClosure'
          ctx
          (Just name)
          zts
          m
          xts
          (m, CodeTheta (ThetaSysCall sysCall ys))
    _ -> throwError $ "the type of " ++ name ++ " is wrong"

complementaryChainOf ::
     Context -> [(Identifier, TermPlus)] -> WithEnv [(Identifier, TermPlus)]
complementaryChainOf ctx xts = do
  zts <- getClosedChainBindings ctx xts []
  return $ nubBy (\(x, _) (y, _) -> x == y) zts

toVar :: Identifier -> DataPlus
toVar x = (emptyMeta, DataUpsilon x)

-- {enum.top, enum.choice, etc.} ~> {(the number of contents in enum)}
-- enum.n{i}とかも処理できないとだめ。
asEnumConstant :: Identifier -> WithEnv (Maybe Integer)
asEnumConstant x
  | ["enum", y] <- wordsBy '.' x = do
    eenv <- gets enumEnv
    case lookup y eenv of
      Nothing -> return Nothing
      Just ls -> return $ Just $ toInteger $ length ls
asEnumConstant _ = return Nothing

clarifyBinder ::
     Context -> [(Identifier, TermPlus)] -> WithEnv [(Identifier, CodePlus)]
clarifyBinder _ [] = return []
clarifyBinder ctx ((x, t):xts) = do
  t' <- clarify' ctx t
  bar <- clarifyBinder ((x, t) : ctx) xts
  return $ (x, t') : bar

makeClosure' ::
     Context
  -> Maybe Identifier -- the name of newly created closure
  -> [(Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
makeClosure' ctx mName fvs m xts e = do
  fvs' <- clarifyBinder ctx fvs
  xts' <- clarifyBinder ctx xts
  makeClosure mName fvs' m xts' e

callClosure' :: Context -> Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure' ctx m e es = do
  tmp <- mapM (clarifyPlus ctx) es
  callClosure m e tmp
