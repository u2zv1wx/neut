-- This module "clarifies" a neutral term into a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value. A detailed explanation of Call-By-Push-Value can be found
-- in P. Levy, "Call-by-Push-Value: A Subsuming Paradigm". Ph. D. thesis,
-- Queen Mary College, 2001.
module Clarify
  ( clarify
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Prelude hiding (pi)

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
clarify (m, TermTau) = do
  v <- cartesianUniv m
  return (m, CodeUpIntro v)
clarify (m, TermTheta x) = clarifyTheta m x
clarify (m, TermUpsilon x) = do
  return (m, CodeUpIntro (m, DataUpsilon x))
clarify (m, TermPi _ _) = do
  returnClosureType m
clarify lam@(m, TermPiIntro xts e) = do
  fvs <- varTermPlus lam
  let (freeVarNameList, freeVarTypeList) = unzip fvs
  negTypeList <- mapM clarify freeVarTypeList
  let fvs' = zip freeVarNameList negTypeList
  e' <- clarify e
  makeClosure' Nothing fvs' m xts e'
clarify (m, TermPiElim e es) = do
  e' <- clarify e
  callClosure' m e' es
clarify (m, TermMu (f, _) e) = do
  tmp <- obtainFreeVarList [f] e -- fの型は使用しないので無視でオーケー
  let (nameList, typeList) = unzip tmp
  let fvs = zip nameList typeList
  let fvs' = map (toTermUpsilon . fst) fvs
  let lamBody = substTermPlus [(f, (m, TermPiElim (m, TermTheta f) fvs'))] e
  lamBody' <- clarify lamBody
  cls <- makeClosure' (Just f) [] m fvs lamBody'
  callClosure' m cls fvs'
clarify (m, TermIntS size l) = do
  return (m, CodeUpIntro (m, DataIntS size l))
clarify (m, TermIntU size l) = do
  return (m, CodeUpIntro (m, DataIntU size l))
clarify (m, TermFloat16 l) = do
  return (m, CodeUpIntro (m, DataFloat16 l))
clarify (m, TermFloat32 l) = do
  return (m, CodeUpIntro (m, DataFloat32 l))
clarify (m, TermFloat64 l) = do
  return (m, CodeUpIntro (m, DataFloat64 l))
clarify (m, TermEnum _) = do
  v <- cartesianImmediate m
  return (m, CodeUpIntro v)
clarify (m, TermEnumIntro l) = do
  return (m, CodeUpIntro (m, DataEnumIntro l))
clarify (m, TermEnumElim e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM clarify es
  (yName, e', y) <- clarifyPlus e
  return $ bindLet [(yName, e')] (m, CodeEnumElim y (zip cs es'))
clarify (m, TermArray _ _) = do
  returnArrayType m
clarify (m, TermArrayIntro k les) = do
  v <- cartesianImmediate m
  let retKindType = (m, CodeUpIntro v)
  -- arrayType = Sigma [_ : IMMEDIATE, ..., _ : IMMEDIATE]
  name <- newNameWith "array"
  arrayType <-
    cartesianSigma name m $ map Left $ replicate (length les) retKindType
  let (ls, es) = unzip les
  (zs, es', xs) <- unzip3 <$> mapM clarifyPlus es
  return $
    bindLet (zip zs es') $
    ( m
    , CodeUpIntro $
      (m, DataSigmaIntro [arrayType, (m, DataArrayIntro k (zip ls xs))]))
clarify (m, TermArrayElim k e1 e2) = do
  e1' <- clarify e1
  e2' <- clarify e2
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

clarifyPlus :: TermPlus -> WithEnv (Identifier, CodePlus, DataPlus)
clarifyPlus e@(m, _) = do
  e' <- clarify e
  (varName, var) <- newDataUpsilonWith' "var" m
  return (varName, e', var)

clarifyTheta :: Meta -> Identifier -> WithEnv CodePlus
clarifyTheta m name
  | Just (lowType, op) <- asUnaryOpMaybe name = clarifyUnaryOp name op lowType m
clarifyTheta m name
  | Just (lowType, op) <- asBinaryOpMaybe name =
    clarifyBinaryOp name op lowType m
clarifyTheta m name
  | Just (sysCall, len, idxList) <- asSysCallMaybe name =
    clarifySysCall name sysCall len idxList m
clarifyTheta m name
  | Just _ <- asLowTypeMaybe name = clarify (m, TermEnum $ EnumTypeLabel "top")
clarifyTheta m "is-enum" = clarifyIsEnum m
clarifyTheta m "unsafe.eval-io" = clarifyEvalIO m
clarifyTheta m "file-descriptor" = clarify (m, TermTheta "i64")
clarifyTheta m "stdin" = clarify (m, TermIntS 64 0)
clarifyTheta m "stdout" = clarify (m, TermIntS 64 1)
clarifyTheta m "stderr" = clarify (m, TermIntS 64 2)
clarifyTheta m name = do
  mx <- asEnumConstant name
  case mx of
    Just i -> clarify (m, TermIntS 64 i) -- enum.top ~> 1, enum.choice ~> 2, etc.
    -- muで導入されたthetaに由来するものもここにくる。
    -- たぶんたんにreturn (DataTheta f)とすればよい。
    Nothing -> throwError $ "clarify.theta: " ++ name

-- {enum.top, enum.choice, etc.} ~> {(the number of contents in enum)}
asEnumConstant :: Identifier -> WithEnv (Maybe Integer)
asEnumConstant x
  | ["enum", y] <- wordsBy '.' x = do
    eenv <- gets enumEnv
    case lookup y eenv of
      Nothing -> return Nothing
      Just ls -> return $ Just $ toInteger $ length ls
asEnumConstant _ = return Nothing

clarifyUnaryOp :: Identifier -> UnaryOp -> LowType -> Meta -> WithEnv CodePlus
clarifyUnaryOp name op lowType m = do
  t <- lookupTypeEnv name
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi [(x, tx)] _) -> do
      let varX = toDataUpsilon (x, emptyMeta)
      makeClosure'
        (Just name)
        []
        m
        [(x, tx)]
        (m, CodeTheta (ThetaUnaryOp op lowType varX))
    _ -> throwError $ "the arity of " ++ name ++ " is wrong"

clarifyBinaryOp :: Identifier -> BinaryOp -> LowType -> Meta -> WithEnv CodePlus
clarifyBinaryOp name op lowType m = do
  t <- lookupTypeEnv name
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi [(x, tx), (y, ty)] _) -> do
      let varX = toDataUpsilon (x, emptyMeta)
      let varY = toDataUpsilon (y, emptyMeta)
      makeClosure'
        (Just name)
        []
        m
        [(x, tx), (y, ty)]
        (m, CodeTheta (ThetaBinaryOp op lowType varX varY))
    _ -> throwError $ "the arity of " ++ name ++ " is wrong"

clarifyIsEnum :: Meta -> WithEnv CodePlus
clarifyIsEnum m = do
  t <- lookupTypeEnv "is-enum"
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi [(x, tx)] _) -> do
      v <- cartesianImmediate m
      let varX = toDataUpsilon (x, emptyMeta)
      aff <- newNameWith "aff"
      rel <- newNameWith "rel"
      retImmType <- returnCartesianImmediate
      makeClosure'
        (Just "is-enum")
        []
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
clarifyEvalIO :: Meta -> WithEnv CodePlus
clarifyEvalIO m = do
  t <- lookupTypeEnv "unsafe.eval-io"
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi [arg] _) -> do
      (resultValue, resultValueVar) <- newDataUpsilonWith "result"
      (sig, sigVar) <- newDataUpsilonWith "eval-io-sig"
      resultEnv <- newNameWith "env"
      arg' <- clarify $ toTermUpsilon $ fst arg
      -- IO Top == Top -> (Bottom, Top)
      evalArgWithZero <- callClosure' m arg' [toTermInt64 0]
      retImmType <- returnCartesianImmediate
      makeClosure'
        (Just "unsafe.eval-io")
        []
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
     Identifier -- the name of theta
  -> SysCall -- the kind of system call
  -> Int -- the length of the arguments of the theta
  -> [Int] -- used (or, non-discarded) arguments in its actual implementation (index starts from zero)
  -> Meta -- the meta of the theta
  -> WithEnv CodePlus
clarifySysCall name sysCall argLen argIdxList m = do
  t <- lookupTypeEnv name
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts _)
      | length xts == argLen -> do
        let ys = map (\i -> toVar $ fst $ xts !! i) argIdxList
        -- p "syscall"
        -- p "name:"
        -- p' name
        -- p "args (default):"
        -- p' xts
        -- p "choice:"
        -- p' argIdxList
        -- p "chosen args:"
        -- p' ys
        -- pi-introのときと同じように、fvsをとったうえでmakeClosureにあたえる必要がある
        -- （つまりxtsはclosed chainとは限らないので適切なcompletionが必要。でないとtを使用したときに自由変数が絡んでしまうことになる）
        -- clarify lam@(m, TermPiIntro xts e) = do
        -- fvs <- varTermPlus lam
        -- let (freeVarNameList, freeVarTypeList) = unzip fvs
        -- negTypeList <- mapM clarify freeVarTypeList
        -- let fvs' = zip freeVarNameList negTypeList
        -- e' <- clarify e
        -- makeClosure' Nothing fvs' m xts e'
        makeClosure'
          (Just name)
          []
          m
          xts -- ここはおかしいな？いや、引数じたいはふつうにxtsでとっていいのか。……xtsをclosed chainにする必要があるんでは。
          (m, CodeTheta (ThetaSysCall sysCall ys))
    _ -> throwError $ "the type of " ++ name ++ " is wrong"

toVar :: Identifier -> DataPlus
toVar x = (emptyMeta, DataUpsilon x)

makeClosure' ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, CodePlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
makeClosure' mName fvs m xts e = do
  let (xs, ts) = unzip xts
  ts' <- mapM clarify ts
  makeClosure mName fvs m (zip xs ts') e

callClosure' :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure' m e es = do
  tmp <- mapM clarifyPlus es
  callClosure m e tmp

obtainFreeVarList ::
     [Identifier] -> TermPlus -> WithEnv [(Identifier, TermPlus)]
obtainFreeVarList xs e = do
  tmp <- varTermPlus e
  return $ filter (\(x, _) -> x `notElem` xs) $ tmp
