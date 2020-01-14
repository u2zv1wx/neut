{-# LANGUAGE OverloadedStrings #-}

--
-- clarification == polarization + closure conversion + linearization (+ rename, for LLVM IR)
--
module Clarify
  ( clarify
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nubBy)

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

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
clarify (m, TermUpsilon x) = return (m, CodeUpIntro (m, DataUpsilon x))
clarify (m, TermPi {}) = do
  returnClosureType m
clarify lam@(m, TermPiIntro xts e) = do
  forM_ xts $ uncurry insTypeEnv
  e' <- clarify e
  fvs <- chainTermPlus lam
  retClosure Nothing fvs m xts e'
clarify (m, TermPiElim e es) = do
  e' <- clarify e
  callClosure' m e' es
clarify iter@(m, TermIter (x, t) xts e) = do
  forM_ ((x, t) : xts) $ uncurry insTypeEnv
  e' <- clarify e
  fvs <- chainTermPlus iter
  retClosure' x fvs m xts e'
clarify (m, TermConst x) = clarifyConst m x
clarify (_, TermConstDecl (x, t) e) = do
  _ <- clarify t
  insTypeEnv x t
  clarify e
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
clarify (m, TermArray {}) = do
  returnArrayType m
clarify (m, TermArrayIntro k les) = do
  v <- cartesianImmediate m
  let retKindType = (m, CodeUpIntro v)
  -- arrayType = Sigma [_ : IMMEDIATE, ..., _ : IMMEDIATE]
  name <- newNameWith "array"
  arrayType <-
    cartesianSigma name m $ map Left $ replicate (length les) retKindType
  let (ls, es) = unzip les
  (zs, es', xs) <- unzip3 <$> mapM (clarifyPlus) es
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

clarifyConst :: Meta -> Identifier -> WithEnv CodePlus
clarifyConst m name
  | Just (lowType, op) <- asUnaryOpMaybe name = clarifyUnaryOp name op lowType m
clarifyConst m name
  | Just (lowType, op) <- asBinaryOpMaybe name =
    clarifyBinaryOp name op lowType m
clarifyConst m name
  | Just (sysCall, len, idxList) <- asSysCallMaybe name =
    clarifySysCall name sysCall len idxList m
clarifyConst m name
  | Just _ <- asLowTypeMaybe name = clarify (m, TermEnum $ EnumTypeLabel "top")
clarifyConst m "is-enum" = clarifyIsEnum m
clarifyConst m "file-descriptor" = clarify (m, TermConst "i64")
clarifyConst m "stdin" = clarify (m, TermIntS 64 0)
clarifyConst m "stdout" = clarify (m, TermIntS 64 1)
clarifyConst m "stderr" = clarify (m, TermIntS 64 2)
clarifyConst m name = do
  mx <- asEnumConstant name
  case mx of
    Just i -> clarify (m, TermIntS 64 i) -- enum.top ~> 1, enum.choice ~> 2, etc.
    Nothing -> do
      cenv <- gets constantEnv
      if name `elem` cenv
        then return (m, CodeUpIntro (m, DataTheta name))
        else throwError $ "clarify.theta: " <> name

clarifyUnaryOp :: Identifier -> UnaryOp -> LowType -> Meta -> WithEnv CodePlus
clarifyUnaryOp name op lowType m = do
  t <- lookupTypeEnv name
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx)] _) -> do
      let varX = toDataUpsilon (x, emptyMeta)
      zts <- complementaryChainOf xts
      -- p "one-time closure (unary)"
      retClosure
        (Just name)
        zts
        m
        [(x, tx)]
        (m, CodeTheta (ThetaUnaryOp op lowType varX))
    _ -> throwError $ "the arity of " <> name <> " is wrong"

clarifyBinaryOp :: Identifier -> BinaryOp -> LowType -> Meta -> WithEnv CodePlus
clarifyBinaryOp name op lowType m = do
  t <- lookupTypeEnv name
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx), (y, ty)] _) -> do
      let varX = toDataUpsilon (x, emptyMeta)
      let varY = toDataUpsilon (y, emptyMeta)
      zts <- complementaryChainOf xts
      -- p "one-time closure (binary)"
      retClosure
        (Just name)
        zts
        m
        [(x, tx), (y, ty)]
        (m, CodeTheta (ThetaBinaryOp op lowType varX varY))
    _ -> throwError $ "the arity of " <> name <> " is wrong"

clarifyIsEnum :: Meta -> WithEnv CodePlus
clarifyIsEnum m = do
  t <- lookupTypeEnv "is-enum"
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts@[(x, tx)] _) -> do
      v <- cartesianImmediate m
      let varX = toDataUpsilon (x, emptyMeta)
      aff <- newNameWith "aff"
      rel <- newNameWith "rel"
      retImmType <- returnCartesianImmediate
      zts <- complementaryChainOf xts
      -- p "one-time closure (is-enum)"
      retClosure
        (Just "is-enum")
        zts
        m
        [(x, tx)]
        ( m
        , CodeSigmaElim
            [(aff, retImmType), (rel, retImmType)]
            varX
            (m, CodeUpIntro v))
    _ ->
      throwError $ "the type of is-enum is wrong. t :\n" <> T.pack (Pr.ppShow t)

-- インデックス部分についての説明。たとえばsystem callとしてのwriteは、対象言語では
--   write : Pi (A : Univ, out : file-descriptor, str : u8-array a, len : is-enum A). top
-- などと宣言されることになる。他方で実際のsystem callの引数は
--   write(FILE_DESCRIPTOR, STRING_BUFFER, LENGTH)
-- という感じなので、writeの引数Aの部分が不要である。この不要な部分と必要な部分を指定するためにclarifySyscallは
-- 引数としてインデックスの情報をとっている。writeの例で言えば、長さについての情報は4であり、"used arguments" を
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
    (_, TermPi xts cod)
      | length xts == argLen -> do
        let ys = map (\i -> toVar $ fst $ xts !! i) argIdxList
        zts <- complementaryChainOf xts
        case sysCall of
          SysCallWrite -> do
            (contentTypeVarName, contentTypeVar) <-
              newDataUpsilonWith "array-type"
            (contentVarName, contentVar) <- newDataUpsilonWith "array-content"
            retUnivType <- returnCartesianUniv
            let retContentType = (m, CodeUpIntro contentTypeVar)
            let ys' = [ys !! 0, contentVar, ys !! 2]
            let body =
                  ( m
                  -- decompose the array closure
                  , CodeSigmaElim
                      [ (contentTypeVarName, retUnivType)
                      , (contentVarName, retContentType)
                      ]
                      (ys !! 1)
                      (m, CodeTheta (ThetaSysCall sysCall ys')))
            retClosure (Just name) zts m xts body
          -- read [A, in, len]
          -- ys == [in, len]
          SysCallRead
            | (_, TermPi [c, (funName, funType@(_, TermPi [(_, bufType), (_, sizeType)] _))] _) <-
               cod -> do
              bufName <- newNameWith "buf"
              (buf1Name, buf1) <- newDataUpsilonWith bufName
              buf2Name <- newNameWith bufName
              retImmType <- returnCartesianImmediate
              -- copy as if buf is an immediate (to realize variable assignment)
              relApp <- toRelevantApp m bufName retImmType
              sizeName <- newNameWith "size"
              -- (pair buf2 size) == lam (C : univ). lam (f : (Buf, i64) -> C). f @ (buf2, size)
              let pair =
                    ( m
                    , TermPiIntro
                        [c, (funName, funType)]
                        ( m
                        , TermPiElim
                            (m, TermUpsilon funName)
                            [ (m, TermUpsilon buf2Name)
                            , (m, TermUpsilon sizeName)
                            ]))
              -- buf2NameとかをinsTypeEnvする必要がある。
              insTypeEnv buf2Name bufType
              insTypeEnv sizeName sizeType
              pair' <- clarify pair
              -- buf2がコピーされる可能性はあるから、そこの型はちゃんととっておく必要がある。
              retArrayType <- returnArrayType m
              (sigName, sig) <- newDataUpsilonWith "sig"
              let body =
                    ( m
                    , CodeUpElim
                        bufName
                        (m, CodeUpIntro (m, DataMemory $ ys !! 1)) -- len
                        ( m
                        , CodeUpElim
                            sigName
                            -- bufをimmであるかのようにしてcopy
                            relApp
                            ( m
                            , CodeSigmaElim
                                [ (buf1Name, retArrayType)
                                , (buf2Name, retArrayType)
                                ]
                                sig
                                ( m
                                , CodeUpElim
                                    sizeName
                                    ( m
                                    , CodeTheta
                                        (ThetaSysCall
                                           sysCall
                                           [ys !! 0, buf1, ys !! 1] -- buf1はここでしか使用されない
                                         ))
                                    pair'))))
              retClosure (Just name) zts m xts body
          _ -> throwError $ "the type of " <> name <> " is wrong"
    _ -> throwError $ "the type of " <> name <> " is wrong"

complementaryChainOf ::
     [(Identifier, TermPlus)] -> WithEnv [(Identifier, TermPlus)]
complementaryChainOf xts = do
  zts <- chainTermPlus'' xts []
  return $ nubBy (\(x, _) (y, _) -> x == y) zts

toVar :: Identifier -> DataPlus
toVar x = (emptyMeta, DataUpsilon x)

-- {enum.top, enum.choice, etc.} ~> {(the number of contents in enum)}
-- enum.n{i}とかも処理できないとだめ。
asEnumConstant :: Identifier -> WithEnv (Maybe Integer)
asEnumConstant x
  | ["enum", y] <- wordsBy '.' x = do
    eenv <- gets enumEnv
    case Map.lookup y eenv of
      Nothing -> return Nothing
      Just ls -> return $ Just $ toInteger $ length ls
  | Just i <- asEnumNatNumConstant x = return $ Just i
asEnumConstant _ = return Nothing

clarifyBinder :: [(Identifier, TermPlus)] -> WithEnv [(Identifier, CodePlus)]
clarifyBinder [] = return []
clarifyBinder ((x, t):xts) = do
  t' <- clarify t
  xts' <- clarifyBinder xts
  return $ (x, t') : xts'

retClosure ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
retClosure mName fvs m xts e = do
  cls <- makeClosure' mName fvs m xts e
  return (m, CodeUpIntro cls)

retClosure' ::
     Identifier -- the name of newly created closure
  -> [(Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
retClosure' x fvs m xts e = do
  modify (\env -> env {nameEnv = Map.insert x x (nameEnv env)})
  cls <- makeClosure' (Just x) fvs m xts e
  knot x cls
  return (m, CodeUpIntro cls)

makeClosure' ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv DataPlus
makeClosure' mName fvs m xts e = do
  fvs' <- clarifyBinder fvs
  xts' <- clarifyBinder xts
  makeClosure mName fvs' m xts' e

callClosure' :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure' m e es = do
  tmp <- mapM (clarifyPlus) es
  callClosure m e tmp

knot :: Identifier -> DataPlus -> WithEnv ()
knot z cls = do
  cenv <- gets codeEnv
  case pop z cenv of
    Nothing -> throwError "knot"
    Just ((args, body), cenv') -> do
      let body' = substCodePlus [(z, cls)] body
      let cenv'' = Map.insert z (args, body') cenv'
      modify (\env -> env {codeEnv = cenv''})

-- lookup and remove the matching element from the given assoc list
pop ::
     Identifier
  -> Map.HashMap Identifier b
  -> Maybe (b, Map.HashMap Identifier b)
pop x mp = do
  v <- Map.lookup x mp
  return (v, Map.delete x mp)

asSysCallMaybe :: Identifier -> Maybe (SysCall, ArgLen, UsedArgIndexList)
asSysCallMaybe "write" = Just (SysCallWrite, 4, [1, 2, 3])
asSysCallMaybe "read" = Just (SysCallRead, 3, [1, 2])
asSysCallMaybe _ = Nothing
