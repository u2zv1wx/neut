module Reduce.Code
  ( reduceCodePlus
  , inlineCodePlus
  ) where

import           Control.Monad.State
import           Data.List           (transpose)

import           Data.Basic
import           Data.Code
import           Data.Env
import           Polarize            (bindLet)

reduceCodePlus :: CodePlus -> WithEnv CodePlus
reduceCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaArith ArithAdd t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 + i2) t))
    ThetaArith ArithSub t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 - i2) t))
    ThetaArith ArithMul t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 * i2) t))
    ThetaArith ArithDiv t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 `div` i2) t))
    ThetaPrint (_, DataEpsilonIntro (LiteralInteger i) _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
reduceCodePlus (m, CodeEpsilonElim x v branchList) =
  case v of
    (_, DataEpsilonIntro l _) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
            Nothing   -> return (m, CodeEpsilonElim x v branchList)
    _ -> return (m, CodeEpsilonElim x v branchList)
reduceCodePlus (m, CodePiElimDownElim v es) = do
  es' <- mapM reduceCodePlus es
  case extractUpIntro es' of
    Nothing -> return (m, CodePiElimDownElim v es')
    Just vs -> do
      cenv <- gets codeEnv
      case (v, exponentArgs es') of
        ((_, DataTau), Just (i, w)) -> return $ exponentImmediate i w
        ((_, DataEpsilon _), Just (i, w)) -> return $ exponentImmediate i w
        ((_, DataDownPi _), Just (i, w)) -> return $ exponentImmediate i w
        ((_, DataSigma xps), Just (i, w)) ->
          exponentSigma i xps w >>= reduceCodePlus
        ((_, DataDownIntroPiIntro xs body), _) ->
          reduceCodePlus $ substCodePlus (zip xs vs) body
        ((_, DataTheta x), _)
          | Just (xs, body) <- lookup x cenv ->
            reduceCodePlus $ substCodePlus (zip xs vs) body
        _ -> return (m, CodePiElimDownElim v es')
reduceCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> reduceCodePlus $ substCodePlus (zip xs es) e
    _ -> return (m, CodeSigmaElim xs v e)
reduceCodePlus t = return t

extractUpIntro :: [CodePlus] -> Maybe [DataPlus]
extractUpIntro [] = Just []
extractUpIntro ((_, CodeUpIntro v):es) = do
  vs <- extractUpIntro es
  return $ v : vs
extractUpIntro _ = Nothing

exponentArgs :: [CodePlus] -> Maybe (Int, DataPlus)
exponentArgs [(_, CodeUpIntro (_, DataEpsilonIntro (LiteralInteger i) _)), (_, CodeUpIntro v)] =
  Just (i, v)
exponentArgs _ = Nothing

exponentImmediate :: Int -> DataPlus -> CodePlus
exponentImmediate i v = do
  let ml = fst v
  (ml, CodeUpIntro (ml, DataSigmaIntro $ replicate i v))

-- Sigma (y1 : t1, ..., yn : tn) ~>
--   lam (m, z).
--     let (y1, ..., yn) := z in
--     bind ys1 = t1 @ (m, y1) in
--     ...
--     bind ysn = tn @ (m, yn) in
--     let (ys1-1, ..., ys1-m) := ys1 in
--     ...
--     let (ysn-1, ..., ysn-m) := ysn in
--     ((ys1-1, ..., ysn-1), ..., (ys1-m, ..., ysn-m))
exponentSigma :: Int -> [(Identifier, DataPlus)] -> DataPlus -> WithEnv CodePlus
exponentSigma n xps v = do
  let (xs, ps) = unzip xps
  let vs = map (\x -> (Nothing, CodeUpIntro (toDataUpsilon' x))) xs
  let vps = zip vs ps
  let lenAsEpsilon = (Nothing, DataEpsilonIntro (LiteralInteger n) undefined)
  let bar = (Nothing, CodeUpIntro lenAsEpsilon)
  let appList = map (\(w, p) -> (Nothing, CodePiElimDownElim p [bar, w])) vps
  ys <- mapM (const $ newNameWith "var") xps
  let ys' = map toDataUpsilon' ys
  let yss = map (replicate n) ys
  zss <- mapM (mapM (const $ newNameWith "var")) yss
  return
    ( Nothing
    , CodeSigmaElim -- let (x-1, ..., x-m) := v
        xs
        v
        (bindLet (zip ys appList) $ -- let xs-k := TYPE @ (n, x-k) (k = 1, ..., m)
         toSigmaElimSeq
           (zip zss ys') -- let (xs-k-1, ..., xs-k-n) := xs-k in (k = 1, ..., m)
           ( Nothing
           , CodeUpIntro
               ( Nothing
               , DataSigmaIntro
                   (map (toSigmaIntro . map toDataUpsilon') $ transpose zss)))))

toSigmaIntro :: [DataPlus] -> DataPlus
toSigmaIntro ds = (Nothing, DataSigmaIntro ds)

toSigmaElimSeq :: [([Identifier], DataPlus)] -> CodePlus -> CodePlus
toSigmaElimSeq [] cont = cont
toSigmaElimSeq ((xs, d):xsds) cont =
  (Nothing, CodeSigmaElim xs d (toSigmaElimSeq xsds cont))

inlineCodePlus :: CodePlus -> WithEnv CodePlus
inlineCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaArith ArithAdd t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 + i2) t))
    ThetaArith ArithSub t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 - i2) t))
    ThetaArith ArithMul t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 * i2) t))
    ThetaArith ArithDiv t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 `div` i2) t))
    ThetaPrint (_, DataEpsilonIntro (LiteralInteger i) _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
inlineCodePlus (m, CodeEpsilonElim x v branchList) =
  case v of
    (_, DataEpsilonIntro l _) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> inlineCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> inlineCodePlus $ substCodePlus [(x, v)] body
            Nothing -> do
              let (cs, es) = unzip branchList
              es' <- mapM inlineCodePlus es
              return (m, CodeEpsilonElim x v (zip cs es'))
    _ -> return (m, CodeEpsilonElim x v branchList)
inlineCodePlus (m, CodePiElimDownElim v es) = do
  es' <- mapM inlineCodePlus es
  case extractUpIntro es' of
    Nothing -> return (m, CodePiElimDownElim v es')
    Just vs ->
      case (v, exponentArgs es') of
        ((_, DataTau), Just (i, w)) -> return $ exponentImmediate i w
        ((_, DataEpsilon _), Just (i, w)) -> return $ exponentImmediate i w
        ((_, DataDownPi _), Just (i, w)) -> return $ exponentImmediate i w
        ((_, DataSigma xps), Just (i, w)) ->
          exponentSigma i xps w >>= inlineCodePlus
        ((_, DataDownIntroPiIntro xs body), _) ->
          inlineCodePlus $ substCodePlus (zip xs vs) body
        _ -> return (m, CodePiElimDownElim v es')
  -- es' <- mapM inlineCodePlus es
  -- case extractUpIntro es' of
  --   Nothing ->
  --     return (m1, CodePiElimDownElim (m2, DataDownIntroPiIntro xs body) es')
  --   Just vs -> inlineCodePlus $ substCodePlus (zip xs vs) body
inlineCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> inlineCodePlus $ substCodePlus (zip xs es) e
    _ -> do
      e' <- inlineCodePlus e
      return (m, CodeSigmaElim xs v e')
inlineCodePlus t = return t
