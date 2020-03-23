module Parse.Utility where

import Control.Monad

import qualified Data.Text as T

import Data.Basic
import Data.WeakTerm

type CompInfo = [(Identifier, Meta)]

type CursorName = Identifier

compInfo :: CursorName -> [QuasiStmt] -> Either CompInfo ()
compInfo c ss = compInfoQuasiStmtList c [] ss

compInfoQuasiStmtList ::
     CursorName -> CompInfo -> [QuasiStmt] -> Either CompInfo ()
compInfoQuasiStmtList _ _ [] = return ()
compInfoQuasiStmtList c info ((QuasiStmtLet _ (mx, x, t) e):ss) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoWeakTermPlus c info' e
  compInfoQuasiStmtList c info' ss
compInfoQuasiStmtList c info ((QuasiStmtDef xds):ss) = do
  xms <- mapM (compInfoDef c info . snd) xds
  let info' = xms ++ info
  compInfoQuasiStmtList c info' ss
compInfoQuasiStmtList c info ((QuasiStmtConstDecl _ (mx, x, t)):ss) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoQuasiStmtList c info' ss
compInfoQuasiStmtList c info (_:ss) = compInfoQuasiStmtList c info ss

compInfoDef ::
     CursorName -> CompInfo -> Def -> Either CompInfo (Identifier, Meta)
compInfoDef c info (_, (mx, x, t), xts, e) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoBinder c info' xts e
  return (x, mx)

compInfoWeakTermPlus ::
     CursorName -> CompInfo -> WeakTermPlus -> Either CompInfo ()
compInfoWeakTermPlus _ _ (_, WeakTermTau _) = return ()
compInfoWeakTermPlus c info (_, WeakTermUpsilon x)
  | asText c == asText x = Left info
  | otherwise = return ()
compInfoWeakTermPlus c info (_, WeakTermPi _ xts t) =
  compInfoBinder c info xts t
compInfoWeakTermPlus c info (_, WeakTermPiPlus _ _ xts t) =
  compInfoBinder c info xts t
compInfoWeakTermPlus c info (_, WeakTermPiIntro xts e) =
  compInfoBinder c info xts e
compInfoWeakTermPlus c info (_, WeakTermPiIntroNoReduce xts e) =
  compInfoBinder c info xts e
compInfoWeakTermPlus c info (_, WeakTermPiIntroPlus _ _ xts e) =
  compInfoBinder c info xts e
compInfoWeakTermPlus c info (_, WeakTermPiElim e es) = do
  mapM_ (compInfoWeakTermPlus c info) es
  compInfoWeakTermPlus c info e
compInfoWeakTermPlus c info (_, WeakTermSigma xts) = compInfoSigma c info xts
compInfoWeakTermPlus c info (_, WeakTermSigmaIntro _ es) =
  mapM_ (compInfoWeakTermPlus c info) es
compInfoWeakTermPlus c info (_, WeakTermSigmaElim _ xts e1 e2) = do
  compInfoWeakTermPlus c info e1
  compInfoBinder c info xts e2
compInfoWeakTermPlus c info (_, WeakTermIter (mx, x, t) xts e) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoBinder c info' xts e
compInfoWeakTermPlus _ _ (_, WeakTermZeta _) = return ()
compInfoWeakTermPlus _ _ (_, WeakTermConst _) = return ()
compInfoWeakTermPlus c info (_, WeakTermInt t _) = compInfoWeakTermPlus c info t
compInfoWeakTermPlus _ _ (_, WeakTermFloat16 _) = return ()
compInfoWeakTermPlus _ _ (_, WeakTermFloat32 _) = return ()
compInfoWeakTermPlus _ _ (_, WeakTermFloat64 _) = return ()
compInfoWeakTermPlus c info (_, WeakTermFloat t _) =
  compInfoWeakTermPlus c info t
compInfoWeakTermPlus _ _ (_, WeakTermEnum _) = return ()
compInfoWeakTermPlus _ _ (_, WeakTermEnumIntro _) = return ()
compInfoWeakTermPlus c info (_, WeakTermEnumElim (e, _) les) = do
  compInfoWeakTermPlus c info e
  let (_, es) = unzip les
  mapM_ (compInfoWeakTermPlus c info) es
compInfoWeakTermPlus c info (_, WeakTermArray dom _) =
  compInfoWeakTermPlus c info dom
compInfoWeakTermPlus c info (_, WeakTermArrayIntro _ es) =
  mapM_ (compInfoWeakTermPlus c info) es
compInfoWeakTermPlus c info (_, WeakTermArrayElim _ xts e1 e2) = do
  compInfoWeakTermPlus c info e1
  compInfoBinder c info xts e2
compInfoWeakTermPlus _ _ (_, WeakTermStruct _) = return ()
compInfoWeakTermPlus c info (_, WeakTermStructIntro eks) = do
  let es = map fst eks
  mapM_ (compInfoWeakTermPlus c info) es
compInfoWeakTermPlus c info (_, WeakTermStructElim mxks e1 e2) = do
  compInfoWeakTermPlus c info e1
  compInfoArrayElim c info mxks e2
compInfoWeakTermPlus c info (_, WeakTermCase (e, _) cxtes) = do
  compInfoWeakTermPlus c info e
  forM_ cxtes $ \((_, xts), body) -> compInfoBinder c info xts body

compInfoBinder ::
     CursorName
  -> CompInfo
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> Either CompInfo ()
compInfoBinder s info [] e = compInfoWeakTermPlus s info e
compInfoBinder s info ((mx, x, t):xts) e = do
  compInfoWeakTermPlus s info t
  let info' = (x, mx) : info
  compInfoBinder s info' xts e

compInfoArrayElim ::
     CursorName
  -> CompInfo
  -> [(Meta, Identifier, ArrayKind)]
  -> WeakTermPlus
  -> Either CompInfo ()
compInfoArrayElim s info [] e = compInfoWeakTermPlus s info e
compInfoArrayElim s info ((mx, x, _):xts) e = do
  let info' = (x, mx) : info
  compInfoArrayElim s info' xts e

compInfoSigma ::
     CursorName -> CompInfo -> [IdentifierPlus] -> Either CompInfo ()
compInfoSigma _ _ [] = return ()
compInfoSigma s info ((mx, x, t):xts) = do
  compInfoWeakTermPlus s info t
  let info' = (x, mx) : info
  compInfoSigma s info' xts

filterCompInfo :: Prefix -> (Identifier, Meta) -> Bool
filterCompInfo prefix (I (x, _), m)
  | True <- metaIsAppropriateAsCompletionCandidate m = prefix `T.isPrefixOf` x
  | otherwise = False

type Prefix = T.Text

headTailMaybe :: [a] -> Maybe (a, [a])
headTailMaybe [] = Nothing
headTailMaybe (x:xs) = return (x, xs)

headTailMaybeText :: T.Text -> Maybe (Char, T.Text)
headTailMaybeText s
  | s == T.empty = Nothing
  | otherwise = return (T.head s, T.tail s)

splitAtMaybe :: Int -> T.Text -> Maybe (T.Text, T.Text)
splitAtMaybe i xs = do
  if 0 <= i && i < T.length xs
    then return $ T.splitAt i xs
    else Nothing
