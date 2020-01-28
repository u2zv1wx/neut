module Parse.Utility
  ( compInfo
  , CursorName
  , CompInfo
  ) where

import qualified Data.Text as T

import Data.Basic
import Data.WeakTerm

type CompInfo = [(Identifier, Meta)]

type CursorName = T.Text

compInfo :: CursorName -> [Stmt] -> Either CompInfo ()
compInfo c ss = compInfoStmtList c [] ss

compInfoStmtList :: CursorName -> CompInfo -> [Stmt] -> Either CompInfo ()
compInfoStmtList _ _ [] = return ()
compInfoStmtList c info ((StmtLet _ (mx, x, t) e):ss) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoWeakTermPlus c info' e
  compInfoStmtList c info' ss
compInfoStmtList c info ((StmtDef xds):ss) = do
  xms <- mapM (compInfoDef c info . snd) xds
  let info' = xms ++ info
  compInfoStmtList c info' ss
compInfoStmtList c info ((StmtConstDecl _ (mx, x, t)):ss) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoStmtList c info' ss

compInfoDef ::
     CursorName -> CompInfo -> Def -> Either CompInfo (Identifier, Meta)
compInfoDef c info (_, (mx, x, t), xts, e) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoBinder c info' xts e
  return (x, mx)

compInfoWeakTermPlus ::
     CursorName -> CompInfo -> WeakTermPlus -> Either CompInfo ()
compInfoWeakTermPlus _ _ (_, WeakTermTau) = return ()
compInfoWeakTermPlus c info (_, WeakTermUpsilon x)
  | c == x = Left info
  | otherwise = return ()
compInfoWeakTermPlus c info (_, WeakTermPi xts t) = compInfoBinder c info xts t
compInfoWeakTermPlus c info (_, WeakTermPiIntro xts e) =
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
compInfoWeakTermPlus c info (_, WeakTermConstDecl (mx, x, t) e) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoWeakTermPlus c info' e
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
