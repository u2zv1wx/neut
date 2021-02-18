module Parse.Interpret
  ( interpret,
    interpretWeakIdentPlus,
    interpretIdentPlus,
    interpretFix,
  )
where

import Codec.Binary.UTF8.String
import Control.Monad.State.Lazy
import Data.EnumCase
import Data.Env
import Data.Hint
import Data.Ident
import Data.LowType
import Data.Maybe (catMaybes)
import Data.Size
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm
import Text.Read (readMaybe)

interpret :: TreePlus -> WithEnv WeakTermPlus
interpret inputTree =
  case inputTree of
    (m, TreeLeaf atom)
      | atom == "tau" ->
        return (m, WeakTermTau)
      | atom == "*" ->
        newAster m
      | Just x' <- readMaybe $ T.unpack atom -> do
        h <- newAster m
        return (m, WeakTermInt h x')
      | Just x' <- readMaybe $ T.unpack atom -> do
        h <- newAster m
        return (m, WeakTermFloat h x')
      | Just str <- readMaybe $ T.unpack atom -> do
        u8s <- forM (encode str) $ \u ->
          return (m, WeakTermInt (i8 m) (toInteger u))
        sigmaIntroString m u8s
      | otherwise ->
        case T.uncons atom of
          Nothing ->
            raiseCritical m "encountered a variable with empty identifier"
          Just (c, rest)
            | c == '?' ->
              if T.length rest == 0
                then raiseError m "found a note-variable with empty identifier"
                else do
                  e <- interpret (m, TreeLeaf rest)
                  h <- newAster m
                  return (m, WeakTermQuestion e h)
            | otherwise ->
              return (m, WeakTermUpsilon $ asIdent atom)
    (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
      case headAtom of
        "Π"
          | [(_, TreeNode xts), t] <- rest -> do
            (xts', t') <- interpretBinder xts t
            return (m, WeakTermPi xts' t')
          | otherwise ->
            raiseSyntaxError m "(Π (TREE*) TREE)"
        "Π-introduction"
          | [(_, TreeNode xts), e] <- rest -> do
            (xts', e') <- interpretBinder xts e
            return (m, WeakTermPiIntro xts' e')
          | otherwise ->
            raiseSyntaxError m "(Π-introduction (TREE*) TREE)"
        "Π-elimination"
          | e : es <- rest ->
            interpretPiElim m e es
          | otherwise ->
            raiseSyntaxError m "(Π-elimination TREE TREE*)"
        "fix"
          | [xt, xts@(_, TreeNode _), e] <- rest -> do
            (m', xt', xts', e') <- interpretFix (m, TreeNode [xt, xts, e])
            return (m', WeakTermFix xt' xts' e')
          | otherwise ->
            raiseSyntaxError m "(fix TREE (TREE*) TREE)"
        "constant"
          | [(_, TreeLeaf x)] <- rest ->
            return (m, WeakTermConst x)
          | otherwise ->
            raiseSyntaxError m "(constant LEAF)"
        "f16"
          | [(mx, TreeLeaf x)] <- rest ->
            case readMaybe $ T.unpack x of
              Nothing ->
                raiseError mx "the argument of `f16` must be a float"
              Just x' ->
                return (m, WeakTermFloat (m, WeakTermConst "f16") x')
          | otherwise ->
            raiseSyntaxError m "(f16 LEAF)"
        "f32"
          | [(mx, TreeLeaf x)] <- rest ->
            case readMaybe $ T.unpack x of
              Nothing ->
                raiseError mx "the argument of `f32` must be a float"
              Just x' ->
                return (m, WeakTermFloat (m, WeakTermConst "f32") x')
          | otherwise ->
            raiseSyntaxError m "(f32 LEAF)"
        "f64"
          | [(mx, TreeLeaf x)] <- rest ->
            case readMaybe $ T.unpack x of
              Nothing ->
                raiseError mx "the argument of `f64` must be a float"
              Just x' ->
                return (m, WeakTermFloat (m, WeakTermConst "f64") x')
          | otherwise ->
            raiseSyntaxError m "(f64 LEAF)"
        "enum"
          | [(_, TreeLeaf x)] <- rest ->
            return (m, WeakTermEnum x)
          | otherwise ->
            raiseSyntaxError m "(enum LEAF)"
        "enum-introduction"
          | [(_, TreeLeaf l)] <- rest ->
            return (m, WeakTermEnumIntro l)
          | otherwise ->
            raiseSyntaxError m "(enum-introduction TREE)"
        "enum-elimination"
          | e : cs <- rest -> do
            e' <- interpret e
            cs' <- mapM interpretClause cs
            h <- newAster m
            return (m, WeakTermEnumElim (e', h) cs')
          | otherwise ->
            raiseSyntaxError m "(enum-elimination TREE TREE*)"
        "array"
          | [dom, kind] <- rest -> do
            dom' <- interpret dom
            kind' <- asArrayKind kind
            return (m, WeakTermArray dom' kind')
          | otherwise ->
            raiseSyntaxError m "(array TREE TREE)"
        "array-introduction"
          | kind : es <- rest -> do
            kind' <- asArrayKind kind
            es' <- mapM interpret es
            return (m, WeakTermArrayIntro kind' es')
          | otherwise ->
            raiseSyntaxError m "(array-introduction TREE TREE*)"
        "array-elimination"
          | [kind, (_, TreeNode xts), e1, e2] <- rest -> do
            kind' <- asArrayKind kind
            e1' <- interpret e1
            (xts', e2') <- interpretBinder xts e2
            return (m, WeakTermArrayElim kind' xts' e1' e2')
          | otherwise ->
            raiseSyntaxError m "(array-elimination TREE (TREE*) TREE TREE)"
        "struct" -> do
          ks' <- mapM asArrayKind rest
          return (m, WeakTermStruct ks')
        "struct-introduction" -> do
          ets' <- mapM interpretStructIntro rest
          return (m, WeakTermStructIntro ets')
        "struct-elimination"
          | [(_, TreeNode xts), e1, e2] <- rest -> do
            e1' <- interpret e1
            xts' <- mapM interpretStructElim xts
            e2' <- interpret e2
            return (m, WeakTermStructElim xts' e1' e2')
          | otherwise ->
            raiseSyntaxError m "(struct-elimination (TREE*) TREE TREE)"
        "question"
          | [e] <- rest -> do
            e' <- interpret e
            h <- newAster m
            return (m, WeakTermQuestion e' h)
          | otherwise ->
            raiseSyntaxError m "(question TREE)"
        "erase"
          | [(_, TreeNode mxs), body] <- rest,
            Just mxs' <- mapM asLeaf mxs -> do
            body' <- interpret body
            return (m, WeakTermErase mxs' body')
          | otherwise ->
            raiseSyntaxError m "(erase (LEAF ... LEAF) TREE)"
        "irreducible"
          | [e] <- rest -> do
            e' <- interpret e
            return ((fst e') {metaIsReducible = False}, snd e')
          | otherwise ->
            raiseSyntaxError m "(irreducible TREE)"
        "with" ->
          interpretWith inputTree
        _
          | [(_, TreeLeaf value)] <- rest,
            Just (intSize, v) <- readValueInt headAtom value ->
            return (m, WeakTermInt (m, WeakTermConst (showIntSize intSize)) v)
          | otherwise ->
            interpretAux m $ leaf : rest
    (m, TreeNode es) ->
      interpretAux m es

interpretAux :: Hint -> [TreePlus] -> WithEnv WeakTermPlus
interpretAux m es =
  case es of
    [] ->
      raiseSyntaxError m "(TREE TREE*)"
    f : args ->
      interpretPiElim m f args

interpretPiElim :: Hint -> TreePlus -> [TreePlus] -> WithEnv WeakTermPlus
interpretPiElim m f es = do
  f' <- interpret f
  (xts, args) <- interpretArg es
  if null xts
    then return (m, WeakTermPiElim f' args)
    else return (m, WeakTermPiIntro xts (m, WeakTermPiElim f' args))

interpretArg :: [TreePlus] -> WithEnv ([WeakIdentPlus], [WeakTermPlus])
interpretArg es =
  case es of
    [] ->
      return ([], [])
    tree : treeList -> do
      (xts, args) <- interpretArg treeList
      case tree of
        (_, TreeLeaf "_") -> do
          xt@(m, h, _) <- interpretIdentPlus tree
          return (xt : xts, (m, WeakTermUpsilon h) : args)
        _ -> do
          e <- interpret tree
          return (xts, e : args)

-- (definition string
--   (Σ
--     ((len u64))
--     (array len u8)))
sigmaIntroString :: Hint -> [WeakTermPlus] -> WithEnv WeakTermPlus
sigmaIntroString m u8s = do
  let z = asIdent "internal.sigma-tau"
  k <- newNameWith'' "sigma"
  let lenVar = asIdent "length"
  arrVar <- newNameWith'' "array"
  return
    ( m,
      WeakTermPiIntro
        [ (m, z, (m, WeakTermTau)),
          ( m,
            k,
            ( m,
              WeakTermPi
                [ (m, lenVar, (m, WeakTermConst (showIntSize 64))),
                  (m, arrVar, (m, WeakTermArray (m, WeakTermUpsilon lenVar) (ArrayKindInt 8)))
                ]
                (m, WeakTermUpsilon z)
            )
          )
        ]
        ( m,
          WeakTermPiElim
            (m, WeakTermUpsilon k)
            [ (m, WeakTermInt (i64 m) (toInteger $ length u8s)),
              (m, WeakTermArrayIntro (ArrayKindInt 8) u8s)
            ]
        )
    )

interpretWeakIdentPlus :: TreePlus -> WithEnv WeakIdentPlus
interpretWeakIdentPlus tree =
  case tree of
    leaf@(_, TreeLeaf _) -> do
      (m, x') <- interpretLeaf leaf
      h <- newAster m
      return (m, x', h)
    (_, TreeNode [x, t]) -> do
      (m, x') <- interpretLeaf x
      t' <- interpret t
      return (m, x', t')
    t ->
      raiseSyntaxError (fst t) "(LEAF TREE)"

interpretFix :: TreePlus -> WithEnv Def
interpretFix tree =
  case tree of
    (m, TreeNode [xt, (_, TreeNode xts), e]) -> do
      xt' <- interpretWeakIdentPlus xt
      (xts', e') <- interpretBinder xts e
      return (m, xt', xts', e')
    t ->
      raiseSyntaxError (fst t) "(TREE (TREE ... TREE) TREE)"

interpretLeaf :: TreePlus -> WithEnv (Hint, Ident)
interpretLeaf tree =
  case tree of
    (m, TreeLeaf "_") -> do
      h <- newNameWith'' "H"
      return (m, h)
    (m, TreeLeaf x) ->
      return (m, asIdent x)
    t ->
      raiseSyntaxError (fst t) "LEAF"

interpretIdentPlus :: TreePlus -> WithEnv WeakIdentPlus
interpretIdentPlus tree =
  case tree of
    leaf@(_, TreeLeaf _) -> do
      (m, x') <- interpretLeafText leaf
      h <- newAster m
      return (m, asIdent x', h)
    (_, TreeNode [x, t]) -> do
      (m, x') <- interpretLeafText x
      t' <- interpret t
      return (m, asIdent x', t')
    t ->
      raiseSyntaxError (fst t) "(LEAF TREE)"

interpretLeafText :: TreePlus -> WithEnv (Hint, T.Text)
interpretLeafText tree =
  case tree of
    (m, TreeLeaf "_") -> do
      h <- newTextWith "_"
      return (m, h)
    (m, TreeLeaf x) ->
      return (m, x)
    t ->
      raiseSyntaxError (fst t) "LEAF"

interpretBinder :: [TreePlus] -> TreePlus -> WithEnv ([WeakIdentPlus], WeakTermPlus)
interpretBinder xts t = do
  xts' <- mapM interpretWeakIdentPlus xts
  t' <- interpret t
  return (xts', t')

interpretClause :: TreePlus -> WithEnv (EnumCasePlus, WeakTermPlus)
interpretClause tree =
  case tree of
    (_, TreeNode [c, e]) -> do
      c' <- interpretEnumCase c
      e' <- interpret e
      return (c', e')
    e ->
      raiseSyntaxError (fst e) "(TREE TREE)"

interpretEnumCase :: TreePlus -> WithEnv EnumCasePlus
interpretEnumCase tree =
  case tree of
    (m, TreeNode [(_, TreeLeaf "enum-introduction"), (_, TreeLeaf l)]) ->
      return (m, EnumCaseLabel l)
    (m, TreeLeaf "default") ->
      return (m, EnumCaseDefault)
    (m, TreeLeaf l) ->
      return (m, EnumCaseLabel l)
    (m, _) ->
      raiseSyntaxError m "default | LEAF"

interpretStructIntro :: TreePlus -> WithEnv (WeakTermPlus, ArrayKind)
interpretStructIntro tree =
  case tree of
    (_, TreeNode [k, e]) -> do
      k' <- asArrayKind k
      e' <- interpret e
      return (e', k')
    e ->
      raiseSyntaxError (fst e) "(TREE TREE)"

interpretStructElim :: TreePlus -> WithEnv (Hint, Ident, ArrayKind)
interpretStructElim tree =
  case tree of
    (_, TreeNode [leaf, k]) -> do
      (m, x) <- interpretLeaf leaf
      k' <- asArrayKind k
      return (m, x, k')
    e ->
      raiseSyntaxError (fst e) "(LEAF TREE)"

readValueInt :: T.Text -> T.Text -> Maybe (IntSize, Integer)
readValueInt t x
  | Just (LowTypeInt i) <- asLowTypeMaybe t,
    Just x' <- readMaybe $ T.unpack x =
    Just (i, x')
  | otherwise =
    Nothing

asArrayKind :: TreePlus -> WithEnv ArrayKind
asArrayKind tree =
  case tree of
    e@(_, TreeLeaf x) ->
      case asArrayKindMaybe x of
        Nothing ->
          raiseSyntaxError (fst e) "SINT-TYPE | UINT-TYPE | FLOAT-TYPE"
        Just t ->
          return t
    _ ->
      raiseSyntaxError (fst tree) "LEAF"

-- raiseSyntaxError :: Hint -> T.Text -> WithEnv a
-- raiseSyntaxError m form =
--   raiseError m $ "couldn't match the input with the expected form: " <> form

interpretWith :: TreePlus -> WithEnv WeakTermPlus
interpretWith tree =
  case tree of
    (m, TreeNode (with@(_, TreeLeaf "with") : bind : (_, TreeNode ((_, TreeLeaf "let") : xt : es)) : rest)) -> do
      (borrowVarList, es') <- interpretBorrow m es
      if not (null borrowVarList)
        then do
          sig <- newTextWith "borrow"
          -- macroExpand >=> interpretWith $
          interpretWith $
            ( m,
              TreeNode
                [ with,
                  bind,
                  (m, TreeNode ((m, TreeLeaf "let") : (m, TreeLeaf sig) : es')),
                  ( m,
                    TreeNode
                      [ (m, TreeLeaf "sigma-elimination"),
                        (m, TreeNode (borrowVarList ++ [xt])),
                        (m, TreeLeaf sig),
                        (m, TreeNode (with : bind : rest))
                      ]
                  )
                ]
            )
        else do
          bind' <- interpret bind
          h1 <- newAster m
          h2 <- newAster m
          e' <- interpretWith (m, TreeNode (with : bind : es'))
          xt' <- interpretWeakIdentPlus xt
          rest' <- interpretWith (m, TreeNode (with : bind : rest))
          return (m, WeakTermPiElim bind' [h1, h2, e', (m, WeakTermPiIntro [xt'] rest')])
    (m, TreeNode (with@(_, TreeLeaf "with") : bind : (_, TreeNode ((_, TreeLeaf "erase") : xs)) : rest)) ->
      case mapM asLeaf xs of
        Nothing ->
          raiseSyntaxError m "(with TREE (erase LEAF ... LEAF) TREE*)"
        Just xs' -> do
          rest' <- interpretWith (m, TreeNode (with : bind : rest))
          return (m, WeakTermErase xs' rest')
    (_, TreeNode [(_, TreeLeaf "with"), _, e]) ->
      interpret e
    (m, TreeNode (with@(_, TreeLeaf "with") : bind : e : rest)) -> do
      let e' = (m, TreeNode [(m, TreeLeaf "let"), (m, TreeLeaf "_"), e])
      interpretWith (m, TreeNode (with : bind : e' : rest))
    t ->
      raiseSyntaxError (fst t) "(with TREE TREE+)"

interpretBorrow :: Hint -> [TreePlus] -> WithEnv ([TreePlus], [TreePlus])
interpretBorrow m treeList =
  case treeList of
    [] ->
      raiseSyntaxError m "(TREE TREE*)"
    es -> do
      let (borrowVarList, e') = interpretBorrow' $ last es
      return (borrowVarList, init es ++ [e'])

interpretBorrow' :: TreePlus -> ([TreePlus], TreePlus)
interpretBorrow' tree =
  case tree of
    t@(_, TreeLeaf _) ->
      ([], t)
    (m, TreeNode ts) -> do
      let (mmxs, ts') = unzip $ map interpretBorrow'' ts
      (catMaybes mmxs, (m, TreeNode ts'))

interpretBorrow'' :: TreePlus -> (Maybe TreePlus, TreePlus)
interpretBorrow'' tree =
  case tree of
    (m, TreeLeaf s)
      | T.length s > 1,
        T.head s == '&' ->
        (Just (m, TreeLeaf $ T.tail s), (m, TreeLeaf $ T.tail s))
    t ->
      (Nothing, t)
