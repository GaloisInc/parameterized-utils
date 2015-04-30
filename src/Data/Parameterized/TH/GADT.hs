------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.TH.GADT
-- Description      : Utilities for traversing GADTs
-- Copyright        : (c) Galois, Inc 2013-2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module declares template Haskell primitives so that it is easier
-- to work with GADTs that have many constructors.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.TH.GADT
  ( structuralEquality
  , structuralTypeEquality
  , structuralTypeOrd
  , structuralTraversal
  , structuralShowsPrec
  , structuralHash
  , PolyEq(..)
    -- * Template haskell utilities that may be useful in other contexts.
  , DataD(..)
  , lookupDataType'
  , asTypeCon
  , TypePat(..)
  ) where

import Control.Lens hiding (pre)
import Control.Monad
import Data.Hashable (hashWithSalt)
import Data.List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Language.Haskell.TH

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import Data.Parameterized.Classes

------------------------------------------------------------------------
-- Template Haskell utilities

tyVarName :: TyVarBndr -> Name
tyVarName (PlainTV nm) = nm
tyVarName (KindedTV nm _) = nm

data DataD = DD { _dataCtx :: Cxt
                , _dataName :: Name
                , dataTyVarBndrs :: [TyVarBndr]
                , dataCtors :: [Con]
                , _dataDeriving :: [Name]
                } deriving (Show)

asTyConI :: Info -> Maybe Dec
asTyConI (TyConI d) = Just d
asTyConI _ = Nothing

asDataD :: Dec -> Maybe DataD
asDataD (DataD ctx n v ctors d) = Just $ DD ctx n v ctors d
asDataD _ = Nothing

-- | Given a constructor and string, this generates a pattern for matching
-- the expression, and the names of variables bound by pattern in order
-- they appear in constructor.
conPat :: Con
        -> String
        -> Q (Pat, [Name])
conPat (NormalC nm a) pre = do
  nms <- replicateM (length a) (newName pre)
  return (ConP nm (VarP <$> nms), nms)
conPat (RecC nm a) pre = do
  nms <- replicateM (length a) (newName pre)
  return (ConP nm (VarP <$> nms), nms)
conPat (InfixC _ nm _) pre = do
  xnm <- newName pre
  ynm <- newName pre
  return (InfixP (VarP xnm) nm (VarP ynm), [xnm, ynm])
conPat (ForallC _ _ c) pre = conPat c pre

-- | Given a constructor, this generates a pattern for matching
-- the constructor with no bound varibles.
conPat_ :: Con -> Pat
conPat_ (NormalC nm a) = ConP nm (replicate (length a) WildP)
conPat_ (RecC nm a)    = ConP nm (replicate (length a) WildP)
conPat_ (InfixC _ nm _) = InfixP WildP nm WildP
conPat_ (ForallC _ _ c) = conPat_ c

-- | Get types of arguments for constructor.
conArgTypes :: Con
            -> [Type]
conArgTypes (NormalC _ a)              = snd <$> a
conArgTypes (RecC _ a)                 = (\(_,_,tp) -> tp) <$> a
conArgTypes (InfixC (_,xtp) _ (_,ytp)) = [xtp, ytp]
conArgTypes (ForallC _ _ c) = conArgTypes c


-- | Return an expression corresponding to the constructor.
-- Note that this will have the type of a function expecting
-- the argumetns given.
conName :: Con -> Name
conName (NormalC nm _) = nm
conName (RecC nm _)   = nm
conName (InfixC _ nm _) = nm
conName (ForallC _ _ c) = conName c

-- | Return an expression corresponding to the constructor.
-- Note that this will have the type of a function expecting
-- the argumetns given.
conExpr :: Con -> Exp
conExpr c = ConE (conName c)

------------------------------------------------------------------------
-- TypePat

data TypePat
   = TypeApp TypePat TypePat
   | AnyType
   | DataArg Int
   | ConType TypeQ

matchTypePat :: DataD -> TypePat -> Type -> Q Bool
matchTypePat d (TypeApp p q) (AppT x y) = do
  r <- matchTypePat d p x
  case r of
    True -> matchTypePat d q y
    False -> return False
matchTypePat _ AnyType _ = return True
matchTypePat d (DataArg i) tp
  | i < 0 || i > length (dataTyVarBndrs d) = error $ "Illegal type pattern index " ++ show i
  | otherwise =
    return $ VarT (tyVarName (dataTyVarBndrs d !! i)) == tp
matchTypePat _ (ConType tpq) tp = do
  tp' <- tpq
  return (tp' == tp)
matchTypePat _ _ _ = return False

matchTypePats :: DataD -> [TypePat] -> Type -> Q Bool
matchTypePats _ [] _ = return False
matchTypePats d (p:pats) tp = do
  r <- matchTypePat d p tp
  case r of
    True -> return True
    False -> matchTypePats d pats tp

------------------------------------------------------------------------
-- Contructor cases

typeVars :: Type -> Set Name
typeVars tp = typeVars' tp Set.empty

typeVars' :: Type -> Set Name -> Set Name
typeVars' (ForallT vars _ tp) s =
  foldl' (flip Set.delete) (typeVars' tp s) (tyVarName <$> vars)
typeVars' (AppT x y) s = typeVars' x $! typeVars' y s
typeVars' (SigT t _) s = typeVars' t s
typeVars' (VarT nm) s = Set.insert nm s
typeVars' _ s = s

lookupDataType' :: Name -> Q DataD
lookupDataType' tpName = do
  info <- reify tpName
  maybe (fail $ "Expected datatype: " ++ show (ppr tpName)) return $
    asDataD =<< asTyConI info

-- | @declareStructuralEquality@ declares a structural equality predicate.
structuralEquality :: TypeQ -> [TypePat] -> ExpQ
structuralEquality tpq pats =
  [| \x y -> isJust ($(structuralTypeEquality tpq pats) x y) |]

joinEqMaybe :: Name -> Name -> ExpQ -> ExpQ
joinEqMaybe x y r = do
  [| if $(varE x) == $(varE y) then $(r) else Nothing |]

joinTestEquality :: Name -> Name -> ExpQ -> ExpQ
joinTestEquality x y r =
  [| case testEquality $(varE x) $(varE y) of
      Nothing -> Nothing
      Just Refl -> $(r)
   |]

-- | Match equational form.
mkEqF :: DataD -- ^ Data declaration.
      -> [TypePat]
      -> Con
      -> MatchQ
mkEqF d pats c = do
  -- Get argument types for constructor.
  (xp,xv) <- conPat c "x"
  (yp,yv) <- conPat c "y"

  let go :: Set Name -> [Type] -> [Name] -> [Name] -> ExpQ
      go bnd (tp:tpl) (x:xl) (y:yl) = do
        doesMatch <- matchTypePats d pats tp
        case doesMatch of
          True -> do
            let bnd' =
                  case tp of
                    AppT _ (VarT nm) -> Set.insert nm bnd
                    _ -> bnd
            joinTestEquality x y (go bnd' tpl xl yl)
          False | typeVars tp `Set.isSubsetOf` bnd -> do
            joinEqMaybe x y (go bnd tpl xl yl)
          False -> do
            fail $ "Unsupported argument type " ++ show (ppr tp)
                ++ " in " ++ show (ppr (conName c)) ++ "."
      go _ [] [] [] = [| Just Refl |]
      go _ [] _ _ = error "Unexpected end of types."
      go _ _ [] _ = error "Unexpected end of names."
      go _ _ _ [] = error "Unexpected end of names."

  let dataVars = Set.fromList (tyVarName <$> dataTyVarBndrs d)
  let rv = go dataVars (conArgTypes c) xv yv
  match (pure (TupP [xp, yp])) (normalB rv) []

-- | @structuralTypeEquality f@ returns a function with the type:
--   forall x y . f x -> f y -> Maybe (x :~: y)
structuralTypeEquality :: TypeQ -> [TypePat] -> ExpQ
structuralTypeEquality tpq pats = do
  d <- lookupDataType' =<< asTypeCon "structuralTypeEquality" =<< tpq
  let trueEqs = (mkEqF d pats <$> dataCtors d)
      baseEq = match [p| (_, _)|] (normalB [| Nothing |]) []
  [| \x y -> $(caseE [| (x, y) |] (trueEqs ++ [baseEq])) |]

-- | @structuralTypeEquality f@ returns a function with the type:
--   forall x y . f x -> f y -> OrderingF x y
structuralTypeOrd :: TypeQ
                  -> [TypePat] -- ^ List of type patterns to match.
                  -> ExpQ
structuralTypeOrd tpq l = do
  d <- lookupDataType' =<< asTypeCon "structuralTypeEquality" =<< tpq
  matchEqs <- traverse (mkOrdF d l) (dataCtors d)
  case reverse matchEqs of
    [] -> do
      [| \_ _ -> EQF |]
    [t,_,_] : r -> do
      [| \x y -> $(caseE [| (x, y) |] (concat (reverse ([t]:r)))) |]
    _ -> error "Bad return value from structuralTypeOrd"


joinCompareF :: Name -> Name -> ExpQ -> ExpQ
joinCompareF x y r = do
  [| case compareF $(varE x) $(varE y) of
      LTF -> LTF
      GTF -> GTF
      EQF -> $(r)
   |]

joinCompareToOrdF :: Name -> Name -> ExpQ -> ExpQ
joinCompareToOrdF x y r =
  [| case compare $(varE x) $(varE y) of
      LT -> LTF
      GT -> GTF
      EQ -> $(r)
   |]

-- | Match equational form.
mkOrdF :: DataD -- ^ Data declaration.
       -> [TypePat] -- ^ Second order argument types.
       -> Con
       -> Q [MatchQ]
mkOrdF d pats c = do
  -- Get argument types for constructor.
  (xp,xv) <- conPat c "x"
  (yp,yv) <- conPat c "y"
  -- Match expression with given type to variables
  let go :: Set Name -> [Type] -> [Name] -> [Name] -> ExpQ
      -- Use testEquality on vars with second order types.
      go bnd (tp : tpl) (x:xl) (y:yl) = do
        doesMatch <- matchTypePats d pats tp
        case doesMatch of
          True -> do
            let bnd' = case tp of
                         AppT _ (VarT nm) -> Set.insert nm bnd
                         _ -> bnd
            joinCompareF x y (go bnd' tpl xl yl)
          False | typeVars tp `Set.isSubsetOf` bnd -> do
            joinCompareToOrdF x y (go bnd tpl xl yl)
          False ->
            fail $ "Unsupported argument type " ++ show (ppr tp)
                ++ " in " ++ show (ppr (conName c)) ++ "."
      go _ [] [] [] = [| EQF |]
      go _ [] _ _ = error "Unexpected end of types."
      go _ _ [] _ = error "Unexpected end of names."
      go _ _ _ [] = error "Unexpected end of names."

  -- Zip types together
  let dataVars = Set.fromList (tyVarName <$> dataTyVarBndrs d)
  rv <- go dataVars (conArgTypes c) xv yv
  ltf <- [| LTF |]
  gtf <- [| GTF |]
  -- Return match expression
  return [ pure $ Match (TupP [xp, yp]) (NormalB rv) []
         , pure $ Match (TupP [conPat_ c, WildP]) (NormalB ltf) []
         , pure $ Match (TupP [WildP, conPat_ c]) (NormalB gtf) []
         ]

type TraversePats = [(Type -> Q Bool, ExpQ)]

-- | @recurseArg f var tp@ applies @f@ to @var@ where @var@ has type @tp@.
recurseArg :: TraversePats
           -> ExpQ -- ^ Function to apply
           -> ExpQ
           -> Type
           -> Q (Maybe Exp)
recurseArg ((p,g):r) f v tp = do
  b <- p tp
  if b then
    Just <$> [| $(g) $(f) $(v) |]
  else
    recurseArg r f v tp
recurseArg [] f v (AppT (ConT _) (AppT (VarT _) _)) = Just <$> [| traverse $(f) $(v) |]
recurseArg [] f v (AppT (VarT _) _)                 = Just <$> [| $(f) $(v) |]
recurseArg [] _ _ _ = return Nothing

-- | @traverseAppMatch f c@ builds a case statement that matches a term with
-- the constructor @c@ and applies @f@ to each argument.
traverseAppMatch :: TraversePats -- ^ Variables bound in data
                 -> ExpQ -- ^ Function to apply to each argument recursively.
                 -> Con -- ^ Constructor to match.
                 -> MatchQ -- ^ Match expression that
traverseAppMatch pats fv c0 = do
  (pat,patArgs) <- conPat c0 "p"
  exprs <- zipWithM (recurseArg pats fv) (varE <$> patArgs) (conArgTypes c0)

  let mkRes :: ExpQ -> [(Name, Maybe Exp)] -> ExpQ
      mkRes e [] = e
      mkRes e ((v,Nothing):r) =
        mkRes (appE e (varE v)) r
      mkRes e ((_,Just{}):r) = do
        v <- newName "r"
        lamE [varP v] (mkRes (appE e (varE v)) r)

  -- Apply the reamining argument to the expression in list.
  let applyRest :: ExpQ -> [Exp] -> ExpQ
      applyRest e [] = e
      applyRest e (a:r) = applyRest [| $(e) <*> $(pure a) |] r

  -- Apply the first argument to the list
  let applyFirst :: ExpQ -> [Exp] -> ExpQ
      applyFirst e [] = [| pure $(e) |]
      applyFirst e (a:r) = applyRest [| $(e) <$> $(pure a) |] r

  let pargs = patArgs `zip` exprs
  let rhs = applyFirst (mkRes (pure (conExpr c0)) pargs) (catMaybes exprs)
  match (pure pat) (normalB rhs) []

-- | @structuralTraversal tp@ generates a function that applies
-- a traversal @f@ to the subterms with free variables in @tp@.
structuralTraversal :: TypeQ -> [(TypePat, ExpQ)] -> ExpQ
structuralTraversal tpq pats0 = do
  d <- lookupDataType' =<< asTypeCon "structuralTraversal" =<< tpq
  f <- newName "f"
  a <- newName "a"
  let pats = fmap (over _1 (matchTypePat d)) pats0
  lamE [varP f, varP a] $
    caseE (varE a) (traverseAppMatch pats (varE f) <$> dataCtors d)

asTypeCon :: Monad m => String -> Type -> m Name
asTypeCon _ (ConT nm) = return nm
asTypeCon fn _ = fail $ fn ++ " expected type constructor."

-- | @structuralHash tp@ generates a function with the type
-- @Int -> tp -> Int@ that hashes type.
structuralHash :: TypeQ -> ExpQ
structuralHash tpq = do
  d <- lookupDataType' =<< asTypeCon "structuralHash" =<< tpq
  s <- newName "s"
  a <- newName "a"
  lamE [varP s, varP a] $
    caseE (varE a) (zipWith (matchHashCtor (varE s)) [0..] (dataCtors d))

matchHashCtor :: ExpQ -> Integer  -> Con -> MatchQ
matchHashCtor s0 i c = do
  (pat,vars) <- conPat c "x"
  let args = [| $(litE (IntegerL i)) :: Int |] : (varE <$> vars)
  let go s e = [| hashWithSalt $(s) $(e) |]
  let rhs = foldl go s0 args
  match (pure pat) (normalB rhs) []

-- | @structuralShow tp@ generates a function with the type
-- @tp -> ShowS@ that shows the constructor.
structuralShowsPrec :: TypeQ -> ExpQ
structuralShowsPrec tpq = do
  d <- lookupDataType' =<< asTypeCon "structuralShowPrec" =<< tpq
  p <- newName "_p"
  a <- newName "a"
  lamE [varP p, varP a] $
    caseE (varE a) (matchShowCtor (varE p) <$> dataCtors d)

matchShowCtor :: ExpQ -> Con -> MatchQ
matchShowCtor p (NormalC nm tps) = do
  (pat,vars) <- conPat (NormalC nm tps) "x"
  let go s e = [| $(s) . showChar ' ' . showsPrec 10 $(varE e) |]
  let ctor = [| showString $(return (LitE (StringL (nameBase nm)))) |]
  let rhs | null vars = ctor
          | otherwise = [| showParen ($(p) >= 10) $(foldl go ctor vars) |]
  match (pure pat) (normalB rhs) []
matchShowCtor p (ForallC _ _ c) = matchShowCtor p c
matchShowCtor _ _ = error "structuralShow only support normal constructors."
