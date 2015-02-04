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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.TH.GADT
  ( structuralEquality
  , structuralTypeEquality
  , structuralTraversal
  , structuralShowsPrec
  , structuralHash
  , PolyEq(..)
    -- * Template haskell utilities that may be useful in other contexts.
  , DataD(..)
  , lookupDataType'
  , asTypeCon
  ) where

import Control.Applicative
import Control.Monad
import Data.Hashable (hashWithSalt)
import Data.Maybe
import Data.Traversable (traverse)
import Language.Haskell.TH

import Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx

------------------------------------------------------------------------
-- Template Haskell utilities

data DataD = DD { _dataCtx :: Cxt
                , _dataName :: Name
                , _dataTypeVars :: [TyVarBndr]
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
conExpr :: Con -> Exp
conExpr (NormalC nm _) = ConE nm
conExpr (RecC nm _)   = ConE nm
conExpr (InfixC _ nm _) = ConE nm
conExpr (ForallC _ _ c) = conExpr c

------------------------------------------------------------------------
-- Contructor cases

isGroundType :: Type -> Bool
isGroundType (ConT _) = True
isGroundType (AppT f a) = isGroundType f && isGroundType a
isGroundType _ = False

lookupDataType' :: Name -> Q DataD
lookupDataType' tpName = do
  info <- reify tpName
  maybe (fail $ "Expected datatype: " ++ show (ppr tpName)) return $
    asDataD =<< asTyConI info

-- | @declareStructuralEquality@ declares a structural equality predicate.
structuralEquality :: TypeQ -> ExpQ
structuralEquality tpq = [| \x y -> isJust ($(structuralTypeEquality tpq) x y) |]

mkEqF :: Con -> MatchQ
mkEqF c = do
  -- Get argument types for constructor.
  (xp,xv) <- conPat c "x"
  (yp,yv) <- conPat c "y"
  let go :: (Type,Name,Name) -> ExpQ -> ExpQ
      go (tp, x, y) r | isGroundType tp = [| if $(varE x) == $(varE y) then $(r) else Nothing |]
      go (AppT (ConT _) (VarT _),  x, y) r = do
        [| do Refl <- testEquality $(varE x) $(varE y)
              $(r) |]
      go (_,  x, y) r = do
        [| do Refl <- polyEqF $(varE x) $(varE y)
              $(r) |]
  let base = [| return Refl |]
  let rv = foldr go base (zip3 (conArgTypes c) xv yv)
  match (pure (TupP [xp, yp])) (normalB rv) []

-- | @declareStructuralEquality@ declares a structural equality predicate.
structuralTypeEquality :: TypeQ -> ExpQ
structuralTypeEquality tpq = do
  d <- lookupDataType' =<< asTypeCon "structuralTypeEquality" =<< tpq
  let trueEqs = (mkEqF <$> dataCtors d)
      baseEq = match [p| (_, _)|] (normalB [| Nothing |]) []
  [| \x y -> $(caseE [| (x, y) |] (trueEqs ++ [baseEq])) |]

-- | Parse type and identify if this is an arg left unchanged
-- or arg with more inforamtion.
-- Returns variable binding arg for pattern matching, and
-- information needed for traversal.
recurseArg :: Exp -> Name -> Type -> Q (Maybe Exp)
recurseArg f v (AppT (AppT (ConT cnm) _) _)
  | nameBase cnm `elem` [ "Assignment" ]
  = Just <$> [| Ctx.traverseF $(pure f) $(varE v) |]
recurseArg f v (AppT (ConT _var) (AppT (VarT _) _)) = do
  Just <$> [| traverse $(pure f) $(varE v) |]
recurseArg f v (AppT (VarT _) _) = do
  Just <$> [| $(pure f) $(varE v) |]
recurseArg _ _ _ = return Nothing

-- | @traverseAppMatch f c@ builds a case statement that matches a term with
-- the constructor @c@ and applies @f@ to each argument.
traverseAppMatch :: Exp -- ^ Function to apply to each argument recursively.
                 -> Con -- ^ Constructor to match.
                 -> MatchQ -- ^ Match expression that
traverseAppMatch fv c0 = do
  (pat,patArgs) <- conPat c0 "p"
  exprs <- zipWithM (recurseArg fv) patArgs (conArgTypes c0)

  let mkRes :: ExpQ -> [(Name, Maybe Exp)] -> ExpQ
      mkRes e [] = e
      mkRes e ((v,Nothing):r) = mkRes (appE e (varE v)) r
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
structuralTraversal :: TypeQ -> ExpQ
structuralTraversal tpq = do
  d <- lookupDataType' =<< asTypeCon "structuralTraversal" =<< tpq
  f <- newName "f"
  a <- newName "a"
  lamE [varP f, varP a] $
    caseE (varE a) (traverseAppMatch (VarE f) <$> dataCtors d)

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
