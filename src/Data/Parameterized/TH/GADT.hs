------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.TH.GADT
-- Copyright        : (c) Galois, Inc 2013-2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
--
-- This module declares template Haskell primitives so that it is easier
-- to work with GADTs that have many constructors.
------------------------------------------------------------------------
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
  , DataD
  , lookupDataType'
  , asTypeCon
  , conPat
  , TypePat(..)
  , dataParamTypes
  , assocTypePats
  ) where

import Control.Monad
import Data.Hashable (hashWithSalt)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Language.Haskell.TH
import Language.Haskell.TH.Datatype


import Data.Parameterized.Classes

------------------------------------------------------------------------
-- Template Haskell utilities

type DataD = DatatypeInfo

lookupDataType' :: Name -> Q DatatypeInfo
lookupDataType' = reifyDatatype

-- | Given a constructor and string, this generates a pattern for matching
-- the expression, and the names of variables bound by pattern in order
-- they appear in constructor.
conPat ::
  ConstructorInfo {- ^ constructor information -} ->
  String          {- ^ generated name prefix   -} ->
  Q (Pat, [Name]) {- ^ pattern and bound names -}
conPat con pre = do
  nms <- replicateM (length (constructorFields con)) (newName pre)
  return (ConP (constructorName con) (VarP <$> nms), nms)


-- | Return an expression corresponding to the constructor.
-- Note that this will have the type of a function expecting
-- the argumetns given.
conExpr :: ConstructorInfo -> Exp
conExpr = ConE . constructorName

------------------------------------------------------------------------
-- TypePat

data TypePat
   = TypeApp TypePat TypePat -- ^ The application of a type.
   | AnyType       -- ^ Match any type.
   | DataArg Int   -- ^ Match the ith argument of the data type we are traversing.
   | ConType TypeQ -- ^ Match a ground type.

matchTypePat :: [Type] -> TypePat -> Type -> Q Bool
matchTypePat d (TypeApp p q) (AppT x y) = do
  r <- matchTypePat d p x
  case r of
    True -> matchTypePat d q y
    False -> return False
matchTypePat _ AnyType _ = return True
matchTypePat tps (DataArg i) tp
  | i < 0 || i > length tps = error $ "Illegal type pattern index " ++ show i
  | otherwise = do
    return $ tps !! i == tp
matchTypePat _ (ConType tpq) tp = do
  tp' <- tpq
  return (tp' == tp)
matchTypePat _ _ _ = return False

dataParamTypes :: DatatypeInfo -> [Type]
dataParamTypes = datatypeVars

-- | Find value associated with first pattern that matches given pat if any.
assocTypePats :: [Type] -> [(TypePat,v)] -> Type -> Q (Maybe v)
assocTypePats _ [] _ = return Nothing
assocTypePats dTypes ((p,v):pats) tp = do
  r <- matchTypePat dTypes p tp
  case r of
    True -> return (Just v)
    False -> assocTypePats dTypes pats tp

------------------------------------------------------------------------
-- Contructor cases

typeVars :: TypeSubstitution a => a -> Set Name
typeVars = Set.fromList . freeVariables


-- | @declareStructuralEquality@ declares a structural equality predicate.
structuralEquality :: TypeQ -> [(TypePat,ExpQ)] -> ExpQ
structuralEquality tpq pats =
  [| \x y -> isJust ($(structuralTypeEquality tpq pats) x y) |]

joinEqMaybe :: Name -> Name -> ExpQ -> ExpQ
joinEqMaybe x y r = do
  [| if $(varE x) == $(varE y) then $(r) else Nothing |]

joinTestEquality :: ExpQ -> Name -> Name -> ExpQ -> ExpQ
joinTestEquality f x y r =
  [| case $(f) $(varE x) $(varE y) of
      Nothing -> Nothing
      Just Refl -> $(r)
   |]

matchEqArguments :: [Type]
                    -- ^ Types bound by data arguments.
                  -> [(TypePat,ExpQ)] -- ^ Patterns for matching arguments
                 -> Name
                     -- ^ Name of constructor.
                 -> Set Name
                 -> [Type]
                 -> [Name]
                 -> [Name]
                 -> ExpQ
matchEqArguments dTypes pats cnm bnd (tp:tpl) (x:xl) (y:yl) = do
  doesMatch <- assocTypePats dTypes pats tp
  case doesMatch of
    Just q -> do
      let bnd' =
            case tp of
              AppT _ (VarT nm) -> Set.insert nm bnd
              _ -> bnd
      joinTestEquality q x y (matchEqArguments dTypes pats cnm bnd' tpl xl yl)
    Nothing | typeVars tp `Set.isSubsetOf` bnd -> do
      joinEqMaybe x y        (matchEqArguments dTypes pats cnm bnd  tpl xl yl)
    Nothing -> do
      fail $ "Unsupported argument type " ++ show tp
          ++ " in " ++ show (ppr cnm) ++ "."
matchEqArguments _ _ _ _ [] [] [] = [| Just Refl |]
matchEqArguments _ _ _ _ [] _  _  = error "Unexpected end of types."
matchEqArguments _ _ _ _ _  [] _  = error "Unexpected end of names."
matchEqArguments _ _ _ _ _  _  [] = error "Unexpected end of names."

mkSimpleEqF :: [Type] -- ^ Data declaration types
            -> Set Name
             -> [(TypePat,ExpQ)] -- ^ Patterns for matching arguments
             -> Name
             -> [Type]
             -> MatchQ
mkSimpleEqF dTypes bnd pats nm a = do
  -- Get argument types for constructor.
  xv <- replicateM (length a) $ newName "x"
  yv <- replicateM (length a) $ newName "y"
  let xp = ConP nm (VarP <$> xv)
  let yp = ConP nm (VarP <$> yv)
  let rv = matchEqArguments dTypes pats nm bnd a xv yv
  match (pure (TupP [xp, yp])) (normalB rv) []

-- | Match equational form.
mkEqF :: DatatypeInfo -- ^ Data declaration.
      -> [(TypePat,ExpQ)]
      -> ConstructorInfo
      -> [MatchQ]
mkEqF d pats con =
  let dVars = datatypeVars d
      bnd | null dVars = Set.empty
          | otherwise  = typeVars (init dVars)
  in [mkSimpleEqF dVars bnd pats (constructorName con) (constructorFields con)]

-- | @structuralTypeEquality f@ returns a function with the type:
--   forall x y . f x -> f y -> Maybe (x :~: y)
structuralTypeEquality :: TypeQ -> [(TypePat,ExpQ)] -> ExpQ
structuralTypeEquality tpq pats = do
  d <- reifyDatatype =<< asTypeCon "structuralTypeEquality" =<< tpq
  let trueEqs = concatMap (mkEqF d pats) (datatypeCons d)
      baseEq  = match [p| (_, _)|] (normalB [| Nothing |]) []
  [| \x y -> $(caseE [| (x, y) |] (trueEqs ++ [baseEq])) |]

-- | @structuralTypeEquality f@ returns a function with the type:
--   forall x y . f x -> f y -> OrderingF x y
structuralTypeOrd :: TypeQ
                  -> [(TypePat,ExpQ)] -- ^ List of type patterns to match.
                  -> ExpQ
structuralTypeOrd tpq l = do
  d <- reifyDatatype =<< asTypeCon "structuralTypeEquality" =<< tpq
  matchEqs <- traverse (mkOrdF d l) (datatypeCons d)
  case reverse matchEqs of
    [] -> do
      [| \_ _ -> EQF |]
    [t,_,_] : r -> do
      [| \x y -> $(caseE [| (x, y) |] (concat (reverse ([t]:r)))) |]
    _ -> error "Bad return value from structuralTypeOrd"


joinCompareF :: ExpQ -> Name -> Name -> ExpQ -> ExpQ
joinCompareF f x y r = do
  [| case $(f) $(varE x) $(varE y) of
      LTF -> LTF
      GTF -> GTF
      EQF -> $(r)
   |]

-- | Compare two variables and use following comparison if they are different.
--
-- This returns an 'OrdF' instance.
joinCompareToOrdF :: Name -> Name -> ExpQ -> ExpQ
joinCompareToOrdF x y r =
  [| case compare $(varE x) $(varE y) of
      LT -> LTF
      GT -> GTF
      EQ -> $(r)
   |]

  -- Match expression with given type to variables
matchOrdArguments :: [Type]
                     -- ^ Types bound by data arguments
                  -> [(TypePat,ExpQ)] -- ^ Patterns for matching arguments
                  -> Name
                     -- ^ Name of constructor.
                  -> Set Name
                    -- ^ Names bound in data declaration
                  -> [Type]
                     -- ^ Types for constructors
                  -> [Name]
                     -- ^ Variables bound in first pattern
                  -> [Name]
                     -- ^ Variables bound in second pattern
                  -> ExpQ
matchOrdArguments dTypes pats cnm bnd (tp : tpl) (x:xl) (y:yl) = do
  doesMatch <- assocTypePats dTypes pats tp
  case doesMatch of
    Just f -> do
      let bnd' = case tp of
                   AppT _ (VarT nm) -> Set.insert nm bnd
                   _ -> bnd
      joinCompareF f x y (matchOrdArguments dTypes pats cnm bnd' tpl xl yl)
    Nothing | typeVars tp `Set.isSubsetOf` bnd -> do
      joinCompareToOrdF x y (matchOrdArguments dTypes pats cnm bnd tpl xl yl)
    Nothing ->
      fail $ "Unsupported argument type " ++ show (ppr tp)
             ++ " in " ++ show (ppr cnm) ++ "."
matchOrdArguments _ _ _ _ [] [] [] = [| EQF |]
matchOrdArguments _ _ _ _ [] _  _  = error "Unexpected end of types."
matchOrdArguments _ _ _ _ _  [] _  = error "Unexpected end of names."
matchOrdArguments _ _ _ _ _  _  [] = error "Unexpected end of names."

mkSimpleOrdF :: [Type] -- ^ Data declaration types
             -> [(TypePat,ExpQ)] -- ^ Patterns for matching arguments
             -> Name
             -> [Type]
             -> Q [MatchQ]
mkSimpleOrdF dTypes pats nm a = do
  xv <- replicateM (length a) $ newName "x"
  yv <- replicateM (length a) $ newName "y"
  let xp = ConP nm (VarP <$> xv)
  let yp = ConP nm (VarP <$> yv)
  rv <- matchOrdArguments dTypes pats nm Set.empty a xv yv
  ltf <- [| LTF |]
  gtf <- [| GTF |]
  -- Return match expression
  let anyPat = ConP nm (replicate (length a) WildP)
  return [ pure $ Match (TupP [xp, yp]) (NormalB rv) []
         , pure $ Match (TupP [anyPat, WildP]) (NormalB ltf) []
         , pure $ Match (TupP [WildP, anyPat]) (NormalB gtf) []
         ]

-- | Match equational form.
mkOrdF :: DatatypeInfo -- ^ Data declaration.
       -> [(TypePat,ExpQ)] -- ^ Patterns for matching arguments
       -> ConstructorInfo
       -> Q [MatchQ]
mkOrdF d pats con = mkSimpleOrdF (datatypeVars d) pats (constructorName con) (constructorFields con)

-- | Find the first recurseArg f var tp@ applies @f@ to @var@ where @var@ has type @tp@.
recurseArg :: (Type -> Q (Maybe ExpQ))
           -> ExpQ -- ^ Function to apply
           -> ExpQ
           -> Type
           -> Q (Maybe Exp)
recurseArg m f v tp = do
  mr <- m tp
  case mr of
    Just g ->  Just <$> [| $(g) $(f) $(v) |]
    Nothing ->
      case tp of
        AppT (ConT _) (AppT (VarT _) _) -> Just <$> [| traverse $(f) $(v) |]
        AppT (VarT _) _ -> Just <$> [| $(f) $(v) |]
        _ -> return Nothing

-- | @traverseAppMatch f c@ builds a case statement that matches a term with
-- the constructor @c@ and applies @f@ to each argument.
traverseAppMatch :: (Type -> Q (Maybe ExpQ)) -- Pattern match function
                 -> ExpQ -- ^ Function to apply to each argument recursively.
                 -> ConstructorInfo -- ^ Constructor to match.
                 -> MatchQ -- ^ Match expression that
traverseAppMatch pats fv c0 = do
  (pat,patArgs) <- conPat c0 "p"
  exprs <- zipWithM (recurseArg pats fv) (varE <$> patArgs) (constructorFields c0)

  let mkRes :: ExpQ -> [(Name, Maybe Exp)] -> ExpQ
      mkRes e [] = e
      mkRes e ((v,Nothing):r) =
        mkRes (appE e (varE v)) r
      mkRes e ((_,Just{}):r) = do
        v <- newName "r"
        lamE [varP v] (mkRes (appE e (varE v)) r)

  -- Apply the remaining argument to the expression in list.
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
  d <- reifyDatatype =<< asTypeCon "structuralTraversal" =<< tpq
  f <- newName "f"
  a <- newName "a"
  lamE [varP f, varP a] $
      caseE (varE a)
      (traverseAppMatch (assocTypePats (datatypeVars d) pats0) (varE f) <$> datatypeCons d)

asTypeCon :: Monad m => String -> Type -> m Name
asTypeCon _ (ConT nm) = return nm
asTypeCon fn _ = fail $ fn ++ " expected type constructor."

-- | @structuralHash tp@ generates a function with the type
-- @Int -> tp -> Int@ that hashes type.
structuralHash :: TypeQ -> ExpQ
structuralHash tpq = do
  d <- reifyDatatype =<< asTypeCon "structuralHash" =<< tpq
  s <- newName "s"
  a <- newName "a"
  lamE [varP s, varP a] $
    caseE (varE a) (zipWith (matchHashCtor (varE s)) [0..] (datatypeCons d))

matchHashCtor :: ExpQ -> Integer  -> ConstructorInfo -> MatchQ
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
  d <- reifyDatatype =<< asTypeCon "structuralShowPrec" =<< tpq
  p <- newName "_p"
  a <- newName "a"
  lamE [varP p, varP a] $
    caseE (varE a) (matchShowCtor (varE p) <$> datatypeCons d)

showCon :: ExpQ -> Name -> Int -> MatchQ
showCon p nm n = do
  vars <- replicateM n $ newName "x"
  let pat = ConP nm (VarP <$> vars)
  let go s e = [| $(s) . showChar ' ' . showsPrec 10 $(varE e) |]
  let ctor = [| showString $(return (LitE (StringL (nameBase nm)))) |]
  let rhs | null vars = ctor
          | otherwise = [| showParen ($(p) >= 10) $(foldl go ctor vars) |]
  match (pure pat) (normalB rhs) []

matchShowCtor :: ExpQ -> ConstructorInfo -> MatchQ
matchShowCtor p con = showCon p (constructorName con) (length (constructorFields con))
