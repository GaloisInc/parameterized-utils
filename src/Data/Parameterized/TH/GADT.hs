------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.TH.GADT
-- Copyright        : (c) Galois, Inc 2013-2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
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
  , dataParamTypes
  , assocTypePats
  ) where

import Control.Monad
import Data.Hashable (hashWithSalt)
import Data.List
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Language.Haskell.TH


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
                } deriving (Show)

asTyConI :: Info -> Maybe Dec
asTyConI (TyConI d) = Just d
asTyConI _ = Nothing

#if MIN_VERSION_template_haskell(2,11,0)
gadtArgTypes :: Type -> [Type]
gadtArgTypes (AppT c x) = gadtArgTypes c ++ [x]
gadtArgTypes ConT{} = []
gadtArgTypes tp = error $ "Unexpected GADT return type: " ++ show tp
#endif

asDataD :: Dec -> Maybe DataD
#if MIN_VERSION_template_haskell(2,11,0)
asDataD (DataD ctx n v _ ctors _d) = Just $ DD { _dataCtx = ctx
                                              , _dataName = n
                                              , dataTyVarBndrs = v
                                              , dataCtors = ctors
                                              }
#else
asDataD (DataD ctx n v ctors _d) = Just $ DD ctx n v ctors
#endif
asDataD _ = Nothing

infixPat :: Name -> String -> Q (Pat, [Name])
infixPat nm pre = do
  xnm <- newName pre
  ynm <- newName pre
  return (InfixP (VarP xnm) nm (VarP ynm), [xnm, ynm])

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
conPat (InfixC _ nm _) pre = infixPat nm pre
conPat (ForallC _ _ c) pre = conPat c pre
#if MIN_VERSION_template_haskell(2,11,0)
conPat (GadtC nms a _) pre =
  case nms of
    [nm] -> do
      argNms <- replicateM (length a) (newName pre)
      return (ConP nm (VarP <$> argNms), argNms)
    _ ->
      fail $ "conPat does not support GADTs with multiple ctors per declaration"
conPat RecGadtC{} _ = error "conPat does not support record GADTs."
#endif

-- | Get types of arguments for constructor.
conArgTypes :: Con
            -> [Type]
conArgTypes (NormalC _ a)              = snd <$> a
conArgTypes (RecC _ a)                 = (\(_,_,tp) -> tp) <$> a
conArgTypes (InfixC (_,xtp) _ (_,ytp)) = [xtp, ytp]
conArgTypes (ForallC _ _ c) = conArgTypes c
#if MIN_VERSION_template_haskell(2,11,0)
conArgTypes (GadtC _ a _)              = snd <$> a
conArgTypes RecGadtC{} = error "conArgTypes does not support GADTs."
#endif

-- | Return an expression corresponding to the constructor.
-- Note that this will have the type of a function expecting
-- the argumnts given.
conName :: Con -> Name
conName (NormalC nm _) = nm
conName (RecC nm _)   = nm
conName (InfixC _ nm _) = nm
conName (ForallC _ _ c) = conName c
#if MIN_VERSION_template_haskell(2,11,0)
conName (GadtC nms _ _) =
  case nms of
    [nm] -> nm
    _ -> error "conName does not support multi ctor GADTs."
conName RecGadtC{} = error "conName does not support record GADTs."
#endif

-- | Return an expression corresponding to the constructor.
-- Note that this will have the type of a function expecting
-- the argumetns given.
conExpr :: Con -> Exp
conExpr c = ConE (conName c)

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

dataParamTypes :: DataD -> [Type]
dataParamTypes d = VarT . tyVarName <$> dataTyVarBndrs d

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
mkEqF :: DataD -- ^ Data declaration.
      -> [(TypePat,ExpQ)]
      -> Con
      -> [MatchQ]
mkEqF d pats (NormalC nm a) = (:[]) $ do
  let dVars = tyVarName <$> dataTyVarBndrs d
  let bnd | null dVars = Set.empty
          | otherwise  = Set.fromList (init dVars)
  mkSimpleEqF (VarT <$> dVars) bnd pats nm (snd <$> a)
mkEqF d pats (RecC nm a) = (:[]) $ do
  let dVars = tyVarName <$> dataTyVarBndrs d
  let bnd | null dVars = Set.empty
          | otherwise  = Set.fromList (init dVars)
  mkSimpleEqF (VarT <$> dVars) bnd pats nm ((\(_,_,tp) -> tp) <$> a)
mkEqF d pats (InfixC (_,xtp) nm (_,ytp)) = (:[]) $ do
  let tps = [ xtp, ytp ]
  (xp,xv) <- infixPat nm "x"
  (yp,yv) <- infixPat nm "y"
  let rv = matchEqArguments (dataParamTypes d) pats nm Set.empty tps xv yv
  match (pure (TupP [xp, yp])) (normalB rv) []
mkEqF d pats (ForallC _ _ c) = mkEqF d pats c
#if MIN_VERSION_template_haskell(2,11,0)
mkEqF _ _ RecGadtC{} = do
  fail "mkEqF does not support record GADTs."
mkEqF _ pats (GadtC nms a tp) = f <$> nms
  where f nm = do
          mkSimpleEqF (gadtArgTypes tp) Set.empty pats nm (snd <$> a)
#endif

-- | @structuralTypeEquality f@ returns a function with the type:
--   forall x y . f x -> f y -> Maybe (x :~: y)
structuralTypeEquality :: TypeQ -> [(TypePat,ExpQ)] -> ExpQ
structuralTypeEquality tpq pats = do
  d <- lookupDataType' =<< asTypeCon "structuralTypeEquality" =<< tpq
  let trueEqs = concatMap (mkEqF d pats) (dataCtors d)
      baseEq  = match [p| (_, _)|] (normalB [| Nothing |]) []
  [| \x y -> $(caseE [| (x, y) |] (trueEqs ++ [baseEq])) |]

-- | @structuralTypeEquality f@ returns a function with the type:
--   forall x y . f x -> f y -> OrderingF x y
structuralTypeOrd :: TypeQ
                  -> [(TypePat,ExpQ)] -- ^ List of type patterns to match.
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
mkOrdF :: DataD -- ^ Data declaration.
       -> [(TypePat,ExpQ)] -- ^ Patterns for matching arguments
       -> Con
       -> Q [MatchQ]
mkOrdF d pats (NormalC nm a) = do
  mkSimpleOrdF (dataParamTypes d) pats nm (snd <$> a)
mkOrdF d pats (RecC nm a) = do
  mkSimpleOrdF (dataParamTypes d) pats nm ((\(_,_,tp) -> tp) <$> a)
mkOrdF d pats (InfixC (_,xtp) nm (_,ytp)) = do
  let tps = [ xtp, ytp ]
  -- Get argument types for constructor.
  (xp,xv) <- infixPat nm "x"
  (yp,yv) <- infixPat nm "y"
  --let dataVars = Set.fromList dataVarNames
  rv <- matchOrdArguments (dataParamTypes d) pats nm Set.empty tps xv yv
  ltf <- [| LTF |]
  gtf <- [| GTF |]
  let anyPat = InfixP WildP nm WildP
  -- Return match expression
  return [ pure $ Match (TupP [xp, yp]) (NormalB rv) []
         , pure $ Match (TupP [anyPat, WildP]) (NormalB ltf) []
         , pure $ Match (TupP [WildP, anyPat]) (NormalB gtf) []
         ]
mkOrdF d pats (ForallC _ _ c) =
  mkOrdF d pats c
#if MIN_VERSION_template_haskell(2,11,0)
mkOrdF _ _ RecGadtC{} = do
  fail "mkOrdF does not support record GADTs."
mkOrdF _ pats (GadtC nms a tp) = fmap concat $ do
  forM nms $ \nm -> do
    mkSimpleOrdF (gadtArgTypes tp) pats nm (snd <$> a)
#endif

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
  d <- lookupDataType' =<< asTypeCon "structuralTraversal" =<< tpq
  f <- newName "f"
  a <- newName "a"
  lamE [varP f, varP a] $
    caseE (varE a)
      (traverseAppMatch (assocTypePats (dataParamTypes d) pats0) (varE f) <$> dataCtors d)

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

showCon :: ExpQ -> Name -> Int -> MatchQ
showCon p nm n = do
  vars <- replicateM n $ newName "x"
  let pat = ConP nm (VarP <$> vars)
  let go s e = [| $(s) . showChar ' ' . showsPrec 10 $(varE e) |]
  let ctor = [| showString $(return (LitE (StringL (nameBase nm)))) |]
  let rhs | null vars = ctor
          | otherwise = [| showParen ($(p) >= 10) $(foldl go ctor vars) |]
  match (pure pat) (normalB rhs) []

matchShowCtor :: ExpQ -> Con -> MatchQ
matchShowCtor p (NormalC nm tps) = showCon p nm (length tps)
matchShowCtor _ RecC{} = error "structuralShow does not support records."
matchShowCtor _ InfixC{} = error "structuralShow does not support infix constructors."
matchShowCtor p (ForallC _ _ c) = matchShowCtor p c
#if MIN_VERSION_template_haskell(2,11,0)
matchShowCtor p (GadtC nms a _) =
  case nms of
    [nm] -> showCon p nm (length a)
    _ -> error $ "matchShowCtor does not support GADTs with multiple ctors per declaration"
matchShowCtor _ RecGadtC{} = error "structuralShow does not support GADT records."
#endif
