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
  , NormalizedCon(..)
  , normalizeCon
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
                , dataCtors :: [NormalizedCon]
                } deriving (Show)

data NormalizedCon = NC
  { nrmlConName   :: Name
  , nrmlConFields :: [Type]
  }
  deriving (Show)

asTyConI :: Info -> Maybe Dec
asTyConI (TyConI d) = Just d
asTyConI _ = Nothing

normalizeCon :: Type -> Con -> Either String [NormalizedCon]
normalizeCon t c =
  case c of
    NormalC n xs      -> pure [NC n (map snd xs)]
    RecC n xs         -> pure [NC n [x | (_,_,x) <- xs ]]
    InfixC l n r      -> pure [NC n [snd l, snd r]]
    ForallC _ _ c'    -> normalizeCon t c'
#if MIN_VERSION_template_haskell(2,11,0)
    GadtC ns xs t'    -> traverse (gadtCase (map snd xs) t t') ns
    RecGadtC ns xs t' -> traverse (gadtCase [x | (_,_,x) <- xs] t t') ns

gadtCase :: [Type] -> Type -> Type -> Name -> Either String NormalizedCon
gadtCase fields t t' n = NC n <$> traverse subst fields
  where
    typeMapping = [ (x,y) | (VarT x, VarT y) <- zip (unappsT t') (unappsT t) ]

    subst (VarT x)        = case lookup x typeMapping of
                              Nothing -> pure WildCardT
                              Just y  -> pure (VarT y)
    subst ForallT{}       = Left "Unable to normalize field types with ForallT"
    subst (AppT f x)      = AppT    <$> subst f <*> subst x
    subst (SigT x y)      = SigT    <$> subst x <*> subst y
    subst (InfixT l c r)  = InfixT  <$> subst l <*> pure c <*> pure r
    subst (UInfixT l c r) = InfixT  <$> subst l <*> pure c <*> pure r
    subst (ParensT x)     = ParensT <$> subst x
    subst x               = pure x

unappsT :: Type -> [Type]
unappsT t = reverse (go t)
  where
    go (AppT f x) = x : go f
    go x          = [x]
#endif

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV  n  ) = n
tyVarBndrName (KindedTV n _) = n

asDataD :: Dec -> Either String DataD
#if MIN_VERSION_template_haskell(2,11,0)
asDataD (DataD ctx n v _ ctors _d) =
#else
asDataD (DataD ctx n v ctors _d) =
#endif
  do let ty = foldl AppT (ConT n) (map (VarT . tyVarBndrName) v)
     nctors <- normalizeCon ty `traverse` ctors
     pure DD
       { _dataCtx = ctx
       , _dataName = n
       , dataTyVarBndrs = v
       , dataCtors = concat nctors
       }
asDataD _ = Left "asDataD: Expected name of data type"

-- | Given a constructor and string, this generates a pattern for matching
-- the expression, and the names of variables bound by pattern in order
-- they appear in constructor.
conPat :: NormalizedCon
        -> String
        -> Q (Pat, [Name])
conPat (NC nm a) pre = do
  nms <- replicateM (length a) (newName pre)
  return (ConP nm (VarP <$> nms), nms)


-- | Return an expression corresponding to the constructor.
-- Note that this will have the type of a function expecting
-- the argumetns given.
conExpr :: NormalizedCon -> Exp
conExpr c = ConE (nrmlConName c)

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
  let dec = maybe (Left "not a type constructor") Right
          $ asTyConI info
  case asDataD =<< dec of
    Left e   -> fail ("lookupDataType' " ++ show (ppr tpName) ++ ": " ++ e)
    Right dd -> return dd

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
      -> NormalizedCon
      -> [MatchQ]
mkEqF d pats (NC nm a) = (:[]) $ do
  let dVars = tyVarName <$> dataTyVarBndrs d
  let bnd | null dVars = Set.empty
          | otherwise  = Set.fromList (init dVars)
  mkSimpleEqF (VarT <$> dVars) bnd pats nm a

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
       -> NormalizedCon
       -> Q [MatchQ]
mkOrdF d pats (NC nm a) = mkSimpleOrdF (dataParamTypes d) pats nm a

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
                 -> NormalizedCon -- ^ Constructor to match.
                 -> MatchQ -- ^ Match expression that
traverseAppMatch pats fv c0 = do
  (pat,patArgs) <- conPat c0 "p"
  exprs <- zipWithM (recurseArg pats fv) (varE <$> patArgs) (nrmlConFields c0)

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

matchHashCtor :: ExpQ -> Integer  -> NormalizedCon -> MatchQ
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

matchShowCtor :: ExpQ -> NormalizedCon -> MatchQ
matchShowCtor p (NC nm tps) = showCon p nm (length tps)
