{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, GeneralizedNewtypeDeriving, StandaloneDeriving, DerivingVia, FlexibleInstances, TypeOperators, InstanceSigs #-}

module Syntax where

import qualified Data.List as List
import Data.Type.Equality
import Data.Kind (Type)
import Data.Function(on)
import Data.Maybe ( isJust, fromMaybe ) 

import Unsafe.Coerce (unsafeCoerce)

import Test.QuickCheck

-- import (<>) as PP.(<>) from Text.PrettyPrint

import Text.PrettyPrint


------------------------
-- | SYNTAX
------------------------

-- cf. https://stackoverflow.com/questions/28388715/list-of-any-datakind-in-gadt
--     https://stackoverflow.com/questions/69138268/using-gadts-with-datakinds-for-type-level-data-constructor-constraints-in-functi
data Exists :: (k -> Type) -> Type where
  This :: p x -> Exists p

deriving instance Show (Exists Expr)
deriving instance Show (Exists Ident)

-- data SomeExpr
--   where This :: Expr a -> SomeExpr

newtype AtmLabels = Atm Int deriving (Eq, Show, Ord, Enum)
newtype FnLabels = Fn Int deriving (Eq, Show, Ord, Enum)

data TType =
  TBool
  | TAtom
  | TMemoFun
  | TProduct TType TType
  | TArrow [TType] TType
  deriving (Show, Eq, Ord)

-- trick to implement dependent types using a singleton GADT, 
-- cf. https://homepages.inf.ed.ac.uk/slindley/papers/hasochism.pdf 
data Typey :: TType -> Type where
  𝔹 :: Typey 'TBool
  𝔸 :: Typey 'TAtom
  MemFn :: Typey 'TMemoFun
  Prod :: Typey a -> Typey b -> Typey ('TProduct a b)
  Arr :: Typey a -> Typey b -> Typey ('TArrow '[a] b)
deriving instance Show (Typey a)
deriving instance Eq (Typey a)


instance TestEquality Typey where
  testEquality :: Typey a -> Typey b -> Maybe (a :~: b)
  testEquality 𝔹 𝔹 = Just Refl
  testEquality 𝔸 𝔸 = Just Refl
  testEquality MemFn MemFn = Just Refl
  testEquality (Prod a b) (Prod c d) = do
    Refl <- testEquality a c
    Refl <- testEquality b d
    return Refl
  testEquality (Arr a b) (Arr c d) = do
    Refl <- testEquality a c
    Refl <- testEquality b d
    return Refl
  testEquality _ _ = Nothing

-- data TypedName :: Type -> TType -> Type where
--   TypedName :: a -> TypedName a b

data Ident :: TType -> Type where
  Id :: (String, Typey a) -> Ident a
-- data Ident :: TType -> Type where 
--   Id :: String -> Ident a

instance Show (Ident a) where
  show (Id (x, _)) = x
deriving instance Eq (Ident a)

data Expr :: TType -> Type where
  Atom :: AtmLabels -> Expr 'TAtom
  Bool :: Bool -> Expr 'TBool
  If :: Expr 'TBool -> Expr a -> Expr a -> Expr a
  Pair :: Expr a -> Expr b -> Expr ('TProduct a b)
  Match :: Expr ('TProduct a b) -> (Ident a, Ident b) -> Expr c -> Expr c
  Variable :: Ident a -> Expr a
  Lambda :: [Ident a] -> Expr b -> Expr ('TArrow '[a] b)
  Apply :: Expr ('TArrow '[a] b) -> [Expr a] -> Expr b
  MemoBernoulli :: Double -> Expr 'TMemoFun -- Expr (TArrow '[TAtom] TBool)
  MemoApply :: Expr 'TMemoFun -> Expr 'TAtom -> Expr 'TBool
  Eq  :: Expr a -> Expr a -> Expr 'TBool
  Let :: Defn a -> Expr b -> Expr b
  Sequence :: Expr a -> Expr b -> Expr b
  Fresh :: Expr 'TAtom
  Flip :: Expr 'TBool

instance Show (Expr a) where
  show = render . ppExpr
    where
    ppExpr :: Expr a -> Doc
    ppExpr (Atom a) = text $ show a
    ppExpr (Bool b) = text $ show b
    ppExpr (If e1 e2 e3) = text "If" <+> parens (ppExpr (unsafeCoerce e1)) <+> text "then" <+> parens (ppExpr e2) <+> text "else" <+> parens (ppExpr e3)
    ppExpr (Pair e1 e2) = text "Pair" <+> parens (ppExpr (unsafeCoerce e1) Text.PrettyPrint.<> text "," <+> ppExpr (unsafeCoerce e2))
    ppExpr (Match e (Id (x, _), Id (y, _)) e') = text "Match" <+> ppExpr (unsafeCoerce e) 
        <+> text "with" 
        <+> parens (text x Text.PrettyPrint.<> text "," <+> text y) 
        <+> text "->" 
        <+> parens (ppExpr e')
    ppExpr (Variable (Id (x, _))) = text x
    ppExpr (Lambda [] e) = ppExpr (unsafeCoerce e)
    ppExpr (Lambda (Id (x, _):xs) e) = parens (text "λ" Text.PrettyPrint.<> text x Text.PrettyPrint.<> text "." <+> ppExpr (Lambda xs e))
    ppExpr (Apply e1 e2) = ppExpr (unsafeCoerce e1) <+> text "`Apply`" <+> brackets (hsep (map ppExpr (unsafeCoerce e2)))
    ppExpr (MemoBernoulli p) = text "MemoBernoulli" <+> text (show p)
    ppExpr (MemoApply e1 e2) = ppExpr (unsafeCoerce e1) <+> text "`MemoApply`" <+> parens (ppExpr (unsafeCoerce e2))
    ppExpr (Eq e1 e2) = parens (ppExpr (unsafeCoerce e1)) <+> text "==" <+> parens (ppExpr (unsafeCoerce e2))
    ppExpr (Let d e) = text "Let" <+> parens (ppDefn (unsafeCoerce d)) <+> text "in" <+> ppExpr e
    ppExpr (Sequence e1 e2) = ppExpr (unsafeCoerce e1) Text.PrettyPrint.<> semi <+> ppExpr e2
    ppExpr Fresh = text "Fresh"
    ppExpr Flip = text "Flip"

    ppDefn :: Defn a -> Doc
    ppDefn (Val (Id (x, _)) e) = text x <+> text ":=" <+> ppExpr e

    
instance Eq (Expr a) where
  (==) = (==) `on` show
instance Ord (Expr a) where
  compare = compare `on` show

instance Arbitrary (Exists Expr) where 
  arbitrary :: Gen (Exists Expr)
  arbitrary = sized $ arbExpr [] Nothing
    where
    arbExpr :: [Exists Ident] -> Maybe (Typey a) -> Int -> Gen (Exists Expr)
    arbExpr listVars t 0 = oneof $ listOfPossibilitiesBase listVars t
    arbExpr ls t n = do
      case t of
        Just 𝔹 -> oneof $ listOfPossibilitiesContext ls t n 
          ++ listOfPossibilitiesBase ls t
          ++ [
            do -- Eq construct
              This t' <- elements [This 𝔸, This 𝔹]
              This this1 <- arbExpr ls (Just t') (n `div` 2)
              This this2 <- arbExpr ls (Just t') (n `div` 2)
              return $ This $ Eq this1 (unsafeCoerce this2)
          , do -- MemoApply construct
              This this1 <- arbExpr ls (Just MemFn) (n `div` 2)
              This this2 <- arbExpr ls (Just 𝔸) (n `div` 2)
              return $ This $ MemoApply (unsafeCoerce this1) (unsafeCoerce this2)
          ]
        Just 𝔸 -> oneof $ listOfPossibilitiesContext ls t n 
          ++ listOfPossibilitiesBase ls t
        Just MemFn -> oneof $ listOfPossibilitiesContext ls t n
          ++ listOfPossibilitiesBase ls t
        Just (Prod a b) -> oneof $ listOfPossibilitiesContext ls t n
          ++ listOfPossibilitiesBase ls t
          ++ [
            do
              This this1 <- arbExpr ls (Just a) (n `div` 2)
              This this2 <- arbExpr ls (Just b) (n `div` 2)
              return $ This $ Pair this1 (unsafeCoerce this2)
            ]
        Just (Arr a b) -> oneof $ listOfPossibilitiesContext ls t n
          ++ listOfPossibilitiesBase ls t
          ++ [do
                let s1 = "x_" ++ show (List.length ls + 1)
                This this2 <- arbExpr (This (Id (s1, a)):ls) (Just b) (n `div` 2)
                return $ This $ Lambda [Id (s1, a)] (unsafeCoerce this2)
              ]
        Nothing -> oneof $ listOfPossibilitiesContext ls t n
          ++ listOfPossibilitiesBase ls t
          ++ [
            do
              This t' <- elements [This 𝔸, This 𝔹]
              This this1 <- arbExpr ls (Just t') (n `div` 2)
              This this2 <- arbExpr ls (Just t') (n `div` 2)
              return $ This $ Eq this1 (unsafeCoerce this2)
          , do -- MemoApply construct
              This this1 <- arbExpr ls (Just MemFn) (n `div` 2)
              This this2 <- arbExpr ls (Just 𝔸) (n `div` 2)
              return $ This $ MemoApply (unsafeCoerce this1) (unsafeCoerce this2)
          , do
              let s1 = "x_" ++ show (List.length ls + 1)
              This this2 <- arbExpr (This (Id (s1, 𝔸)):ls) (Just 𝔹) (n `div` 2)
              return $ This $ Lambda [Id (s1, 𝔸)] (unsafeCoerce this2)
          , do
              This this1 <- arbExpr ls (Just 𝔸) (n `div` 2)
              This this2 <- arbExpr ls (Just 𝔸) (n `div` 2)
              return $ This $ Pair this1 (unsafeCoerce this2)
          ]
    listOfPossibilitiesBase :: [Exists Ident] -> Maybe (Typey a) -> [Gen (Exists Expr)]
    listOfPossibilitiesBase listVariables t = case t of
        Just 𝔹 -> return (This Flip) :
          [return $ This (Variable (Id (s', t'))) | (This (Id (s', t'))) <- listVariables, isJust (testEquality t' 𝔹)]
        Just 𝔸 -> return (This Fresh) :
          [return $ This (Variable (Id (s', t'))) | (This (Id (s', t'))) <- listVariables, isJust (testEquality t' 𝔸)]
        Just MemFn -> (This . MemoBernoulli . round' 3 <$> choose (0, 1)) :
          [return $ This (Variable (Id (s', t'))) | (This (Id (s', t'))) <- listVariables, isJust (testEquality t' MemFn)]
        Just t0 -> 
          let resList = [return $ This (Variable (Id (s', t'))) | (This (Id (s', t'))) <- listVariables, isJust (testEquality t' t0)] in
          case resList of
            [] -> case t0 of
              Prod a b -> [do
                  This this1 <- arbExpr listVariables (Just a) 0
                  This this2 <- arbExpr listVariables (Just b) 0
                  return $ This $ Pair this1 this2
                ]
              Arr a b -> [do
                  let s1 = "x_" ++ show (List.length listVariables + 1)
                  This this2 <- arbExpr (This (Id (s1, a)):listVariables) (Just b) 0
                  return $ This $ Lambda [Id (s1, a)] (unsafeCoerce this2)
                ]
            _ -> resList
        Nothing -> [return $ This Fresh, return $ This Flip
          , This . MemoBernoulli . round' 3 <$> choose (0, 1)]
          ++ [return $ This (Variable (Id (s', t'))) | (This (Id (s', t'))) <- listVariables]
    listOfPossibilitiesContext :: [Exists Ident] -> Maybe (Typey a) -> Int -> [Gen (Exists Expr)]
    listOfPossibilitiesContext ls t n = 
      let baseTypes = [This 𝔸, This 𝔹, This MemFn, This (Arr 𝔸 𝔸), This (Arr 𝔸 𝔹), This (Arr 𝔹 𝔸), This (Arr 𝔹 𝔹)] in
        [ do -- If construct
            This t1 <- case t of
              Nothing -> elements baseTypes
              Just t' -> return $ This t'
            This this0 <- arbExpr ls (Just 𝔹) (n `div` 2)
            This this1 <- arbExpr ls (Just t1) (n `div` 2)
            This this2 <- arbExpr ls (Just t1) (n `div` 2)
            return $ This $ If (unsafeCoerce this0) this1 (unsafeCoerce this2)
        , do -- Match construct
            let s1 = "x_" ++ show (List.length ls + 1)
            let s2 = "x_" ++ show (List.length ls + 2)
            This t1 <- elements baseTypes
            This t2 <- elements baseTypes
            let ls' = This (Id (s1, t1)):This (Id (s2, t2)):ls
            This this1 <- arbExpr ls (Just t1) (n `div` 2)
            This this2 <- arbExpr ls (Just t2) (n `div` 2)
            This this3 <- arbExpr ls' t (n `div` 2)
            return $ This $ Match (Pair this1 this2) (Id (s1, unsafeCoerce t1), Id (s2, unsafeCoerce t2)) (unsafeCoerce this3)
        , do -- Apply construct
            This t1 <- elements baseTypes
            This t2 <- elements baseTypes
            let t0 = fromMaybe t2 (unsafeCoerce t)
            This this1 <- arbExpr ls (Just (Arr t1 t0)) (n `div` 2)
            This this2 <- arbExpr ls (Just t1) (n `div` 2)
            return $ This $ Apply (unsafeCoerce this1) [this2]
        , do -- Let construct
            let s1 = "x_" ++ show (List.length ls + 1)
            This t1 <- elements baseTypes
            let ls' = This (Id (s1, t1)) : ls
            This this1 <- arbExpr ls (Just t1) (n `div` 2)
            This this2 <- arbExpr ls' t (n `div` 2)
            return $ This $ Let (Val (Id (s1, unsafeCoerce t1)) (unsafeCoerce this1)) (unsafeCoerce this2)
        -- , do -- Sequence construct
        --     This t1 <- elements baseTypes
        --     This this1 <- arbExpr ls (Just t1) (n `div` 2)
        --     This this2 <- arbExpr ls t (n `div` 2)
        --     return $ This $ Sequence (unsafeCoerce this1) (unsafeCoerce this2)
        ]
    round' :: Int -> Double -> Double
    round' prec num = ((fromIntegral :: Integer -> Double). round 
        $ num * f) / f
      where f = 10^prec

data Defn a =
    Val (Ident a) (Expr a)
  deriving (Eq, Show)


