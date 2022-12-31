{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, GeneralizedNewtypeDeriving, StandaloneDeriving, DerivingVia, FlexibleInstances, TypeOperators, InstanceSigs #-}

module Syntax where

import Data.Char(isAlpha)
import qualified Data.List as List
import Data.Type.Equality
import Data.Function(on)
import Data.Maybe ( isJust, fromMaybe ) 

import Unsafe.Coerce (unsafeCoerce)

import Test.QuickCheck

------------------------
-- | SYNTAX
------------------------

-- cf. https://stackoverflow.com/questions/28388715/list-of-any-datakind-in-gadt
--     https://stackoverflow.com/questions/69138268/using-gadts-with-datakinds-for-type-level-data-constructor-constraints-in-functi
data Exists :: (k -> *) -> * where
  This :: p x -> Exists p

deriving instance Show (Exists Expr)
deriving instance Show (Exists Ident)

-- data SomeExpr
--   where This :: Expr a -> SomeExpr

newtype AtmLabels = Atm Int deriving (Eq, Show, Ord, Enum)
newtype FnLabels = Fn Int deriving (Eq, Show, Ord, Enum)

data Type =
  TBool
  | TAtom
  | TMemoFun
  | TProduct Type Type
  | TArrow [Type] Type
  deriving (Show, Eq, Ord)

-- trick to implement dependent types using a singleton GADT, 
-- cf. https://homepages.inf.ed.ac.uk/slindley/papers/hasochism.pdf 
data Typey :: Type -> * where
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

-- data TypedName :: * -> Type -> * where
--   TypedName :: a -> TypedName a b

data Ident :: Type -> * where
  Id :: (String, Typey a) -> Ident a
-- data Ident :: Type -> * where 
--   Id :: String -> Ident a

instance Show (Ident a) where
  show (Id (x, _)) = x
deriving instance Eq (Ident a)

data Expr :: Type -> * where
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
  show = prettyPrint
instance Eq (Expr a) where
  (==) = (==) `on` prettyPrint
instance Ord (Expr a) where
  compare = compare `on` prettyPrint

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
          ++ [do
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
          ++ [do
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
          ++ [do
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
    listOfPossibilitiesBase listVariables t = case t of
        Just 𝔹 -> return (This Flip) :
          [return $ This (Variable (Id (s', t'))) | (This (Id (s', t'))) <- listVariables, isJust (testEquality t' 𝔹)]
        Just 𝔸 -> return (This Fresh) :
          [return $ This (Variable (Id (s', t'))) | (This (Id (s', t'))) <- listVariables, isJust (testEquality t' 𝔸)]
        Just MemFn -> (This . MemoBernoulli <$> choose (0, 1)) :
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
          , This . MemoBernoulli <$> choose (0, 1)]
          ++ [return $ This (Variable (Id (s', t'))) | (This (Id (s', t'))) <- listVariables]
    listOfPossibilitiesContext ls t n = 
      [
        do -- If construct
            This this0 <- arbExpr ls (Just 𝔹) (n `div` 2)
            This this1 <- arbExpr ls t (n `div` 2)
            This this2 <- arbExpr ls t (n `div` 2)
            return $ This $ If (unsafeCoerce this0) this1 (unsafeCoerce this2)
        , do -- Match construct
            let s1 = "x_" ++ show (List.length ls + 1)
            let s2 = "x_" ++ show (List.length ls + 2)
            This t1 <- elements [This 𝔸, This 𝔹]
            This t2 <- elements [This 𝔸, This 𝔹]
            This this1 <- arbExpr ls (Just t1) (n `div` 2)
            This this2 <- arbExpr ls (Just t2) (n `div` 2)
            This this3 <- arbExpr ([This (Id (s1, t1)), This (Id (s2, t2))] ++ ls) t (n `div` 2)
            return $ This $ Match (Pair this1 this2) (Id (s1, unsafeCoerce t1), Id (s2, unsafeCoerce t2)) (unsafeCoerce this3)
        , do -- Apply construct
            This t1 <- elements [This 𝔸, This 𝔹]
            This t2 <- elements [This 𝔸, This 𝔹]
            let t0 = fromMaybe t2 (unsafeCoerce t)
            This this1 <- arbExpr ls (Just (Arr t1 t0)) (n `div` 2)
            This this2 <- arbExpr ls (Just t1) (n `div` 2)
            return $ This $ Apply (unsafeCoerce this1) [this2]
        , do -- Let construct
            let s1 = "x_" ++ show (List.length ls + 1)
            This t1 <- elements [This 𝔸, This 𝔹]
            This this1 <- arbExpr ls (Just t1) (n `div` 2)
            This this2 <- arbExpr (This (Id (s1, t1)) : ls) t (n `div` 2)
            return $ This $ Let (Val (Id (s1, unsafeCoerce t1)) (unsafeCoerce this1)) (unsafeCoerce this2)
        -- , do -- Sequence construct
        --     This t1 <- elements [This 𝔸, This 𝔹]
        --     This this1 <- arbExpr ls (Just t1) (n `div` 2)
        --     This this2 <- arbExpr ls t (n `div` 2)
        --     return $ This $ Sequence (unsafeCoerce this1) (unsafeCoerce this2)
        ]

data Defn a =
    Val (Ident a) (Expr a)

-- pretty-print an expression with ellipses
prettyPrint :: Expr a -> String
prettyPrint exp = pp 8 1000 exp ""
  where
    pp :: Int -> Int -> Expr a -> ShowS
    pp _ _ (Atom n) = showString ("<atom " ++ show n ++ ">")
    pp _ _ (Bool b) = showString (show b)
    pp _ _ (Variable x) = showName x
    pp _ 0 _ = showString "..."
    pp p d (Let def body) =
      showParen (p < 8)
        (showString "let " . pp_def d def
          . showString " in " . pp 8 (d-1) body)
    pp p d (Match e1 e2 e3) =
      showParen (p < 8)
        (showString "match " . pp 8 (d-1) e1 . showString " with "
          . showString " (" .
          showName (fst e2) . showString ", " . showName (snd e2) .
          showString ") in " . pp 8 (d-1) e3)
    pp p d (Lambda fps body) =
      showParen (p < 8)
        (showString "λ (" . pp_list showName fps . showString ") "
          . pp 8 (d-1) body)
    pp p _ (MemoBernoulli θ) =
      showParen (p < 8)
        (showString "memoBernoulli(" . showString (show θ) . showString ")")
    pp p d (Sequence e1 e2) =
      showParen (p < 8)
        (pp 7 d e1 . showString "; " . pp 7 (d-1) e2)
    pp p d (If e1 e2 e3) =
      showParen (p < 7)
        (showString "if " . pp 7 (d-1) e1 . showString " then "
          . pp 7 (d-1) e2 . showString " else " . pp 7 (d-1) e3)
    pp p d (Eq e1 e2) =
      showParen (p < 4)
        (pp 3 (d-1) e1 . showString " == " . pp 4 (d-1) e2)
    pp p d (Pair e1 e2) =
      showParen (p < 2)
        (pp 2 d e1 . showString ", " . pp 2 (d-1) e2)
    pp p d (Apply f aps) =
      showParen (p < 2)
        (pp 2 d f . showString "(" . pp_list (pp 8 (d-1)) aps . showString ")")
    pp p d (MemoApply f aps) =
      showParen (p < 2)
        (pp 2 d f . showString "@(" . pp 8 (d-1) aps . showString ")")
    pp p _ Flip =
      showParen (p < 2)
        (showString "flip()")
    pp p _ Fresh =
      showParen (p < 2)
        (showString "fresh()")
    showName (Id (x, _) :: Ident a) =
      if isAlpha (head x) then showString x
      else showString "(" . showString x . showString ")"
    pp_def :: Int -> Defn a -> ShowS
    pp_def d (Val x e) =
      showName x . showString " := " . pp 8 (d-1) e
    pp_list :: (a -> ShowS) -> [a] -> ShowS
    pp_list p = foldr (.) id . List.intersperse (showString ", ") . map p


