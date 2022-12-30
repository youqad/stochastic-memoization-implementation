{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, GeneralizedNewtypeDeriving, StandaloneDeriving, DerivingVia, FlexibleInstances, TypeOperators, InstanceSigs #-}

module Syntax where

import Data.Char(isAlpha)
import qualified Data.List as List
import Data.Type.Equality
import Data.Function(on)

------------------------
-- | SYNTAX
------------------------

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
  𝔹 :: Typey TBool
  𝔸 :: Typey TAtom
  MemFn :: Typey TMemoFun
  Prod :: Typey a -> Typey b -> Typey (TProduct a b)
  Arr :: Typey a -> Typey b -> Typey (TArrow '[a] b)
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
  Atom :: AtmLabels -> Expr TAtom
  Bool :: Bool -> Expr TBool
  If :: Expr TBool -> Expr a -> Expr a -> Expr a
  Pair :: Expr a -> Expr b -> Expr (TProduct a b)
  Match :: Expr (TProduct a b) -> (Ident a, Ident b) -> Expr c -> Expr c
  Variable :: Ident a -> Expr a
  Lambda :: [Ident a] -> Expr b -> Expr (TArrow '[a] b)
  Apply :: Expr (TArrow '[a] b) -> [Expr a] -> Expr b
  MemoBernoulli :: Double -> Expr TMemoFun -- Expr (TArrow '[TAtom] TBool)
  MemoApply :: Expr TMemoFun -> Expr TAtom -> Expr TBool
  Eq  :: Expr a -> Expr a -> Expr TBool
  Let :: Defn a -> Expr b -> Expr b
  Sequence :: Expr a -> Expr b -> Expr b
  Fresh :: Expr TAtom
  Flip :: Expr TBool

instance Show (Expr a) where
  show = prettyPrint
instance Eq (Expr a) where
  (==) = (==) `on` prettyPrint
instance Ord (Expr a) where
  compare = compare `on` prettyPrint

data Defn a =
    Val (Ident a) (Expr a)
-- instance Show (Defn a) where
--   show (Val (Ident x) e) = show x ++ " := " ++ show e

-- pretty-print an expression with ellipses
prettyPrint :: Expr a -> String
prettyPrint exp = pp 8 1000 exp ""
  where
    pp :: Int -> Int -> Expr a -> ShowS
    pp p d (Atom n) = showString ("<atom " ++ show n ++ ">")
    pp p d (Bool b) = showString (show b)
    pp p d (Variable x) = showName x
    pp p 0 _ = showString "..."
    pp p d (Let def body) =
      showParen (p < 8)
        (showString "let " . pp_def d def
          . showString " in " . pp 8 (d-1) body)
    pp p d (Match e1 e2 e3) =
      showParen (p < 8)
        (showString "match " . pp 8 (d-1) e1 . showString " with "
          . showString " (" .
          showName (fst e2) . showString ", " . showName (snd e2) .
          showString ") else " . pp 8 (d-1) e3)
    pp p d (Lambda fps body) =
      showParen (p < 8)
        (showString "λ (" . pp_list showName fps . showString ") "
          . pp 8 (d-1) body)
    pp p d (MemoBernoulli θ) =
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
    pp p d Flip =
      showParen (p < 2)
        (showString "flip()")
    pp p d Fresh =
      showParen (p < 2)
        (showString "fresh()")
    showName (Id (x, _) :: Ident a) =
      if isAlpha (head x) then showString x
      else showString "(" . showString x . showString ")"
    pp_def :: Int -> Defn a -> ShowS
    pp_def d (Val x e) =
      showName x . showString " = " . pp 8 (d-1) e
    pp_list :: (a -> ShowS) -> [a] -> ShowS
    pp_list p = foldr (.) id . List.intersperse (showString ", ") . map p


