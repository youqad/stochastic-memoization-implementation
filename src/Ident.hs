{-# LANGUAGE GADTs, DataKinds, PolyKinds, StandaloneDeriving, TypeOperators, RankNTypes, FlexibleInstances, UndecidableInstances, InstanceSigs #-}

module Ident where

import Data.Type.Equality
import Data.Kind (Type)

data TType =
  TBool
  | TAtom
  | TMemoFun
  | TProduct TType TType
  | TArrow [TType] TType
  deriving (Show, Eq, Ord)

-- singleton GADT trick for type-indexed witnesses, cf. https://homepages.inf.ed.ac.uk/slindley/papers/hasochism.pdf
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

-- source identifiers (Id) and evaluator temporaries (Gen, internal to the package)
data Ident :: TType -> Type where
  Id :: (String, Typey a) -> Ident a
  Gen :: (String, Typey a) -> Ident a

instance Show (Ident a) where
  show (Id (x, _)) = sourceText x
  show (Gen (x, _)) = '#' : x

sourceText :: String -> String
sourceText x@('#' : _) = '#' : x
sourceText x = x
deriving instance Eq (Ident a)

-- separate keys for source names and generated temporaries
data IdentKey = SourceIdent (String, TType) | GenIdent (String, TType)
  deriving (Eq, Ord, Show)

typeKey :: Typey a -> TType
typeKey 𝔹 = TBool
typeKey 𝔸 = TAtom
typeKey MemFn = TMemoFun
typeKey (Prod a b) = TProduct (typeKey a) (typeKey b)
typeKey (Arr a b) = TArrow [typeKey a] (typeKey b)

identKey :: Ident a -> IdentKey
identKey (Id (name, t)) = SourceIdent (name, typeKey t)
identKey (Gen (name, t)) = GenIdent (name, typeKey t)
