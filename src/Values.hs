{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, DeriveFunctor, GeneralizedNewtypeDeriving, StandaloneDeriving, DerivingVia, FlexibleInstances #-}

module Values where

import qualified Data.Map as Map
import qualified Data.List as List

import Data.Kind (Type)
import Data.Type.Equality
-- import Data.Function(on)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State

import Syntax
import Environment

------------------------
-- | MONADS
------------------------

type Dist = Dist.T Double

data StateOfBiases t = MemoTable t => S (Map.Map (LeftNode t) Double)

deriving instance Eq (LeftNode t) => Eq (StateOfBiases t)
deriving instance Ord (LeftNode t) => Ord (StateOfBiases t)
deriving instance (Show (LeftNode t), Show (RightNode t), Show (TruthValue t)) => Show (StateOfBiases t)

newtype 𝕋 state x = T (State.StateT state Dist x)
  deriving (Functor, Applicative, Monad)

-- type MemOp = MemoBigraph Closures AtmLabels Bool
type MemDen = MemoBigraph FnLabels AtmLabels Bool

-- type TOp = 𝕋 MemOp
type T = 𝕋 (MemDen, StateOfBiases MemDen)

------------------------
-- | VALUES
------------------------

data Value :: TType -> Type where
  AtomVal :: AtmLabels -> Value 'TAtom
  BoolVal :: Bool -> Value 'TBool
  Function :: (Value a -> T (Value b)) 
    -> Expr ('TArrow '[a] b)
    -> (EnvVal, EnvVal)
    -> Typey ('TArrow '[a] b) 
    -> Value ('TArrow '[a] b)
  MemoFunction :: FnLabels -> Value 'TMemoFun
  PairVal :: Value a -> Value b -> Typey ('TProduct a b) -> Value ('TProduct a b)

instance Eq (Value a) where
  (AtomVal a) == (AtomVal b) = a == b
  (BoolVal a) == (BoolVal b) = a == b
  (Function _ e _ _) == (Function _ e' _ _) = e == e'
  (MemoFunction a) == (MemoFunction b) = a == b
  (PairVal a b _) == (PairVal c d _) = a == c && b == d

instance Ord (Value a) where
  compare (AtomVal a) (AtomVal b) = compare a b
  compare (BoolVal a) (BoolVal b) = compare a b
  compare (Function _ e _ _) (Function _ e' _ _) = compare e e'
  compare (MemoFunction a) (MemoFunction b) = compare a b
  compare (PairVal a b _) (PairVal c d _) =
    case compare a c of
      EQ -> compare b d
      ordering -> ordering
instance Show (Value a) where
  show (AtomVal (Atm a)) = "<atom ++" ++ show a ++ ">"
  show (BoolVal b) = show b
  show (Function _ e _ _) = show e
  show (MemoFunction a) = "<memoized function ++" ++ show a ++ ">"
  show (PairVal a b _) = "(" ++ show a ++ ", " ++ show b ++ ")"

deriving instance Show (Exists (IdentVal Value))
deriving instance Show (Exists Value)

type EnvVal = Env Value

instance Environment EnvVal where
  type Val EnvVal = Value
  emptyEnv = Env []
  find (Env m) x@(Id (s, tx)) = case m of
    (This (IdentVal (Id (s', ty), v))):ms -> case testEquality tx ty of
      Just Refl -> if s == s' then v else find (Env ms) x
      Nothing -> find (Env ms) x
    [] -> error $ show x ++ " not found in environment"
  maybeFind (Env m) x@(Id (s, tx)) = case m of
    (This (IdentVal (Id (s', ty), v))):ms -> case testEquality tx ty of
      Just Refl -> if s == s' then Just v else maybeFind (Env ms) x
      Nothing -> maybeFind (Env ms) x
    [] -> Nothing
  define (Env m) x v = Env (This (IdentVal (x, v)):m)
  defArgs env fps args =
    Env (zipWith (\(This (Id (x, tx))) (This v) ->
              case testEquality tx (typeFromVal v) of
                Just Refl -> This (IdentVal (Id (x, tx), v))
                Nothing -> error "wrong type")
        fps args) `union` env
  makeEnv defs = Env (map (This . IdentVal) defs)
  -- names (Env m) = Map.keys m
  union (Env m1) (Env m2) = Env (m1 ++ m2)
  length (Env m) = List.length m

deriving instance Show EnvVal
instance Eq EnvVal where
  (Env m1) == (Env m2) = m1 == m2
instance Ord EnvVal where
  compare (Env m1) (Env m2) = compare m1 m2
instance Eq (Exists (IdentVal Value)) where
  (This (IdentVal (Id (s1, _), _))) == (This (IdentVal (Id (s2, _), _))) = s1 == s2
instance Ord (Exists (IdentVal Value)) where
  compare (This (IdentVal (Id (s1, _), _))) (This (IdentVal (Id (s2, _), _))) = compare s1 s2

initEnv :: EnvVal
initEnv = makeEnv []

typeFromVal :: Value a -> Typey a
typeFromVal (AtomVal _) = 𝔸
typeFromVal (BoolVal _) = 𝔹
typeFromVal (Function _ _ _ t) = t
typeFromVal (MemoFunction _) = MemFn
typeFromVal (PairVal _ _ t) = t

typeFromIdent :: Ident a -> Typey a
typeFromIdent (Id (_, t)) = t

typeFromExpr :: Expr a -> Typey a
typeFromExpr (Atom _) = 𝔸
typeFromExpr (Bool _) = 𝔹
typeFromExpr (If _ e _) = typeFromExpr e
typeFromExpr (Pair e1 e2) = Prod (typeFromExpr e1) (typeFromExpr e2)
typeFromExpr (Match _ _ e) = typeFromExpr e
typeFromExpr (Variable (Id (_, t))) = t
typeFromExpr (Lambda x e) = Arr (typeFromIdent x) (typeFromExpr e)
typeFromExpr (Apply e _) = case typeFromExpr e of
  Arr _ t -> t
typeFromExpr (MemoBernoulli _) = MemFn
typeFromExpr (MemoApply _ _) = 𝔹
typeFromExpr (Eq _ _) = 𝔹
typeFromExpr (Let _ e) = typeFromExpr e
typeFromExpr (Sequence _ e) = typeFromExpr e
typeFromExpr Fresh = 𝔸
typeFromExpr Flip = 𝔹
