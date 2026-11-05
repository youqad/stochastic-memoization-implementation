{-# LANGUAGE GADTs, DataKinds, PolyKinds, StandaloneDeriving, TypeFamilies, ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor, GeneralizedNewtypeDeriving #-}

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

deriving instance Show (Exists Value)

type EnvVal = Env Value

instance Environment EnvVal where
  type Val EnvVal = Value
  emptyEnv = Env Map.empty
  find env x = case maybeFind env x of
    Just v -> v
    Nothing -> error $ show x ++ " not found in environment"
  maybeFind (Env m) (Id (s, tx)) = case Map.lookup (s, typeKey tx) m of
    Just (This v) -> case testEquality tx (typeFromVal v) of
      Just Refl -> Just v
      Nothing -> Nothing
    Nothing -> Nothing
  define (Env m) x v = Env (Map.insert (identKey x) (This v) m)
  defArgs env fps args
    | List.length fps /= List.length args = error $
        "defArgs: arity mismatch: " ++ show (List.length fps)
        ++ " parameters but " ++ show (List.length args) ++ " arguments"
    | otherwise = Env (foldr insertArg Map.empty (zip fps args)) `union` env
    where
      insertArg :: (Exists Ident, Exists Value)
        -> Map.Map (String, TType) (Exists Value)
        -> Map.Map (String, TType) (Exists Value)
      insertArg (This ident, This v) m =
        case testEquality (typeFromIdent ident) (typeFromVal v) of
          Just Refl -> Map.insert (identKey ident) (This v) m
          Nothing -> error $
            "defArgs: type mismatch for " ++ show ident ++ ": expected "
            ++ show (typeKey (typeFromIdent ident))
            ++ " but got " ++ show (typeKey (typeFromVal v))
  makeEnv defs = Env (Map.fromList (map (\(x, v) -> (identKey x, This v)) defs))
  union (Env m1) (Env m2) = Env (Map.union m1 m2)
  envSize (Env m) = Map.size m

deriving instance Show EnvVal
instance Eq EnvVal where
  (Env m1) == (Env m2) = m1 == m2
instance Ord EnvVal where
  compare (Env m1) (Env m2) = compare m1 m2
instance Eq (Exists Value) where
  (This (a :: Value a)) == (This (b :: Value b)) =
    case testEquality (typeFromVal a) (typeFromVal b) of
      Just Refl -> a == b
      Nothing -> False
instance Ord (Exists Value) where
  compare (This (a :: Value a)) (This (b :: Value b)) =
    case testEquality (typeFromVal a) (typeFromVal b) of
      Just Refl -> compare a b
      Nothing -> compare (typeKey (typeFromVal a)) (typeKey (typeFromVal b))

initEnv :: EnvVal
initEnv = emptyEnv

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
