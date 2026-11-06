{-# LANGUAGE GADTs, DataKinds, TypeFamilies, StandaloneDeriving, PolyKinds #-}

module Environment where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Kind (Type)

import Syntax


------------------------
-- | ENVIRONMENTS
------------------------


-- map of typed values (logarithmic lookup and insertion)
-- redefining a key replaces its value; union keeps the left binding
newtype Env v = Env (Map.Map IdentKey (Exists v))

class Environment env where
  type Val env :: TType -> Type
  emptyEnv :: env
  find :: env -> Ident a -> (Val env) a
  maybeFind :: env -> Ident a -> Maybe ((Val env) a)
  define :: env -> Ident a -> (Val env) a -> env
  defArgs :: env -> [Exists Ident] -> [Exists (Val env)] -> env
  makeEnv :: [(Ident a, (Val env) a)] -> env
  union :: env -> env -> env
  envSize :: env -> Int

------------------------
-- | BIGRAPH MEMORY
------------------------

class MemoTable t where
  type LeftNode t
  type RightNode t
  type TruthValue t
  initMem :: t
  contents :: t -> (LeftNode t, RightNode t) -> Maybe (TruthValue t)
  update :: t -> (LeftNode t, RightNode t) -> TruthValue t -> t
  freshLeft :: t -> (LeftNode t, t)
  freshRight :: t -> (RightNode t, t)

newtype MemoBigraph l r b = Mem ((Set.Set l, Set.Set r), Map.Map (l, r) b)
  deriving (Show, Eq)

instance (Enum l, Ord l, Show l, Enum r, Ord r, Show r) => MemoTable (MemoBigraph l r b) where
  type LeftNode (MemoBigraph l r b) = l
  type RightNode (MemoBigraph l r b) = r
  type TruthValue (MemoBigraph l r b) = b
  initMem = Mem ((Set.empty, Set.empty), Map.empty)
  contents (Mem ((ls, rs), s)) (l,r) = do
    if Set.member l ls && Set.member r rs then
      Map.lookup (l, r) s
    else error $ "function " ++ show l ++
      " or atom " ++ show r ++ " not in bigraph"
  update (Mem ((ls, rs), s)) (l, r) v =
    if Set.member l ls && Set.member r rs then
      Mem ((ls, rs), Map.insert (l, r) v s)
    else error $ "function " ++ show l ++
      " or atom " ++ show r ++ " not in bigraph"
  freshLeft (Mem ((ls, rs), s)) = let n = toEnum (Set.size ls) in
    (n, Mem ((Set.insert n ls, rs), s))
  freshRight (Mem ((ls, rs), s)) = let m = toEnum (Set.size rs) in
    (m, Mem ((ls, Set.insert m rs), s))

deriving instance (Ord l, Ord r, Ord b) => Ord (MemoBigraph l r b)