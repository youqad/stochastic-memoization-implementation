{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, DerivingVia, FlexibleInstances #-}

module Main where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe (fromJust)
import Control.Monad (forM_, forM, foldM)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State
-- import qualified Control.Monad.Trans.State.Strict as State
-- import Debug.Trace (trace)

import Syntax
import Environment
import Values

------------------------
-- | SEMANTICS
------------------------

-- | Big-Step Operational Semantics

getOpSem :: (FnLabels, AtmLabels) -> T Bool
getOpSem (l, r) = T $ do
  (g, S λ) <- State.get
  case contents g (l, r) of
    Just b -> return b
    Nothing -> do
      let θ = λ Map.! l
      b <- State.lift $ bernoulli θ
      State.put (update g (l, r) b, S λ)
      return b

freshAtmOpSem :: T AtmLabels
freshAtmOpSem = T $ do
  (g, sλ) <- State.get
  let (r, g') = freshRight g
  State.put (g', sλ)
  return r

freshFnOpSem :: Double -> T FnLabels
freshFnOpSem θ = T $ do
  (g, S λ) <- State.get
  let (l, g') = freshLeft g
  let λ' = Map.insert l θ λ
  State.put (g', S λ')
  return l


bigStep :: Expr a -> EnvVal -> T (Value a)
bigStep (Atom a) _ = return $ AtomVal a
bigStep (Bool b) _ = return $ BoolVal b
bigStep (If e1 e2 e3) env = do
  b <- bigStep e1 env
  case b of
    BoolVal True -> bigStep e2 env
    BoolVal False -> bigStep e3 env
bigStep (Pair e1 e2) env = do
  v1 <- bigStep e1 env
  v2 <- bigStep e2 env
  return $ PairVal v1 v2 $ Prod (typeFromVal v1) (typeFromVal v2)
bigStep (Match e1 (x1, x2) e2) env = do
  v <- bigStep e1 env
  case v of
    PairVal v1 v2 _ -> bigStep e2 $ defArgs env fps args
      where
        fps = [This x1, This x2]
        args = [This v1, This v2]
bigStep (Variable x) env = return $ find env x
bigStep (Lambda xs e1) env = do
  return $ Function
      -- (bigStep e1 . defArgs env (map This xs) . map This)
      (\arg -> bigStep e1 $ defArgs env (map This xs) [This arg])
      (Lambda xs e1)
      $ typeFromExpr (Lambda xs e1)
bigStep (Apply f es) env = do
  fv <- bigStep f env
  vs <- forM es $ \e -> bigStep e env
  case (fv, vs) of
    (Function f' _ _, _) -> f' (head vs)
bigStep (MemoBernoulli θ) _ = do
  f <- freshFnOpSem θ
  return $ MemoFunction f
bigStep (MemoApply f e) env = do
  fv <- bigStep f env
  v <- bigStep e env
  case (fv, v) of
    (MemoFunction f', AtomVal a) -> BoolVal <$> getOpSem (f', a)
bigStep (Eq e1 e2) env = do
  v1 <- bigStep e1 env
  v2 <- bigStep e2 env
  return $ BoolVal (v1 == v2)
bigStep Fresh _ = AtomVal <$> freshAtmOpSem
bigStep Flip _ = T $ State.lift $ BoolVal <$> bernoulli 0.5
bigStep (Let (Val x e) e1) env = do
  env' <- define env x <$> bigStep e env
  bigStep e1 env'
bigStep (Sequence e1 e2) env =
  bigStep e1 env >> bigStep e2 env

completeBigraph :: T ()
completeBigraph = do
  (Mem((ls, rs), _), _) <- T State.get
  forM_
    [(l, r) | l <- Set.toList ls, r <- Set.toList rs]
    getOpSem

bigStepComplete :: Expr a -> EnvVal -> T (Value a)
bigStepComplete e env = do
  v <- bigStep e env
  completeBigraph
  return v

-- | Small-Step Operational Semantics

type ExprOrValue a = Either (Expr a) (Value a)

smallStep :: Expr a -> EnvVal -> T (ExprOrValue a)
smallStep (Atom a) _ = return $ Right $ AtomVal a
smallStep (Bool b) _ = return $ Right $ BoolVal b
smallStep (If e1 e2 e3) env = do
  e1' <- smallStep e1 env
  case e1' of
    Left e1'' -> return $ Left $ If e1'' e2 e3
    Right (BoolVal True) -> return $ Left e2
    Right (BoolVal False) -> return $ Left e3
smallStep (Pair e1 e2) env = do
  e1' <- smallStep e1 env
  case e1' of
    Left e1'' -> return $ Left $ Pair e1'' e2
    Right v1 -> do
      e2' <- smallStep e2 env
      case e2' of
        Left e2'' -> return $ Left $ Pair e1 e2''
        Right v2 -> return $ Right $ PairVal v1 v2 $
          Prod (typeFromVal v1) (typeFromVal v2)
smallStep (Match e1 (x1, x2) e2) env = do
  e1' <- smallStep e1 env
  case e1' of
    Left e1'' -> return $ Left $ Match e1'' (x1, x2) e2
    Right (PairVal v1 v2 _) ->
      Left <$> subst e2 [This (IdentVal (x1, v1)), This (IdentVal (x2, v2))]
smallStep (Variable x) env = return $ Right $ find env x
smallStep (Lambda xs e1) env = do
  return $ Right $ Function
      (\arg -> bigStep e1 $ defArgs env (map This xs) [This arg])
      (Lambda xs e1)
      $ typeFromExpr (Lambda xs e1)
smallStep (Apply f es) env = do
  f' <- smallStep f env
  case f' of
    Left f'' -> return $ Left $ Apply f'' es
    Right (Function f'' _ _) -> do
      es' <- forM es $ \e -> smallStep e env
      case sequence es' of
        Left es'' -> return $ Left $ Apply f [es'']
        Right vs -> Right <$> f'' (head vs)
smallStep (MemoBernoulli θ) _ = do
  f <- freshFnOpSem θ
  return $ Right $ MemoFunction f
smallStep (MemoApply f e) env = do
  f' <- smallStep f env
  case f' of
    Left f'' -> return $ Left $ MemoApply f'' e
    Right (MemoFunction f'') -> do
      e' <- smallStep e env
      case e' of
        Left e'' -> return $ Left $ MemoApply f e''
        Right (AtomVal a) -> Right . BoolVal <$> getOpSem (f'', a)
smallStep (Let (Val x e) e1) env = do
  e' <- smallStep e env
  case e' of
    Left e'' -> return $ Left $ Let (Val x e'') e1
    Right v -> Left <$> subst e1 [This (IdentVal (x, v))]
smallStep (Sequence e1 e2) env = do
  e1' <- smallStep e1 env
  case e1' of
    Left e1'' -> return $ Left $ Sequence e1'' e2
    Right _ -> return $ Left e2
smallStep Fresh _ = do
  Right . AtomVal <$> freshAtmOpSem
smallStep Flip _ = do
  T $ State.lift $ Right . BoolVal <$> bernoulli 0.5
smallStep (Eq e1 e2) env = do
  e1' <- smallStep e1 env
  case e1' of
    Left e1'' -> return $ Left $ Eq e1'' e2
    Right v1 -> do
      e2' <- smallStep e2 env
      case e2' of
        Left e2'' -> return $ Left $ Eq e1 e2''
        Right v2 -> return $ Right $ BoolVal $ v1 == v2

subst :: Expr a -> [Exists (IdentVal Value)] -> T (Expr a)
subst (Atom a) _ = return $ Atom a
subst (Bool b) _ = return $ Bool b
subst (If e1 e2 e3) env = If <$> subst e1 env <*> subst e2 env <*> subst e3 env
subst (Pair e1 e2) env = Pair <$> subst e1 env <*> subst e2 env
subst (Match e1 (x1, x2) e2) env =
  Match <$> subst e1 env <*> pure (x1, x2) <*> subst e2 env
subst (Variable x) env = case maybeFind (Env env) x of
  Nothing -> return $ Variable x
  Just v -> valueToExpr v
subst (Lambda xs e1) env = Lambda xs <$> subst e1 env
subst (Apply f es) env = Apply <$> subst f env <*> mapM (subst <*> pure env) es
subst (MemoBernoulli θ) _ = return $ MemoBernoulli θ
subst (MemoApply f e) env = MemoApply <$> subst f env <*> subst e env
subst (Let (Val x e) e1) env = Let <$> (Val x <$> subst e env) <*> subst e1 env
subst (Sequence e1 e2) env = Sequence <$> subst e1 env <*> subst e2 env
subst Fresh _ = return Fresh
subst Flip _ = return Flip
subst (Eq e1 e2) env = Eq <$> subst e1 env <*> subst e2 env


valueToExpr :: Value a -> T (Expr a)
valueToExpr (AtomVal a) = return $ Atom a
valueToExpr (BoolVal b) = return $ Bool b
valueToExpr (Function _ e _) = return e
valueToExpr (MemoFunction l) = do
  (_, S λ) <- T State.get
  return $ MemoBernoulli $ λ Map.! l
valueToExpr (PairVal a b _) = (Pair <$> valueToExpr a) <*> valueToExpr b

-- | Denotational Semantics
getDen :: (FnLabels, AtmLabels) -> T Bool
getDen (l, r) = T $ do
  (g, _) <- State.get
  State.lift $ return $
    fromJust $ contents g (l, r)

freshAtmDen :: T AtmLabels
freshAtmDen = T $ do
  (g, S λ) <- State.get
  let (r, g'@(Mem ((ls, _), _))) = freshRight g
  gNew <- State.lift $
    foldM (\g'' l -> update g'' (l, r)
      <$> bernoulli (λ Map.! l))
    g' ls
  State.put (gNew, S λ)
  return r

freshFnDen :: Double -> T FnLabels
freshFnDen θ = T $ do
  (g, S λ) <- State.get
  let (l, g'@(Mem ((_, rs), _))) = freshLeft g
  gNew <- State.lift $
    foldM (\g'' r -> update g'' (l, r)
      <$> bernoulli θ)
    g' rs
  let λ' = Map.insert l θ λ
  State.put (gNew, S λ')
  return l

den :: Expr a -> EnvVal -> T (Value a)
den (Atom a) _ = return $ AtomVal a
den (Bool b) _ = return $ BoolVal b
den (If e1 e2 e3) env = do
  b <- den e1 env
  case b of
    BoolVal True -> den e2 env
    BoolVal False -> den e3 env
den (Pair e1 e2) env = do
  v1 <- den e1 env
  v2 <- den e2 env
  return $ PairVal v1 v2 $ Prod (typeFromVal v1) (typeFromVal v2)
den (Match e1 (x1, x2) e2) env = do
  v <- den e1 env
  case v of
    PairVal v1 v2 _ -> den e2 $ defArgs env
      [This x1, This x2] [This v1, This v2]
den (Variable x) env = return $ find env x
den (Apply f es) env = do
  fv <- den f env
  vs <- forM es $ \e -> den e env
  case (fv, vs) of
    (Function f' _ _, _) -> f' (head vs)
den (Lambda xs e1) env = do
  return $ Function
      (\arg -> den e1 $ defArgs env (map This xs) [This arg])
      (Lambda xs e1)
      $ typeFromExpr (Lambda xs e1)
den (MemoBernoulli θ) _ = do
  f <- freshFnDen θ
  return $ MemoFunction f
den (MemoApply f e) env = do
  fv <- den f env
  v <- den e env
  case (fv, v) of
    (MemoFunction f', AtomVal a) -> BoolVal <$> getDen (f', a)
den (Eq e1 e2) env = do
  v1 <- den e1 env
  v2 <- den e2 env
  return $ BoolVal (v1 == v2)
den Fresh _ = AtomVal <$> freshAtmDen
den Flip _ = T $ State.lift $ BoolVal <$> bernoulli 0.5
den (Let (Val x e) e1) env = do
  env' <- define env x <$> den e env
  den e1 env'
den (Sequence e1 e2) env =
  den e1 env >> den e2 env

initEnv :: EnvVal
initEnv = makeEnv []

-- let-bind two atoms and apply a function comparing two atoms to them
exp1 :: Expr 'TBool
exp1 =
  Let (Val (Id ("x", 𝔹)) Flip) $
  Let (Val (Id ("y", 𝔹)) Flip) $
  Apply
    (Lambda [Id ("x'", 𝔹)] (Eq (Variable (Id ("x'", 𝔹))) (Variable (Id ("x", 𝔹)))))
    [Variable (Id ("y", 𝔹))]

-- assign two atoms to two variables and applyBigStep a bernoulli function of bias 0.5 to them, then applyBigStep a memoized application of the bernoulli function to the two atoms and compare them 

-- | NB: The memoization state/memory is global, not local to the body of Lambda expressions (does carry over outside the scope of the body)
-- | cf. exp2 vs exp3

exp2 :: Expr 'TBool
exp2 =
  Let (Val (Id ("x", 𝔸)) Fresh) $
  Let (Val (Id ("y", 𝔸)) Fresh) $
  Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.5)) $
  Let (Val (Id ("g", Arr 𝔸 (Arr 𝔸 𝔹))) 
    (Lambda [Id ("x'", 𝔸)] $ Lambda [Id ("y'", 𝔸)] $ 
      Eq
        (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("x'", 𝔸))))
        (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("y'", 𝔸)))))) $
  Apply
    (Apply (Variable (Id ("g", Arr 𝔸 (Arr 𝔸 𝔹)))) [Variable (Id ("x", 𝔸))]) 
    [Variable (Id ("y", 𝔸))]

exp3 :: Expr 'TBool
exp3 =
  Let (Val (Id ("x", 𝔸)) Fresh) $
  Let (Val (Id ("y", 𝔸)) Fresh) $
  Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.5)) $
  Eq (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("x", 𝔸)))) (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("y", 𝔸))))

exp4 :: Expr 'TBool
exp4 =
  Let (Val (Id ("x", 𝔸)) Fresh) $
  Let (Val (Id ("y", 𝔸)) Fresh) $
  Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.5)) $
  Eq (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("x", 𝔸)))) (Bool True)

simplify :: (Eq (LeftNode t), Show (LeftNode t)) =>
  (a, (MemoBigraph (LeftNode t) r b, StateOfBiases t))
  -> (a, [(LeftNode t, Double)], [r], [((LeftNode t, r), b)])
simplify (b, (Mem ((l, r), m), S λ)) =
    (b,
    zipWith (\f (f', θ) ->
      if f == f' then (f, θ) else error (show f ++ " ≠ " ++ show f'))
      (Set.toList l) (Map.toList λ),
    Set.toList r,
    Map.toList m)

main :: IO ()
main = do
  let exps = [exp1, exp2, exp3, exp4]
  forM_ exps $ \exp -> do
    print exp
    let T ev = den exp initEnv
    let T ev' = bigStepComplete exp initEnv
    let T ev'' = smallStep exp initEnv
    let res = simplify <$> State.runStateT ev (initMem, S Map.empty)
    let res' = simplify <$> State.runStateT ev' (initMem, S Map.empty)
    let res'' = simplify <$> State.runStateT ev'' (initMem, S Map.empty)
    putStrLn $ Dist.pretty show res
    putStrLn $ Dist.pretty show res'
    putStrLn $ Dist.pretty show res''