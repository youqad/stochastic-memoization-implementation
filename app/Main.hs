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

import Test.QuickCheck
-- import System.IO.Unsafe (unsafePerformIO)

import Syntax
import Environment
import Values


bernoulli :: Num prob => prob -> Dist.T prob Bool
bernoulli θ = Dist.choose θ True False

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

smallStep :: Expr a -> EnvVal -> T (ExprOrValue a, EnvVal)
smallStep (Atom a) env = return (Right $ AtomVal a, env)
smallStep (Bool b) env = return (Right $ BoolVal b, env)
smallStep (If e1 e2 e3) env = do
  (e1', env') <- smallStep e1 env
  case e1' of
    Left e1'' -> return (Left $ If e1'' e2 e3, env')
    Right (BoolVal True) -> return (Left e2, env')
    Right (BoolVal False) -> return (Left e3, env')
smallStep (Pair e1 e2) env = do
  (e1', env') <- smallStep e1 env
  case e1' of
    Left e1'' -> return (Left $ Pair e1'' e2, env')
    Right v1 -> do
      (e2', env'') <- smallStep e2 env
      case e2' of
        Left e2'' -> return (Left $ Pair e1 e2'', env'')
        Right v2 -> return (Right $ PairVal v1 v2 $
          Prod (typeFromVal v1) (typeFromVal v2), env'')
smallStep (Match e1 (x1, x2) e2) env = do
  (e1', env') <- smallStep e1 env
  case e1' of
    Left e1'' -> return (Left $ Match e1'' (x1, x2) e2, env')
    Right (PairVal v1 v2 _) -> return (Left e2, defArgs env ids vs)
      where
        ids = [This x1, This x2]
        vs = [This v1, This v2]
smallStep (Variable x) env = return (Right $ find env x, env)
smallStep (Lambda xs e1) env = do
  return (Right $ Function
      (\arg -> bigStep e1 $ defArgs env (map This xs) [This arg])
      (Lambda xs e1)
      $ typeFromExpr (Lambda xs e1), env)
smallStep (Apply f es) env = do
  (f', env') <- smallStep f env
  case f' of
    Left f'' -> return (Left $ Apply f'' es, env')
    Right (Function f'' _ _) -> do
      es' <- forM es $ \e -> smallStep e env
      case head es' of
        (Left e', env'') -> return (Left $ Apply f [e'], env'')
        (Right v, env'') -> do
          v' <- f'' v
          return (Right v', env'')
smallStep (MemoBernoulli θ) env = do
  f <- freshFnOpSem θ
  return (Right $ MemoFunction f, env)
smallStep (MemoApply f e) env = do
  (f', env') <- smallStep f env
  case f' of
    Left f'' -> return (Left $ MemoApply f'' e, env')
    Right (MemoFunction f'') -> do
      (e', env'') <- smallStep e env
      case e' of
        Left e'' -> return (Left $ MemoApply f e'', env'')
        Right (AtomVal a) -> do
          b <- getOpSem (f'', a)
          return (Right $ BoolVal b, env'')
smallStep (Let (Val x e) e1) env = do
  (e', env') <- smallStep e env
  case e' of
    Left e'' -> return (Left $ Let (Val x e'') e1, env')
    Right v -> return (Left e1, define env' x v)
smallStep (Sequence e1 e2) env = do
  (e1', env') <- smallStep e1 env
  case e1' of
    Left e1'' -> return (Left $ Sequence e1'' e2, env')
    Right _ -> return (Left e2, env')
smallStep Fresh env = do
  a <- freshAtmOpSem
  return (Right $ AtomVal a, env)
smallStep Flip env = T $ State.lift $ do
  b <- bernoulli 0.5
  return (Right $ BoolVal b, env)
smallStep (Eq e1 e2) env = do
  (e1', env') <- smallStep e1 env
  case e1' of
    Left e1'' -> return (Left $ Eq e1'' e2, env')
    Right v1 -> do
      (e2', env'') <- smallStep e2 env
      case e2' of
        Left e2'' -> return (Left $ Eq e1 e2'', env'')
        Right v2 -> return (Right $ BoolVal $ v1 == v2, env'')

-- subst :: Expr a -> [Exists (IdentVal Value)] -> T (Expr a)
-- subst (Atom a) _ = return $ Atom a
-- subst (Bool b) _ = return $ Bool b
-- subst (If e1 e2 e3) env = If <$> subst e1 env <*> subst e2 env <*> subst e3 env
-- subst (Pair e1 e2) env = Pair <$> subst e1 env <*> subst e2 env
-- subst (Match e1 (x1, x2) e2) env =
--   Match <$> subst e1 env <*> pure (x1, x2) <*> subst e2 env
-- subst (Variable x) env = case maybeFind (Env env) x of
--   Nothing -> return $ Variable x
--   Just v -> valueToExpr v
-- subst (Lambda xs e1) env = Lambda xs <$> subst e1 env
-- subst (Apply f es) env = Apply <$> subst f env <*> mapM (subst <*> pure env) es
-- subst (MemoBernoulli θ) _ = return $ MemoBernoulli θ
-- subst (MemoApply f e) env = MemoApply <$> subst f env <*> subst e env
-- subst (Let (Val x e) e1) env = Let <$> (Val x <$> subst e env) <*> subst e1 env
-- subst (Sequence e1 e2) env = Sequence <$> subst e1 env <*> subst e2 env
-- subst Fresh _ = return Fresh
-- subst Flip _ = return Flip
-- subst (Eq e1 e2) env = Eq <$> subst e1 env <*> subst e2 env


valueToExpr :: Value a -> T (Expr a)
valueToExpr (AtomVal a) = return $ Atom a
valueToExpr (BoolVal b) = return $ Bool b
valueToExpr (Function _ e _) = return e
valueToExpr (MemoFunction l) = do
  (_, S λ) <- T State.get
  return $ MemoBernoulli $ λ Map.! l
valueToExpr (PairVal a b _) = (Pair <$> valueToExpr a) <*> valueToExpr b

-- | Transitive closure of small step semantics

smallStepIterate :: Int -> Expr a -> EnvVal -> T (ExprOrValue a, EnvVal)
smallStepIterate 0 e env = return (Left e, env)
smallStepIterate n e env = do
  (e', env') <- smallStep e env
  case e' of
    Left e'' -> smallStepIterate (n - 1) e'' env'
    Right v -> return (Right v, env')


smallStepIterated :: Expr a -> EnvVal -> T (Value a)
smallStepIterated e env = do
  (e', env') <- smallStep e env
  case e' of
    Left e'' -> smallStepIterated e'' env'
    Right v -> return v

smallStepIteratedComplete :: Expr a -> EnvVal -> T (Value a)
smallStepIteratedComplete e env = do
  v <- smallStepIterated e env
  completeBigraph
  return v

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

exp5 :: Expr 'TBool 
-- exp5 is the expression (where == is syntactic sugar for the Eq construct):
-- "if (λ (x_1) flip())((λ (x_1) fresh())(flip())) then (λ (x_1) fresh())(flip()) == (if flip() then fresh() else fresh()) else (if flip() then fresh() else fresh()), (if flip() then fresh() else fresh())"
exp5 = 
  If (Apply (Lambda [Id ("x_1", 𝔸)] Flip) [Apply (Lambda [Id ("x_2", 𝔹)] Fresh) [Flip]]) 
    (Apply (Lambda [Id ("x_3", 𝔹)] Fresh) [Flip]
    `Eq`  
    If Flip Fresh Fresh) $
    If Flip Flip Flip




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

simplify' :: (Eq (LeftNode t), Show (LeftNode t)) =>
  (a, (MemoBigraph (LeftNode t) r b, StateOfBiases t))
  -> (a, [(LeftNode t, Double)], [r])
simplify' (b, (Mem ((l, r), _), S λ)) =
    (b,
    zipWith (\f (f', θ) ->
      if f == f' then (f, θ) else error (show f ++ " ≠ " ++ show f'))
      (Set.toList l) (Map.toList λ),
    Set.toList r)

run :: Ord a => 
  (e -> EnvVal -> T a)
  -> e -> Dist (a, [(FnLabels, Double)], [AtmLabels])
run sem e =
  let T ev = sem e initEnv
      res = simplify' <$> State.runStateT ev (initMem, S Map.empty) in
  Dist.norm res

runSems :: [Expr a -> Dist (Value a, [(FnLabels, Double)], [AtmLabels])]
runSems = [run den, run bigStepComplete, run smallStepIteratedComplete]

-- QuickCheck to test equivalence of the various semantics
-- prop_semantics :: Expr a -> Property
-- prop_semantics e =
--   forAll (choose (0, 10)) $ \n ->
--     let res = runSems <*> [e] in
--     all (== head res) (tail res)

-- | More permissive version of `approx`:
approx' :: (RealFloat prob, Ord a) =>
  Dist.T prob a -> Dist.T prob a ->Bool
approx' (Dist.Cons xs) (Dist.Cons ys) =
  let (xse, xsp) = unzip (Dist.norm' xs)
      (yse, ysp) = unzip (Dist.norm' ys)
  in  xse == yse &&
      all (\p -> abs p < 1e-8) (zipWith (-) xsp ysp)


prop_semanticsEquivalent :: Property
prop_semanticsEquivalent =
  forAll (resize 4 arbitrary :: Gen (Exists Expr)) $ \(This expr) ->
      let bigStepResult = run bigStep expr
          denResult = run den expr
      in
      -- test that the two semantics agree on the distribution with @approx'@,
      -- and if they don't, display the two distributions
      counterexample (Dist.pretty show bigStepResult ++ "\n  ≠  \n" ++ Dist.pretty show denResult) $ approx' bigStepResult denResult

-- -- expression1: if ((λx_1. Flip) [(λx_2. Fresh) [Flip]]) then (((λx_3. Fresh) [Flip]) == (if (Flip) then (Fresh) else (Fresh))) else (if (Flip) then (Flip) else (Flip))
expression1 :: Expr _
expression1 = 
  If (Apply (Lambda [Id ("x_1", 𝔸)] Flip) [Apply (Lambda [Id ("x_2", 𝔹)] Fresh) [Flip]]) 
    (Apply (Lambda [Id ("x_3", 𝔹)] Fresh) [Flip]
    `Eq`  
    If Flip Fresh Fresh) $
    If Flip Flip Flip



main :: IO ()
main = do
  -- let exps = [exp1]--, exp2, exp3, exp4]
  -- exps <- generate (vectorOf 2 (resize 4 arbitrary :: Gen (Exists Expr)))
  -- forM_ exps $ \(This exp) -> do
  --   putStrLn "_______________________"
  --   print exp
  --   let res = runSems <*> [exp]
  --   forM_ res putStrLn
  --   putStrLn $ run (smallStepIterate 2) exp
  --   putStrLn "_______________________"
  print exp5
  quickCheck prop_semanticsEquivalent