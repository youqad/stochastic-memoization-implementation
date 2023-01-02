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

-- smallStep with a an extra environment for temporary variables 
-- (to store values that need to be remembered while evaluating the expression)
smallStep :: Expr a -> EnvVal -> EnvVal -> T (ExprOrValue a, EnvVal, EnvVal)
smallStep (Atom a) envTemp env = return (Right $ AtomVal a, envTemp, env)
smallStep (Bool b) envTemp env = return (Right $ BoolVal b, envTemp, env)
smallStep (If e1 e2 e3) envTemp env = do
  (e1', envTemp', env') <- smallStep e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ If e1'' e2 e3, envTemp', env')
    Right (BoolVal True) -> return (Left e2, envTemp', env')
    Right (BoolVal False) -> return (Left e3, envTemp', env')
smallStep (Pair e1 e2) envTemp env = do
  (e1', envTemp', env') <- smallStep e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ Pair e1'' e2, envTemp', env')
    Right v1 -> do
      (e2', envTemp'', env'') <- smallStep e2 envTemp' env'
      case e2' of
        Left e2'' -> do
          case e1 of
            Variable x -> return (Left $ Pair (Variable x) e2'', envTemp'', env'')
            _ -> do
              let varName = "x_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal v1)
                  envTemp''' = define envTemp'' ident v1
              return (Left $ Pair (Variable ident) e2'', envTemp''', env'')
        Right v2 -> return (Right $ PairVal v1 v2 $
          Prod (typeFromVal v1) (typeFromVal v2), envTemp'', env'')
smallStep (Match e1 (x1, x2) e2) envTemp env = do
  (e1', envTemp', env') <- smallStep e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ Match e1'' (x1, x2) e2, envTemp', env')
    Right (PairVal v1 v2 _) -> return (Left e2, envTemp', defArgs env' ids vs)
      where
        ids = [This x1, This x2]
        vs = [This v1, This v2]
smallStep (Variable x) envTemp env = do
  let env' = envTemp `union` env
  return (Right $ find env' x, envTemp, env)
smallStep (Lambda xs e1) envTemp env = do
  let env' = envTemp `union` env
  return (Right $ Function
      (\arg -> bigStep e1 $ defArgs env' (map This xs) [This arg])
      (Lambda xs e1)
      $ typeFromExpr (Lambda xs e1), envTemp, env)
smallStep (Apply f es) envTemp env = do
  (f', envTemp', env') <- smallStep f envTemp env
  case f' of
    Left f'' -> return (Left $ Apply f'' es, envTemp', env')
    Right fv@(Function f'' _ _) -> do
      es' <- forM es $ \e -> smallStep e envTemp' env'
      case head es' of
        (Left e', envTemp'', env'') -> 
          case f of
            Variable x -> 
              return (Left $ Apply (Variable x) (e':tail es), envTemp'', env'')
            _ -> do
              let varName = "f_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal fv)
                  envTemp''' = define envTemp'' ident fv
              return (Left $ Apply (Variable ident) (e':tail es), envTemp''', env'')
        (Right v, envTemp'', env'') -> do
          v' <- f'' v
          return (Right v', envTemp'', env'')
smallStep (MemoBernoulli θ) envTemp env = do
  f <- freshFnOpSem θ
  return (Right $ MemoFunction f, envTemp, env)
smallStep (MemoApply f e) envTemp env = do
  (f', envTemp', env') <- smallStep f envTemp env
  case f' of
    Left f'' -> return (Left $ MemoApply f'' e, envTemp', env')
    Right fv@(MemoFunction f'') -> do
      (e', envTemp'', env'') <- smallStep e envTemp' env'
      case e' of
        Left e'' -> do
          case f of
            Variable x -> 
              return (Left $ MemoApply (Variable x) e'', envTemp'', env'')
            _ -> do
              let varName = "fMemo_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal fv)
                  envTemp''' = define envTemp'' ident fv
              return (Left $ MemoApply (Variable ident) e'', envTemp''', env'')
        Right (AtomVal a) -> do
          b <- getOpSem (f'', a)
          return (Right $ BoolVal b, envTemp'', env'')
smallStep (Let (Val x e) e1) envTemp env = do
  (e', envTemp', env') <- smallStep e envTemp env
  case e' of
    Left e'' -> return (Left $ Let (Val x e'') e1, envTemp', env')
    Right v -> return (Left e1, envTemp', define env' x v)
smallStep (Sequence e1 e2) envTemp env = do
  (e1', envTemp', env') <- smallStep e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ Sequence e1'' e2, envTemp', env')
    Right _ -> return (Left e2, envTemp', env')
smallStep Fresh envTemp env = do
  a <- freshAtmOpSem
  return (Right $ AtomVal a, envTemp, env)
smallStep Flip envTemp env = T $ State.lift $ do
  b <- bernoulli 0.5
  return (Right $ BoolVal b, envTemp, env)
smallStep (Eq e1 e2) envTemp env = do
  (e1', envTemp', env') <- smallStep e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ Eq e1'' e2, envTemp', env')
    Right v1 -> do
      (e2', envTemp'', env'') <- smallStep e2 envTemp' env'
      case e2' of
        Left e2'' -> do
          case e1 of
            Variable x -> 
              return (Left $ Eq (Variable x) e2'', envTemp'', env'')
            _ -> do
              let varName = "e_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal v1)
                  envTemp''' = define envTemp'' ident v1
              return (Left $ Eq (Variable ident) e2'', envTemp''', env'')
        Right v2 -> return (Right $ BoolVal $ v1 == v2, envTemp'', env'')

subst :: Expr a -> EnvVal -> T (Expr a)
subst (Atom a) _ = return $ Atom a
subst (Bool b) _ = return $ Bool b
subst (If e1 e2 e3) env = If <$> subst e1 env <*> subst e2 env <*> subst e3 env
subst (Pair e1 e2) env = Pair <$> subst e1 env <*> subst e2 env
subst (Match e1 (x1, x2) e2) env =
  Match <$> subst e1 env <*> pure (x1, x2) <*> subst e2 env
subst (Variable x) env = case maybeFind env x of
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

-- | Transitive closure of small step semantics

smallStepIterate :: Int -> Expr a -> EnvVal -> T (ExprOrValue a, EnvVal)
smallStepIterate n expr = smallStepIterate' n expr (makeEnv []) 
  where 
    smallStepIterate' 0 e envTemp env = do 
      e' <- subst e envTemp
      return (Left e', env)
    smallStepIterate' m e envTemp env = do
      (e', envTemp', env') <- smallStep e envTemp env
      case e' of
        Left e'' -> smallStepIterate' (m - 1) e'' envTemp' env'
        Right v -> return (Right v, env')


smallStepIterated :: Expr a -> EnvVal -> T (Value a)
smallStepIterated expr = smallStepIterated' expr (makeEnv [])
  where 
    smallStepIterated' e envTemp env = do
      (e', envTemp', env') <- smallStep e envTemp env
      case e' of
        Left e'' -> smallStepIterated' e'' envTemp' env'
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

-- exp6: if ((λx_1. Flip) [(λx_2. Fresh) [Flip]]) then (((λx_3. Fresh) [Flip]) == (if (Flip) then (Fresh) else (Fresh))) else (if (Flip) then (Flip) else (Flip))
exp6 :: Expr 'TBool
exp6 = 
  If (Apply (Lambda [Id ("x_1", 𝔸)] Flip) [Apply (Lambda [Id ("x_2", 𝔹)] Fresh) [Flip]]) 
    (Apply (Lambda [Id ("x_3", 𝔹)] Fresh) [Flip]
    `Eq`  
    If Flip Fresh Fresh) $
    If Flip Flip Flip

-- exp7: ((λx_1. Fresh) [memoBernoulli 0.166 `memoApply` (Fresh)]) == (let (x_1 := (λx_1. x_1)) in (λx_2. Fresh) [(λx_1. Flip)])
exp7 :: Expr 'TBool
exp7 = 
  Apply (Lambda [Id ("x_1", 𝔹)] Fresh) [MemoBernoulli 0.166 `MemoApply` Fresh]
  `Eq`
  Let (Val (Id ("x_1", Arr 𝔸 𝔸)) (Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸))))) 
  (Apply (Lambda [Id ("x_2", Arr 𝔸 𝔸)] Fresh) [Lambda [Id ("x_1", 𝔸)] Fresh])

-- exp8: Match (Match ((Fresh) == (Fresh), let (x_1 := (λx_1. x_1)) in Fresh) with (x_1, x_2) -> (let (x_3 := (λx_3. Fresh)) in memoBernoulli 0.403), Match (if (Flip) then ((λx_1. Fresh)) else ((λx_1. Fresh)), let (x_1 := (λx_1. x_1)) in Flip) with (x_1, x_2) -> (if (x_2) then (memoBernoulli 0.795) else (memoBernoulli 0.826))) with (x_1, x_2) -> (Fresh)
exp8 :: Expr 'TAtom
exp8 = 
  Match (
    Pair
    (Match
      (Pair (Fresh `Eq` Fresh) (Let (Val (Id ("x_1", Arr 𝔹 𝔹)) (Lambda [Id ("x_1", 𝔹)] (Variable (Id ("x_1", 𝔹))))) Fresh)) 
      (Id ("x_1", 𝔹), Id ("x_2", 𝔸))
      (Let (Val (Id ("x_3", Arr 𝔹 𝔸)) (Lambda [Id ("x_3", 𝔹)] Fresh)) (MemoBernoulli 0.403)))
    (Match 
      (Pair
      (If Flip (Lambda [Id ("x_1", 𝔸)] Fresh) (Lambda [Id ("x_1", 𝔸)] Fresh))
      (Let (Val (Id ("x_1", Arr 𝔹 𝔹)) (Lambda [Id ("x_1", 𝔹)] (Variable (Id ("x_1", 𝔹))))) Flip))
      (Id ("x_1", Arr 𝔸 𝔸), Id ("x_2", 𝔹))
      (If (Variable (Id ("x_2", 𝔹))) (MemoBernoulli 0.795) (MemoBernoulli 0.826)))
  )
  (Id ("x_1", MemFn), Id ("x_2", MemFn)) 
  Fresh

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
      let bigStepResult = run bigStepComplete expr
          denResult = run den expr
          smallStepResult = run smallStepIteratedComplete expr
      in
      -- test that the two semantics agree on the distribution with @approx'@,
      -- and if they don't, display the two distributions
      counterexample (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |denotational| \n\n" ++ Dist.pretty show denResult) (approx' bigStepResult denResult)
      .&&. 
      counterexample (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |smallStep| \n\n" ++ Dist.pretty show smallStepResult) (approx' bigStepResult smallStepResult)



main :: IO ()
main = do
  let exps = [This exp8]--, This exp2, This exp3, This exp4]
  -- exps <- generate (vectorOf 2 (resize 4 arbitrary :: Gen (Exists Expr)))
  forM_ exps $ \(This exp) -> do
    putStrLn "_______________________"
    print exp
    let res = runSems <*> [exp]
    forM_ res (putStrLn . Dist.pretty show)
    let T ev = smallStepIterate 2 exp initEnv
        res' = simplify' <$> State.runStateT ev (initMem, S Map.empty)
    putStrLn $ "smallStepIterate 2: \n" ++ Dist.pretty show (Dist.norm res')
    putStrLn "_______________________"
  -- print exp5
  -- quickCheck prop_semanticsEquivalent