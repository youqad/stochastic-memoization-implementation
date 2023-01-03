{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, DerivingVia, FlexibleInstances #-}

module Semantics where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (partition)

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
-- | PROBABILITY DISTRIBUTIONS
------------------------

bernoulli :: Num prob => prob -> Dist.T prob Bool
bernoulli θ = Dist.choose θ True False

-- | More permissive version of `approx`:
approx' :: (RealFloat prob, Ord a) =>
  Dist.T prob a -> Dist.T prob a -> Bool
approx' (Dist.Cons xs) (Dist.Cons ys) =
  let (xse, xsp) = unzip (Dist.norm' xs)
      (yse, ysp) = unzip (Dist.norm' ys)
  in  xse == yse &&
      all (\p -> abs p < 1e-2) (zipWith (-) xsp ysp)

forcedGrouping :: (Eq a, Num b) => [(a, b)] -> [(a, b)]
forcedGrouping ls = case ls of
  [] -> []
  ((x, p):xs) -> 
    let (xs', notxs') = partition ((== x) . fst) xs
        p' = sum $ p : map snd xs' in
    (x, p') : forcedGrouping notxs'

-- | @approx''@ = @approx'@, but with forced grouping in case @Dist.norm'@ didn't group all values.
approx'' :: (RealFloat prob, Ord a) =>
  Dist.T prob a -> Dist.T prob a -> Bool
approx'' dist1@(Dist.Cons xs) dist2@(Dist.Cons ys) =
  approx' dist1 dist2 || 
  (let
    (xse, xsp) = unzip (forcedGrouping (Dist.norm' xs))
    (yse, ysp) = unzip (forcedGrouping (Dist.norm' ys)) in
    xse == yse
      && all (\ p -> abs p < 1e-2) (zipWith (-) xsp ysp))


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
              let varName = "xTemp_" ++ show (Environment.length envTemp'' 
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
  return (Right -- $ trace ("envTemp: " ++ show envTemp ++ " env: " ++ show env) 
          $ find env' x
    , envTemp, env)
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
              let varName = "fTemp_" ++ show (Environment.length envTemp'' 
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
              let varName = "fMemoTemp_" ++ show (Environment.length envTemp'' 
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
              let varName = "eTemp_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal v1)
                  envTemp''' = define envTemp'' ident v1
              return (Left $ Eq (Variable ident) e2'', envTemp''', env'')
        Right v2 -> return (Right $ BoolVal $ v1 == v2, envTemp'', env'')

-- smallStep' Nothing with a an extra environment for temporary variables 
-- (to store values that need to be remembered while evaluating the expression)
smallStep' :: Maybe (EnvVal, EnvVal, Maybe (FnLabels, AtmLabels)) -> Expr a -> EnvVal -> EnvVal -> T (ExprOrValue a, EnvVal, EnvVal)
smallStep' Nothing (Atom a) envTemp env = return (Right $ AtomVal a, envTemp, env)
smallStep' Nothing (Bool b) envTemp env = return (Right $ BoolVal b, envTemp, env)
smallStep' Nothing (If e1 e2 e3) envTemp env = do
  (e1', envTemp', env') <- smallStep' Nothing e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ If e1'' e2 e3, envTemp', env')
    Right (BoolVal True) -> return (Left e2, envTemp', env')
    Right (BoolVal False) -> return (Left e3, envTemp', env')
smallStep' Nothing (Pair e1 e2) envTemp env = do
  (e1', envTemp', env') <- smallStep' Nothing e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ Pair e1'' e2, envTemp', env')
    Right v1 -> do
      (e2', envTemp'', env'') <- smallStep' Nothing e2 envTemp' env'
      case e2' of
        Left e2'' -> do
          case e1 of
            Variable x -> return (Left $ Pair (Variable x) e2'', envTemp'', env'')
            _ -> do
              let varName = "xTemp_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal v1)
                  envTemp''' = define envTemp'' ident v1
              return (Left $ Pair (Variable ident) e2'', envTemp''', env'')
        Right v2 -> return (Right $ PairVal v1 v2 $
          Prod (typeFromVal v1) (typeFromVal v2), envTemp'', env'')
smallStep' Nothing (Match e1 (x1, x2) e2) envTemp env = do
  (e1', envTemp', env') <- smallStep' Nothing e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ Match e1'' (x1, x2) e2, envTemp', env')
    Right (PairVal v1 v2 _) -> return (Left e2, envTemp', defArgs env' ids vs)
      where
        ids = [This x1, This x2]
        vs = [This v1, This v2]
smallStep' Nothing (Variable x) envTemp env = do
  let env' = envTemp `union` env
  return (Right -- $ trace ("envTemp: " ++ show envTemp ++ " env: " ++ show env) 
          $ find env' x
    , envTemp, env)
smallStep' Nothing (Lambda xs e1) envTemp env = do
  let env' = envTemp `union` env
  return (Right $ Function
      (\arg -> bigStep e1 $ defArgs env' (map This xs) [This arg])
      (Lambda xs e1)
      $ typeFromExpr (Lambda xs e1), envTemp, env)
smallStep' Nothing (Apply f es) envTemp env = do
  (f', envTemp', env') <- smallStep' Nothing f envTemp env
  case f' of
    Left f'' -> return (Left $ Apply f'' es, envTemp', env')
    Right fv@(Function f'' _ _) -> do
      es' <- forM es $ \e -> smallStep' Nothing e envTemp' env'
      case head es' of
        (Left e', envTemp'', env'') -> 
          case f of
            Variable x -> 
              return (Left $ Apply (Variable x) (e':tail es), envTemp'', env'')
            _ -> do
              let varName = "fTemp_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal fv)
                  envTemp''' = define envTemp'' ident fv
              return (Left $ Apply (Variable ident) (e':tail es), envTemp''', env'')
        (Right v, envTemp'', env'') -> do
          v' <- f'' v
          return (Right v', envTemp'', env'')
smallStep' Nothing (MemoBernoulli θ) envTemp env = do
  f <- freshFnOpSem θ
  return (Right $ MemoFunction f, envTemp, env)
smallStep' Nothing (MemoApply f e) envTemp env = do
  (f', envTemp', env') <- smallStep' Nothing f envTemp env
  case f' of
    Left f'' -> return (Left $ MemoApply f'' e, envTemp', env')
    Right fv@(MemoFunction f'') -> do
      (e', envTemp'', env'') <- smallStep' Nothing e envTemp' env'
      case e' of
        Left e'' -> do
          case f of
            Variable x -> 
              return (Left $ MemoApply (Variable x) e'', envTemp'', env'')
            _ -> do
              let varName = "fMemoTemp_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal fv)
                  envTemp''' = define envTemp'' ident fv
              return (Left $ MemoApply (Variable ident) e'', envTemp''', env'')
        Right (AtomVal a) -> do
          b <- getOpSem (f'', a)
          return (Right $ BoolVal b, envTemp'', env'')
smallStep' Nothing (Let (Val x e) e1) envTemp env = do
  (e', envTemp', env') <- smallStep' Nothing e envTemp env
  case e' of
    Left e'' -> return (Left $ Let (Val x e'') e1, envTemp', env')
    Right v -> return (Left e1, envTemp', define env' x v)
smallStep' Nothing (Sequence e1 e2) envTemp env = do
  (e1', envTemp', env') <- smallStep' Nothing e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ Sequence e1'' e2, envTemp', env')
    Right _ -> return (Left e2, envTemp', env')
smallStep' Nothing Fresh envTemp env = do
  a <- freshAtmOpSem
  return (Right $ AtomVal a, envTemp, env)
smallStep' Nothing Flip envTemp env = T $ State.lift $ do
  b <- bernoulli 0.5
  return (Right $ BoolVal b, envTemp, env)
smallStep' Nothing (Eq e1 e2) envTemp env = do
  (e1', envTemp', env') <- smallStep' Nothing e1 envTemp env
  case e1' of
    Left e1'' -> return (Left $ Eq e1'' e2, envTemp', env')
    Right v1 -> do
      (e2', envTemp'', env'') <- smallStep' Nothing e2 envTemp' env'
      case e2' of
        Left e2'' -> do
          case e1 of
            Variable x -> 
              return (Left $ Eq (Variable x) e2'', envTemp'', env'')
            _ -> do
              let varName = "eTemp_" ++ show (Environment.length envTemp'' 
                          + Environment.length env'' + 1)
                  ident = Id (varName, typeFromVal v1)
                  envTemp''' = define envTemp'' ident v1
              return (Left $ Eq (Variable ident) e2'', envTemp''', env'')
        Right v2 -> return (Right $ BoolVal $ v1 == v2, envTemp'', env'')
smallStep' _ _ _ _ = undefined


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


------------------------
-- | TESTS
------------------------

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