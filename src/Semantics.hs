{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, DerivingVia, FlexibleInstances #-}

module Semantics where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (partition)

import Data.Maybe (fromJust, isJust)
import Control.Monad (forM_, when, unless, forM, foldM)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State
-- import qualified Control.Monad.Trans.State.Strict as State
-- import Debug.Trace (trace, traceM)

import Syntax
import Environment
import Values
-- import Text.Pretty.Simple (pPrintString, pShow)

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




type Flag = Bool
-- a type flag to indicate whether at the top-level expression, the environment has already been stored on the restoration stack 

type 𝒯 x = State.StateT (Flag, Maybe [(EnvVal, EnvVal)], EnvVal, EnvVal) T x
-- Flag: whether at the top-level expression, the environment has already been stored on the current restoration stack
-- Maybe [(EnvVal, EnvVal)] is the restoration stack of (envTemp, env) environments to restore once we hit a value 
-- EnvVal, EnvVal: envTemp, env: an extra environment envTemp for temporary variables (to store values that need to be remembered while evaluating the expression), and the current environment env

getFlag :: 𝒯 Flag
getFlag = do
  (flag, _, _, _) <- State.get
  return flag

setFlag :: Bool -> 𝒯 ()
setFlag b = do
  (_, envs, envTemp, env) <- State.get
  State.put (b, envs, envTemp, env)

addRestore :: (EnvVal, EnvVal) -> 𝒯 ()
addRestore (envTemp', env') = do
  (flag, envs, envTemp, env) <- State.get
  case envs of
    Just envs' -> State.put (flag, Just ((envTemp', env') : envs'), envTemp, env)
    Nothing -> State.put (flag, Just [(envTemp', env')], envTemp, env)

restoreEnv :: 𝒯 ()
restoreEnv = do
  (_, toBeRestored, envTemp, env) <- State.get 
  case toBeRestored of
    Just ((envTemp', env') : envs) -> do
      State.put (False, Just envs, envTemp', env')
    _ -> do 
      State.put (False, Nothing, envTemp, env)

-- smallStep: 
smallStep :: Expr a -> 𝒯 (ExprOrValue a)
smallStep (Atom a) = return $ Right $ AtomVal a
smallStep (Bool b) = return $ Right $ BoolVal b
smallStep (If e1 e2 e3) = do
  e1' <- smallStep e1
  case e1' of
    Left e1'' -> do
      return $ Left $ If e1'' e2 e3
    Right (BoolVal True) -> do
      return $ Left e2
    Right (BoolVal False) -> do
      return $ Left e3
smallStep (Pair e1 e2) = do
  (_, _, envT, _) <- State.get
  case e1 of
    Variable x | isJust (maybeFind envT x) -> do
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      e2' <- smallStep e2
      case e2' of
        Left e2'' -> do
          setFlag True
          return $ Left $ Pair (Variable x) e2''
        Right v2 -> do
          restoreEnv
          let v1 = find (envTemp `union` env) x
          return $ Right $ PairVal v1 v2 
            $ Prod (typeFromVal v1) (typeFromVal v2)
    _ -> do
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      e1' <- smallStep e1
      case e1' of
        Left e1'' -> do
          setFlag True
          return (Left $ Pair e1'' e2)
        Right v1 -> do
          restoreEnv
          (_, envs', envTemp', env') <- State.get
          let varName = "xTemp_" ++ show (Environment.length envTemp' 
                      + Environment.length env' + 1)
              ident = Id (varName, typeFromVal v1)
              envTemp'' = define envTemp' ident v1
          State.put (False, envs', envTemp'', env')
          return $ Left $ Pair (Variable ident) e2
smallStep (Match e1 (x1, x2) e2) = do
  e1' <- smallStep e1
  case e1' of
    Left e1'' -> do
      return $ Left $ Match e1'' (x1, x2) e2
    Right (PairVal v1 v2 _) -> do
      (flag, toBeRestored, envTemp, env) <- State.get
      let ids = [This x1, This x2]
          vs = [This v1, This v2]
          env' = defArgs env ids vs
      State.put (False, toBeRestored, envTemp, env')
      return $ Left e2
smallStep (Variable x) = do
  (_, _, envTemp, env) <- State.get 
  return $ Right $ find (envTemp `union` env) x
smallStep (Lambda xs e1) = do
  return $ Right $ Function
        (\_ -> error "smallStep: Lambda: impossible case")
        (Lambda xs e1)
        $ typeFromExpr (Lambda xs e1)
smallStep (Apply f es) = do
  (_, _, envT, _) <- State.get
  case f of
    Variable x | isJust (maybeFind envT x) -> do
      let Function _ f' _ = find envT x
      case f' of
        Lambda xs e1 -> do
          (_, _, envTemp', env') <- State.get
          addRestore (envTemp', env')
          setFlag True
          return $ Left $ Let (Val (head xs) (head es)) e1
        _ -> error "smallStep: Apply: impossible case"
    _ -> do
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      f' <- smallStep f
      case f' of
        Left f'' -> do
          setFlag True
          return $ Left $ Apply f'' es
        Right fv -> do
          restoreEnv
          (_, envs', envTemp', env') <- State.get
          let varName = "fTemp_" ++ show (Environment.length envTemp' 
                      + Environment.length env' + 1)
              ident = Id (varName, typeFromVal fv)
              envTemp'' = define envTemp' ident fv
          State.put (False, envs', envTemp'', env')
          return $ Left $ Apply (Variable ident) es
smallStep (MemoBernoulli θ) = do
  f <- State.lift $ freshFnOpSem θ
  return $ Right $ MemoFunction f
smallStep (MemoApply f e) = do
  (_, _, envT, _) <- State.get
  case f of
    Variable x | isJust (maybeFind envT x) -> do
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      e' <- smallStep e
      case e' of
        Left e'' -> do
          setFlag True
          return (Left $ MemoApply (Variable x) e'')
        Right (AtomVal a) -> do
          restoreEnv
          let MemoFunction f' = find (envTemp `union` env) x
          b <- State.lift $ getOpSem (f', a)
          return $ Right $ BoolVal b
    _ -> do
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      f' <- smallStep f
      case f' of
        Left f'' -> do
          setFlag True
          return $ Left $ MemoApply f'' e
        Right fv -> do
          restoreEnv
          (_, envs', envTemp', env') <- State.get
          let varName = "fMemoTemp_" ++ show (Environment.length envTemp' 
                      + Environment.length env' + 1)
              ident = Id (varName, typeFromVal fv)
              envTemp'' = define envTemp' ident fv
          State.put (False, envs', envTemp'', env')
          return $ Left $ MemoApply (Variable ident) e
smallStep (Let (Val x e1) e2) = do
  (_, _, envT, _) <- State.get
  case e1 of
    Variable y | isJust (maybeFind envT y) -> do
      e2' <- smallStep e2
      case e2' of
        Left e2'' -> do
          return $ Left $ Let (Val x e1) e2''
        Right v -> do 
          restoreEnv
          return $ Right v
    _ -> do
      e1' <- smallStep e1
      case e1' of
        Left e1'' -> do
          return $ Left $ Let (Val x e1'') e2
        Right v -> do
          (flag, envs, envTemp, env) <- State.get
          if flag
            then do
              -- e2 is the body of a λ-abstraction, 
              -- so we need to restore the environments later.
              -- Store the value in a temporary variable
              let varName = "xLambdaTemp_" ++ show (Environment.length envTemp 
                          + Environment.length env + 1)
                  ident = Id (varName, typeFromVal v)
                  envTemp' = define envTemp ident v
                  env' = define env x v
              State.put (False, envs, envTemp', env')
              return $ Left $ Let (Val x (Variable ident)) e2
            else do
              let env' = define env x v
              State.put (flag, envs, envTemp, env')
              return $ Left e2
smallStep (Sequence e1 e2) = do
  e1' <- smallStep e1
  case e1' of
    Left e1'' -> do
      return $ Left $ Sequence e1'' e2
    Right _ -> do
      return $ Left e2
smallStep Fresh = do
  a <- State.lift freshAtmOpSem
  return $ Right $ AtomVal a
smallStep Flip = do
  b <- State.lift $ T $ State.lift $ bernoulli 0.5
  return $ Right $ BoolVal b
smallStep (Eq e1 e2) = do
  (_, _, envT, _) <- State.get
  case e1 of
    Variable x | isJust (maybeFind envT x) -> do
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      e2' <- smallStep e2
      case e2' of
        Left e2'' -> do
          setFlag True
          return $ Left $ Eq (Variable x) e2''
        Right v2 -> do
          restoreEnv
          let v1 = find (envTemp `union` env) x
          return $ Right $ BoolVal $ v1 == v2
    _ -> do
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      e1' <- smallStep e1
      case e1' of
        Left e1'' -> do
          setFlag True
          return $ Left $ Eq e1'' e2
        Right v1 -> do
          restoreEnv
          (_, envs', envTemp', env') <- State.get
          let varName = "eTemp_" ++ show (Environment.length envTemp' 
                      + Environment.length env' + 1)
              ident = Id (varName, typeFromVal v1)
              envTemp'' = define envTemp' ident v1
          State.put (False, envs', envTemp'', env')
          return $ Left $ Eq (Variable ident) e2

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

smallStepIterate :: Int -> Expr a -> EnvVal 
  -> T (ExprOrValue a, (Flag, Maybe [(EnvVal, EnvVal)], EnvVal, EnvVal))
smallStepIterate n expr env = do
  let s0 = (False, Nothing, makeEnv [], env)
  smallStepIterate' n expr s0
  where 
    smallStepIterate' 0 e s@(_, _, envTemp, _) = do 
      e' <- subst e envTemp
      return (Left e', s)
    smallStepIterate' m e s = do
      (e', s') <- State.runStateT (smallStep e) s
      case e' of
        Left e'' -> smallStepIterate' (m - 1) e'' s'
        Right v -> return (Right v, s')


-- using smallStep:
smallStepIterated :: Expr a -> EnvVal -> T (Value a)
smallStepIterated expr env = do 
  let s0 = (False, Nothing, makeEnv [], env)
  -- traceM $ "Step 0: \n" ++ show expr ++ "\n " ++ show s0 ++ "\n\n"
  smallStepIt expr s0
  where 
    smallStepIt e s = do
      (e', s') <- State.runStateT (smallStep e) s
      -- traceM $ "Step " ++ show i ++ ": \n" ++ show e' ++ "\n " ++ show s' ++ "\n\n"
      case e' of
        Left e'' -> smallStepIt e'' s'
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