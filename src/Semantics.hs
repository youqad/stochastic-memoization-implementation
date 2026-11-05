{-# LANGUAGE GADTs, DataKinds, FlexibleContexts, RankNTypes #-}

module Semantics where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe (isJust, maybeToList)
import Data.Type.Equality ((:~:)(Refl), testEquality)
import Control.Monad (forM_, forM, unless)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State

import Syntax
import Environment
import Values
-- import Text.Pretty.Simple (pPrintString, pShow)

------------------------
-- | PROBABILITY DISTRIBUTIONS
------------------------

validateBias :: RealFloat prob => prob -> ()
validateBias p
  | isNaN p || isInfinite p || p < 0 || p > 1 =
      error "Bernoulli bias must be finite and in [0,1]"
  | otherwise = ()

bernoulli :: RealFloat prob => prob -> Dist.T prob Bool
bernoulli θ = validateBias θ `seq`
  if θ == 0 then return False
  else if θ == 1 then return True
  else Dist.choose θ True False

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
freshFnOpSem θ = validateBias θ `seq` T (do
  (g, S λ) <- State.get
  let (l, g') = freshLeft g
  let λ' = Map.insert l θ λ
  State.put (g', S λ')
  return l)


bigStep :: Expr a -> EnvVal -> T (Value a)
bigStep e env = checkSourceIdents e `seq` bigStepRec e env

bigStepRec :: Expr a -> EnvVal -> T (Value a)
bigStepRec (Atom a) _ = return $ AtomVal a
bigStepRec (Bool b) _ = return $ BoolVal b
bigStepRec (If e1 e2 e3) env = do
  b <- bigStepRec e1 env
  case b of
    BoolVal True -> bigStepRec e2 env
    BoolVal False -> bigStepRec e3 env
bigStepRec (Pair e1 e2) env = do
  v1 <- bigStepRec e1 env
  v2 <- bigStepRec e2 env
  return $ PairVal v1 v2 $ Prod (typeFromVal v1) (typeFromVal v2)
bigStepRec (Match e1 (x1, x2) e2) env = do
  v <- bigStepRec e1 env
  case v of
    PairVal v1 v2 _ -> bigStepRec e2 $ defArgs env fps args
      where
        fps = [This x1, This x2]
        args = [This v1, This v2]
bigStepRec (Variable x) env = return $ find env x
bigStepRec (Lambda xs e1) env = do
  return $ Function
      (\arg -> bigStepRec e1 $ define env xs arg)
      (Lambda xs e1)
      (emptyEnv, env)
      $ typeFromExpr (Lambda xs e1)
bigStepRec (Apply f es) env = do
  fv <- bigStepRec f env
  v <- bigStepRec es env
  case fv of
    Function f' _ _ _ -> f' v
bigStepRec (MemoBernoulli θ) _ = do
  f <- freshFnOpSem θ
  return $ MemoFunction f
bigStepRec (MemoApply f e) env = do
  fv <- bigStepRec f env
  v <- bigStepRec e env
  case (fv, v) of
    (MemoFunction f', AtomVal a) -> BoolVal <$> getOpSem (f', a)
bigStepRec (Eq e1 e2) env = do
  v1 <- bigStepRec e1 env
  v2 <- bigStepRec e2 env
  return $ BoolVal (v1 == v2)
bigStepRec Fresh _ = AtomVal <$> freshAtmOpSem
bigStepRec Flip _ = T $ State.lift $ BoolVal <$> bernoulli 0.5
bigStepRec (Let (Val x e) e1) env = do
  env' <- define env x <$> bigStepRec e env
  bigStepRec e1 env'
bigStepRec (Sequence e1 e2) env =
  bigStepRec e1 env >> bigStepRec e2 env

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

setFlag :: Bool -> 𝒯 ()
setFlag b = do
  (_, envs, envTemp, env) <- State.get
  State.put (b, envs, envTemp, env)

setEnv :: (EnvVal, EnvVal) -> 𝒯 ()
setEnv (envTemp, env) = do
  (flag, envs, _, _) <- State.get
  State.put (flag, envs, envTemp, env)

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

-- | The reserved prefix for machine-generated temporaries. Every temporary
-- the evaluators introduce begins with this character. bigStep, den,
-- smallStepIterate, smallStepIterated, smallStepIteratedTraced and
-- iterateSmallStep reject a source program that uses it (see
-- checkSourceIdents); the recursive workers and smallStep assume a program
-- that has passed that check.
tempPrefix :: String
tempPrefix = "#"

-- | Reject, with a named error, a source program that uses the reserved
-- temporary prefix in any identifier it writes.
checkSourceIdents :: Expr a -> ()
checkSourceIdents e
  | null offenders = ()
  | otherwise = error $
      "source program uses reserved prefix '" ++ tempPrefix
      ++ "' in identifier " ++ show (head offenders)
  where
    offenders = [ name | name <- identNames e, tempPrefix `isPrefixOf` name ]
    isPrefixOf p s = take (length p) s == p
    identNames :: Expr b -> [String]
    identNames (Atom _) = []
    identNames (Bool _) = []
    identNames (If a b c) = identNames a ++ identNames b ++ identNames c
    identNames (Pair a b) = identNames a ++ identNames b
    identNames (Match a (Id (x, _), Id (y, _)) b) =
      identNames a ++ [x, y] ++ identNames b
    identNames (Variable (Id (x, _))) = [x]
    identNames (Lambda (Id (x, _)) b) = x : identNames b
    identNames (Apply f a) = identNames f ++ identNames a
    identNames (MemoBernoulli _) = []
    identNames (MemoApply f a) = identNames f ++ identNames a
    identNames (Eq a b) = identNames a ++ identNames b
    identNames (Let (Val (Id (x, _)) v) b) = x : identNames v ++ identNames b
    identNames (Sequence a b) = identNames a ++ identNames b
    identNames Fresh = []
    identNames Flip = []

-- | Bind a temporary for a value about to be stepped into.
storeTemp :: String -> Value a -> 𝒯 (Ident a)
storeTemp prefix v = do
  (_, envs', envTemp', env') <- State.get
  let varName = tempPrefix ++ prefix ++ show (envSize envTemp'
              + envSize env' + 1)
      ident = Id (varName, typeFromVal v)
      envTemp'' = define envTemp' ident v
  State.put (False, envs', envTemp'', env')
  return ident

-- | Step a subterm; while it is still reducing, rebuild the parent around
-- the reduced subterm (guarded), and once it is a value, bind a fresh
-- temporary for the value and rebuild the parent around its variable.
withTemp :: String -> Expr a
  -> (Expr a -> Expr b)   -- ^ rebuild around a still-reducing subterm
  -> (Ident a -> Expr b)  -- ^ rebuild around the fresh temporary variable
  -> 𝒯 (ExprOrValue b)
withTemp prefix sub onStep onValue = do
  (flag, _, envTemp, env) <- State.get
  unless flag $ addRestore (envTemp, env)
  setFlag False
  sub' <- smallStep sub
  case sub' of
    Left sub'' -> do
      setFlag True
      return $ Left $ onStep sub''
    Right v -> do
      restoreEnv
      ident <- storeTemp prefix v
      return $ Left $ onValue ident

-- smallStep: 
smallStep :: Expr a -> 𝒯 (ExprOrValue a)
smallStep (Atom a) = return $ Right $ AtomVal a
smallStep (Bool b) = return $ Right $ BoolVal b
smallStep (If e1 e2 e3) = do
  (flag, _, envTemp, env) <- State.get
  unless flag $ addRestore (envTemp, env)
  setFlag False
  e1' <- smallStep e1
  case e1' of
    Left e1'' -> do
      setFlag True
      return $ Left $ If e1'' e2 e3
    Right (BoolVal True) -> do
      restoreEnv
      return $ Left e2
    Right (BoolVal False) -> do
      restoreEnv
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
    _ ->
      withTemp "xTemp_" e1
        (\e1'' -> Pair e1'' e2)
        (\ident -> Pair (Variable ident) e2)
smallStep (Match e1 (x1, x2) e2) = do
  e1' <- smallStep e1
  case e1' of
    Left e1'' -> do
      return $ Left $ Match e1'' (x1, x2) e2
    Right (PairVal v1 v2 _) -> do
      (_, toBeRestored, envTemp, env) <- State.get
      let ids = [This x1, This x2]
          vs = [This v1, This v2]
          env' = defArgs env ids vs
      State.put (False, toBeRestored, envTemp, env')
      return $ Left e2
smallStep (Variable x) = do
  (_, _, envTemp, env) <- State.get 
  return $ Right $ find (envTemp `union` env) x
smallStep (Lambda xs e1) = do
  (_, _, envTemp, env) <- State.get
  return $ Right $ Function
        (\arg -> smallStepIterated e1 $ define (envTemp `union` env) xs arg)
        (Lambda xs e1)
        (envTemp, env)
        $ typeFromExpr (Lambda xs e1)
smallStep (Apply f es) = do
  (_, _, envT, _) <- State.get
  case f of
    Variable x | isJust (maybeFind envT x) -> do
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      es' <- smallStep es
      case es' of
        Left e' -> do
          setFlag True
          return $ Left $ Apply (Variable x) e'
        Right v' -> do
          restoreEnv
          let Function _ f' (envTempF, envF) _ = find envT x
          case f' of
            Lambda xs e1 -> do
              (_, _, envTemp', env') <- State.get
              addRestore (envTemp', env')
              let mergedTemp = envTempF `union` envTemp'
                  varName = tempPrefix ++ "xLambdaTemp_" ++ show (envSize mergedTemp
                            + envSize (envF `union` env') + 1)
                  ident = Id (varName, typeFromVal v')
                  envTemp'' = define mergedTemp ident v'
                  env'' = define (envF `union` env') xs v'
              setFlag False
              setEnv (envTemp'', env'')
              return $ Left $ Let (Val xs (Variable ident)) e1
            _ -> error "smallStep: Apply: impossible case"
    _ ->
      withTemp "fTemp_" f
        (\f'' -> Apply f'' es)
        (\ident -> Apply (Variable ident) es)
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
    _ ->
      withTemp "fMemoTemp_" f
        (\f'' -> MemoApply f'' e)
        (\ident -> MemoApply (Variable ident) e)
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
      (flag, _, envTemp, env) <- State.get
      unless flag $ addRestore (envTemp, env)
      setFlag False
      e1' <- smallStep e1
      case e1' of
        Left e1'' -> do
          setFlag True
          return $ Left $ Let (Val x e1'') e2
        Right v -> do
          restoreEnv
          (_, envs, envTemp', env') <- State.get
          let env'' = define env' x v
          State.put (False, envs, envTemp', env'')
          return $ Left e2
smallStep (Sequence e1 e2) = do
  (flag, _, envTemp, env) <- State.get
  unless flag $ addRestore (envTemp, env)
  setFlag False
  e1' <- smallStep e1
  case e1' of
    Left e1'' -> do
      setFlag True
      return $ Left $ Sequence e1'' e2
    Right _ -> do
      restoreEnv
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
    _ ->
      withTemp "eTemp_" e1
        (\e1'' -> Eq e1'' e2)
        (\ident -> Eq (Variable ident) e2)

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
subst (Apply f e) env = Apply <$> subst f env <*> subst e env
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
valueToExpr (Function _ e _ _) = return e
valueToExpr (MemoFunction l) = do
  (_, S λ) <- T State.get
  return $ MemoBernoulli $ λ Map.! l
valueToExpr (PairVal a b _) = (Pair <$> valueToExpr a) <*> valueToExpr b

-- | Transitive closure of small step semantics

smallStepIterate :: Int -> Expr a -> EnvVal
  -> T (ExprOrValue a, (Flag, Maybe [(EnvVal, EnvVal)], EnvVal, EnvVal))
smallStepIterate n expr env = checkSourceIdents expr `seq` do
  let s0 = (False, Nothing, emptyEnv, env)
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
-- One iteration loop. The optional observer is called with the step index
-- and the new expression-or-value and state after each step; it returns a
-- log line that the loop accumulates and returns alongside the value, so
-- the trace is part of the result.
iterateSmallStep ::
  (Int -> ExprOrValue a -> (Flag, Maybe [(EnvVal, EnvVal)], EnvVal, EnvVal) -> Maybe String)
  -> Expr a -> EnvVal -> T (Value a, [String])
iterateSmallStep observe expr env = checkSourceIdents expr `seq` do
  let s0 = (False, Nothing, emptyEnv, env)
      header = observe 0 (Left expr) s0
  smallStepIt 1 expr s0 (maybeToList header)
  where
    smallStepIt i e s acc = do
      (e', s') <- State.runStateT (smallStep e) s
      let acc' = maybe acc (: acc) (observe i e' s')
      case e' of
        Left e'' -> smallStepIt (i + 1) e'' s' acc'
        Right v -> return (v, reverse acc')

-- | The plain small-step iteration, with no per-step observer.
smallStepIterated :: Expr a -> EnvVal -> T (Value a)
smallStepIterated expr env = checkSourceIdents expr `seq`
  fst <$> iterateSmallStep (\_ _ _ -> Nothing) expr env

-- | The traced small-step iteration: the value plus the per-step log, so a
-- caller can render the trace however it chooses, for example in a
-- counterexample string.
smallStepIteratedTraced :: Expr a -> EnvVal -> T (Value a, String)
smallStepIteratedTraced expr env = checkSourceIdents expr `seq` do
  (v, lines') <- iterateSmallStep observe expr env
  return (v, unlines lines')
  where
    observe i e s = Just $
      "Step " ++ show i ++ ": \n" ++ show e ++ "\n " ++ show s ++ "\n"

smallStepIteratedComplete :: Expr a -> EnvVal -> T (Value a)
smallStepIteratedComplete e env = do
  v <- smallStepIterated e env
  completeBigraph
  return v

-- | Denotational Semantics
--
-- getDen samples a memo-table edge the first time it is used and stores the
-- result, as the big-step semantics does, so repeated queries of the same
-- edge return the same bit.
getDen :: (FnLabels, AtmLabels) -> T Bool
getDen (l, r) = T $ do
  (g, S λ) <- State.get
  case contents g (l, r) of
    Just b -> State.lift $ return b
    Nothing -> do
      let θ = λ Map.! l
      b <- State.lift $ bernoulli θ
      State.put (update g (l, r) b, S λ)
      State.lift $ return b

freshAtmDen :: T AtmLabels
freshAtmDen = T $ do
  (g, sλ) <- State.get
  let (r, g') = freshRight g
  State.put (g', sλ)
  return r

freshFnDen :: Double -> T FnLabels
freshFnDen θ = validateBias θ `seq` T (do
  (g, S λ) <- State.get
  let (l, g') = freshLeft g
  let λ' = Map.insert l θ λ
  State.put (g', S λ')
  return l)

den :: Expr a -> EnvVal -> T (Value a)
den e env = checkSourceIdents e `seq` denRec e env

denRec :: Expr a -> EnvVal -> T (Value a)
denRec (Atom a) _ = return $ AtomVal a
denRec (Bool b) _ = return $ BoolVal b
denRec (If e1 e2 e3) env = do
  b <- denRec e1 env
  case b of
    BoolVal True -> denRec e2 env
    BoolVal False -> denRec e3 env
denRec (Pair e1 e2) env = do
  v1 <- denRec e1 env
  v2 <- denRec e2 env
  return $ PairVal v1 v2 $ Prod (typeFromVal v1) (typeFromVal v2)
denRec (Match e1 (x1, x2) e2) env = do
  v <- denRec e1 env
  case v of
    PairVal v1 v2 _ -> denRec e2 $ defArgs env
      [This x1, This x2] [This v1, This v2]
denRec (Variable x) env = return $ find env x
denRec (Apply f es) env = do
  fv <- denRec f env
  v <- denRec es env
  case fv of
    Function f' _ _ _ -> f' v
denRec (Lambda xs e1) env = do
  return $ Function
      (\arg -> denRec e1 $ define env xs arg)
      (Lambda xs e1)
      (emptyEnv, env)
      $ typeFromExpr (Lambda xs e1)
denRec (MemoBernoulli θ) _ = do
  f <- freshFnDen θ
  return $ MemoFunction f
denRec (MemoApply f e) env = do
  fv <- denRec f env
  v <- denRec e env
  case (fv, v) of
    (MemoFunction f', AtomVal a) -> BoolVal <$> getDen (f', a)
denRec (Eq e1 e2) env = do
  v1 <- denRec e1 env
  v2 <- denRec e2 env
  return $ BoolVal (v1 == v2)
denRec Fresh _ = AtomVal <$> freshAtmDen
denRec Flip _ = T $ State.lift $ BoolVal <$> bernoulli 0.5
denRec (Let (Val x e) e1) env = do
  env' <- define env x <$> denRec e env
  denRec e1 env'
denRec (Sequence e1 e2) env =
  denRec e1 env >> denRec e2 env


------------------------
-- | TESTS
------------------------

simplify :: (Eq (LeftNode t), Show (LeftNode t)) =>
  (a, (MemoBigraph (LeftNode t) r b, StateOfBiases t))
  -> (a, [(LeftNode t, Double)], [r], [((LeftNode t, r), b)])
simplify (b, (Mem ((l, r), m), S λ))
  | Set.toList l == Map.keys λ =
      (b, Map.toList λ, Set.toList r, Map.toList m)
  | otherwise = error $
      "allocated function labels " ++ show (Set.toList l)
      ++ " differ from bias-map keys " ++ show (Map.keys λ)

-- These are finite application observations, not extensional function equality.
-- The result contains no closure syntax or existential environment equality.
data Observation
  = ObservedBool Bool
  | ObservedAtom AtmLabels [(FnLabels, Bool)]
  | ObservedMemo FnLabels Double [(AtmLabels, Bool)]
  | ObservedPair Observation Observation
  | ObservedFunction Int Observation
  deriving (Eq, Ord, Show)

type Evaluator = forall a. Expr a -> EnvVal -> T (Value a)

observeValue :: Evaluator -> Value a -> T Observation
observeValue _ (BoolVal b) = return $ ObservedBool b
observeValue _ (AtomVal a) = do
  (Mem ((functions, _), _), _) <- T State.get
  column <- forM (Set.toAscList functions) $ \f -> do
    bit <- getOpSem (f, a)
    return (f, bit)
  return $ ObservedAtom a column
observeValue _ (MemoFunction f) = do
  (Mem ((_, atoms), _), S biases) <- T State.get
  row <- forM (Set.toAscList atoms) $ \a -> do
    bit <- getOpSem (f, a)
    return (a, bit)
  return $ ObservedMemo f (biases Map.! f) row
observeValue sem (PairVal a b _) =
  ObservedPair <$> observeValue sem a <*> observeValue sem b
observeValue sem (Function f _ _ (Arr a _)) = do
  choices <- probeChoices sem a
  (index, action) <- T $ State.lift $ Dist.uniform $ zip [0..] choices
  -- Apply twice to the same argument: the pair of results records the
  -- correlation between calls, which separates a stored bit from a fresh
  -- bit when their single-call distributions agree.
  argument <- action
  result1 <- f argument >>= observeValue sem
  result2 <- f argument >>= observeValue sem
  return $ ObservedFunction index (ObservedPair result1 result2)

-- Enumerate an exact uniform mixture of labelled application contexts.
-- Each branch runs one argument in its own state: unrelated probes
-- must not allocate a Cartesian product of unused memo-table entries.
-- Atom probes cover allocated atoms and one fresh atom. Memo probes cover
-- allocated labels and new labels at 0, 1/2 and 1. Products use all pairs;
-- higher-order arguments use closed constants and the typed identity.
probeChoices :: Evaluator -> Typey a -> T [T (Value a)]
probeChoices _ 𝔹 = return $ map return [BoolVal False, BoolVal True]
probeChoices sem 𝔸 = do
  (Mem ((_, atoms), _), _) <- T State.get
  return $ map (return . AtomVal) (Set.toAscList atoms) ++ [sem Fresh initEnv]
probeChoices sem MemFn = do
  (Mem ((labels, _), _), _) <- T State.get
  return $ map (return . MemoFunction) (Set.toAscList labels)
    ++ map (\p -> sem (MemoBernoulli p) initEnv) [0, 0.5, 1]
probeChoices sem (Prod a b) = do
  left <- probeChoices sem a
  right <- probeChoices sem b
  return [PairVal <$> x <*> y <*> pure (Prod a b) | x <- left, y <- right]
probeChoices sem t@(Arr _ _) = return $ map (\e -> sem e initEnv) (closedProbes t)

closedProbes :: Typey a -> [Expr a]
closedProbes 𝔹 = [Bool False, Bool True]
closedProbes 𝔸 = [Fresh]
closedProbes MemFn = map MemoBernoulli [0, 0.5, 1]
closedProbes (Prod a b) = [Pair x y | x <- closedProbes a, y <- closedProbes b]
closedProbes (Arr a b) =
  let x = Id ("observation_argument", a)
      constants = map (Lambda x) (closedProbes b)
  in case testEquality a b of
    Just Refl -> Lambda x (Variable x) : constants
    Nothing -> constants

type ObservedOutcome =
  (Observation, [(FnLabels, Double)], [AtmLabels], [((FnLabels, AtmLabels), Bool)])

run :: Evaluator -> Expr a -> Dist ObservedOutcome
run sem e =
  let T ev = do
        value <- sem e initEnv
        completeBigraph
        originalState <- T State.get
        observation <- observeValue sem value
        return $ simplify (observation, originalState)
      res = State.evalStateT ev (initMem, S Map.empty)
  in Dist.norm res

-- | Run an evaluator on a closed boolean expression against the standard
-- initial state and return its normalized boolean law.
runBooleanLaw :: (Expr 'TBool -> EnvVal -> T (Value 'TBool))
  -> Expr 'TBool -> [(Bool, Double)]
runBooleanLaw sem e =
  let T ev = sem e initEnv
      values = fmap (\(BoolVal b, _) -> b) $
        State.runStateT ev (initMem, S Map.empty)
      Dist.Cons law = Dist.norm values
  in law
