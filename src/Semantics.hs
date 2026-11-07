{-# LANGUAGE GADTs, DataKinds, FlexibleContexts, RankNTypes #-}

-- small-step intermediate expressions may contain generated identifiers
module Semantics
  (
    validateBias
  , bernoulli
  , bigStep
  , bigStepComplete
  , bigStepRec
  , completeBigraph
  , getOpSem
  , freshAtmOpSem
  , freshFnOpSem
  , smallStep
  , smallStepIterated
  , smallStepIteratedTraced
  , smallStepIteratedComplete
  , iterateSmallStep
  , setEnv
  , addRestore
  , restoreEnv
  , den
  , denRec
  , getDen
  , freshAtmDen
  , freshFnDen
  , Observation (..)
  , ObservedOutcome
  , Evaluator
  , ExprOrValue
  , 𝒯
  , observeValue
  , probeChoices
  , closedProbes
  , simplify
  , run
  , runBooleanLaw
  ) where

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Maybe (isJust, maybeToList)
import Data.Type.Equality ((:~:)(Refl))
import Control.Monad (forM_, forM, when, foldM)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State

import Syntax
import Ident
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

bernoulli :: Double -> Dist.T Rational Bool
bernoulli θ = validateBias θ `seq`
  if θ == 0 then return False
  else if θ == 1 then return True
  else Dist.choose (toRational θ) True False

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
bigStep e env = bigStepRec e env

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




type 𝒯 x = State.StateT ([(EnvVal, EnvVal)], EnvVal, EnvVal) T x
-- [(EnvVal, EnvVal)] is the restoration stack of (envTemp, env) environments to restore once we hit a value 
-- EnvVal, EnvVal: envTemp, env: an extra environment envTemp for temporary variables (to store values that need to be remembered while evaluating the expression), and the current environment env

setEnv :: (EnvVal, EnvVal) -> 𝒯 ()
setEnv (envTemp, env) = do
  (envs, _, _) <- State.get
  State.put (envs, envTemp, env)

addRestore :: (EnvVal, EnvVal) -> 𝒯 ()
addRestore frame =
  State.modify (\(envs, envTemp, env) -> (frame : envs, envTemp, env))

restoreEnv :: 𝒯 ()
restoreEnv = do
  (toBeRestored, _, _) <- State.get
  case toBeRestored of
    (envTemp', env') : envs -> State.put (envs, envTemp', env')
    [] -> return ()

storeTemp :: String -> Value a -> 𝒯 (Ident a)
storeTemp prefix v = do
  (envs', envTemp', env') <- State.get
  let varName = prefix ++ show (envSize envTemp'
              + envSize env' + 1)
      ident = Gen (varName, typeFromVal v)
      envTemp'' = define envTemp' ident v
  State.put (envs', envTemp'', env')
  return ident

withTemp :: Int -> String -> Expr a
  -> (Expr a -> Expr b)   -- ^ rebuild around a reducing subterm
  -> (Ident a -> Expr b)  -- ^ rebuild around a temporary variable
  -> 𝒯 (ExprOrValue b)
withTemp d prefix sub onStep onValue =
  withRestore d sub onStep $ \v -> do
    ident <- storeTemp prefix v
    return $ Left $ onValue ident

-- spine depth d: number of enclosing constructs that are reducing a subterm,
-- counted from the whole expression (depth 0). The stack holds at most one frame
-- per depth: at depth d, push if it has at most d frames, pop once sub is a value
withRestore :: Int -> Expr a
  -> (Expr a -> Expr b)
  -> (Value a -> 𝒯 (ExprOrValue b))
  -> 𝒯 (ExprOrValue b)
withRestore d sub onStep onValue = do
  (envs, envTemp, env) <- State.get
  when (length envs <= d) $ addRestore (envTemp, env)
  sub' <- smallStepAt (d + 1) sub
  case sub' of
    Left sub'' -> do
      return $ Left $ onStep sub''
    Right v -> do
      restoreEnv
      onValue v

-- smallStep:
smallStep :: Expr a -> 𝒯 (ExprOrValue a)
smallStep = smallStepAt 0

smallStepAt :: Int -> Expr a -> 𝒯 (ExprOrValue a)
smallStepAt _ (Atom a) = return $ Right $ AtomVal a
smallStepAt _ (Bool b) = return $ Right $ BoolVal b
smallStepAt d (If e1 e2 e3) =
  withRestore d e1 (\e1'' -> If e1'' e2 e3) $ \v -> case v of
    BoolVal True -> return $ Left e2
    BoolVal False -> return $ Left e3
smallStepAt d (Pair e1 e2) = do
  (_, envT, _) <- State.get
  case e1 of
    Variable x | isJust (maybeFind envT x) ->
      withRestore d e2 (\e2'' -> Pair (Variable x) e2'') $ \v2 -> do
        (_, envTemp, env) <- State.get
        let v1 = find (envTemp `union` env) x
        return $ Right $ PairVal v1 v2
          $ Prod (typeFromVal v1) (typeFromVal v2)
    _ ->
      withTemp d "xTemp_" e1
        (\e1'' -> Pair e1'' e2)
        (\ident -> Pair (Variable ident) e2)
smallStepAt d (Match e1 (x1, x2) e2) =
  withRestore d e1 (\e1'' -> Match e1'' (x1, x2) e2) $ \v -> case v of
    PairVal v1 v2 _ -> do
      (envs, envTemp', env') <- State.get
      let ids = [This x1, This x2]
          vs = [This v1, This v2]
          env'' = defArgs env' ids vs
      State.put (envs, envTemp', env'')
      return $ Left e2
smallStepAt _ (Variable x) = do
  (_, envTemp, env) <- State.get
  return $ Right $ find (envTemp `union` env) x
smallStepAt _ (Lambda xs e1) = do
  (_, envTemp, env) <- State.get
  return $ Right $ Function
        (\arg -> smallStepIterated e1 $ define (envTemp `union` env) xs arg)
        (Lambda xs e1)
        (envTemp, env)
        $ typeFromExpr (Lambda xs e1)
smallStepAt d (Apply f es) = do
  (_, envT, _) <- State.get
  case f of
    Variable x | isJust (maybeFind envT x) ->
      withRestore d es (\e' -> Apply (Variable x) e') $ \v' -> do
        (_, envT', _) <- State.get
        let Function _ f' (envTempF, envF) _ = find envT' x
        case f' of
          Lambda xs e1 -> do
            (_, envTemp', env') <- State.get
            addRestore (envTemp', env')
            let mergedTemp = envTempF `union` envTemp'
                varName = "xLambdaTemp_" ++ show (envSize mergedTemp
                          + envSize (envF `union` env') + 1)
                ident = Gen (varName, typeFromVal v')
                envTemp'' = define mergedTemp ident v'
                env'' = define (envF `union` env') xs v'
            setEnv (envTemp'', env'')
            return $ Left $ Let (Val xs (Variable ident)) e1
          _ -> error "smallStepAt: Apply: impossible case"
    _ ->
      withTemp d "fTemp_" f
        (\f'' -> Apply f'' es)
        (\ident -> Apply (Variable ident) es)
smallStepAt _ (MemoBernoulli θ) = do
  f <- State.lift $ freshFnOpSem θ
  return $ Right $ MemoFunction f
smallStepAt d (MemoApply f e) = do
  (_, envT, _) <- State.get
  case f of
    Variable x | isJust (maybeFind envT x) ->
      withRestore d e (\e'' -> MemoApply (Variable x) e'') $ \v -> case v of
        AtomVal a -> do
          (_, envTemp', env') <- State.get
          let MemoFunction f' = find (envTemp' `union` env') x
          b <- State.lift $ getOpSem (f', a)
          return $ Right $ BoolVal b
    _ ->
      withTemp d "fMemoTemp_" f
        (\f'' -> MemoApply f'' e)
        (\ident -> MemoApply (Variable ident) e)
smallStepAt d (Let (Val x e1) e2) = do
  (_, envT, _) <- State.get
  case e1 of
    Variable y | isJust (maybeFind envT y) -> do
      -- lambda body from Apply (which pushed the caller's frame at depth d)
      e2' <- smallStepAt (d + 1) e2
      case e2' of
        Left e2'' -> do
          return $ Left $ Let (Val x e1) e2''
        Right v -> do
          restoreEnv
          return $ Right v
    _ ->
      withRestore d e1 (\e1'' -> Let (Val x e1'') e2) $ \v -> do
        (envs, envTemp', env') <- State.get
        let env'' = define env' x v
        State.put (envs, envTemp', env'')
        return $ Left e2
smallStepAt d (Sequence e1 e2) =
  withRestore d e1 (\e1'' -> Sequence e1'' e2) (\_ -> return $ Left e2)
smallStepAt _ Fresh = do
  a <- State.lift freshAtmOpSem
  return $ Right $ AtomVal a
smallStepAt _ Flip = do
  b <- State.lift $ T $ State.lift $ bernoulli 0.5
  return $ Right $ BoolVal b
smallStepAt d (Eq e1 e2) = do
  (_, envT, _) <- State.get
  case e1 of
    Variable x | isJust (maybeFind envT x) ->
      withRestore d e2 (\e2'' -> Eq (Variable x) e2'') $ \v2 -> do
        (_, envTemp, env) <- State.get
        let v1 = find (envTemp `union` env) x
        return $ Right $ BoolVal $ v1 == v2
    _ ->
      withTemp d "eTemp_" e1
        (\e1'' -> Eq e1'' e2)
        (\ident -> Eq (Variable ident) e2)

-- using smallStep:
iterateSmallStep ::
  (Int -> ExprOrValue a -> ([(EnvVal, EnvVal)], EnvVal, EnvVal) -> Maybe String)
  -> Expr a -> EnvVal -> T (Value a, [String])
iterateSmallStep observe expr env = do
  let s0 = ([], emptyEnv, env)
      header = observe 0 (Left expr) s0
  smallStepIt 1 expr s0 (maybeToList header)
  where
    smallStepIt i e s acc = do
      (e', s') <- State.runStateT (smallStep e) s
      let acc' = maybe acc (: acc) (observe i e' s')
      case e' of
        Left e'' -> smallStepIt (i + 1) e'' s' acc'
        Right v -> return (v, reverse acc')

smallStepIterated :: Expr a -> EnvVal -> T (Value a)
smallStepIterated expr env =
  fst <$> iterateSmallStep (\_ _ _ -> Nothing) expr env

smallStepIteratedTraced :: Expr a -> EnvVal -> T (Value a, String)
smallStepIteratedTraced expr env = do
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
getDen :: (FnLabels, AtmLabels) -> T Bool
getDen (l, r) = T $ do
  (g, _) <- State.get
  case contents g (l, r) of
    Just b -> State.lift $ return b
    Nothing -> error $
      "no memo-table entry for function " ++ show l ++ " and atom " ++ show r

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
freshFnDen θ = validateBias θ `seq` T (do
  (g, S λ) <- State.get
  let (l, g'@(Mem ((_, rs), _))) = freshLeft g
  gNew <- State.lift $
    foldM (\g'' r -> update g'' (l, r)
      <$> bernoulli θ)
    g' rs
  let λ' = Map.insert l θ λ
  State.put (gNew, S λ')
  return l)

den :: Expr a -> EnvVal -> T (Value a)
den e env = denRec e env

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

runBooleanLaw :: (Expr 'TBool -> EnvVal -> T (Value 'TBool))
  -> Expr 'TBool -> [(Bool, Rational)]
runBooleanLaw sem e =
  let T ev = sem e initEnv
      values = fmap (\(BoolVal b, _) -> b) $
        State.runStateT ev (initMem, S Map.empty)
      Dist.Cons law = Dist.norm values
  in law
