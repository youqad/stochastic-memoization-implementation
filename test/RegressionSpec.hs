{-# LANGUAGE DataKinds, GADTs, RankNTypes #-}
module RegressionSpec (spec) where

import Test.Hspec
import Control.Exception (ErrorCall (ErrorCall), evaluate)
import Control.Monad (forM_)
import Data.Ratio ((%))
import qualified Data.List as List
import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Syntax
import Environment
import Values
import Semantics

booleanLaw :: Evaluator -> Expr 'TBool -> [(Bool, Rational)]
booleanLaw = runBooleanLaw

spec :: Spec
spec = do
  expressionSpec
  orderingSpec
  observationSpec
  biasSpec
  simplifySpec
  defArgsSpec
  eagerSpec
  functionEqSpec

runKeepingTable :: Evaluator -> Expr a -> Dist.T Rational (Value a, MemDen)
runKeepingTable sem e =
  let T ev = do
        v <- sem e initEnv
        (g, _) <- T State.get
        return (v, g)
  in State.evalStateT ev (initMem, S Map.empty)

tableEdges :: MemDen -> [((FnLabels, AtmLabels), Bool)]
tableEdges (Mem ((_, _), edges)) = Map.toList edges

eagerSpec :: Spec
eagerSpec = describe "denotational table allocation" $ do
  describe "function and atom allocation before application" $ do
    let fnThenAtom p =
          Let (Val (Id ("m", MemFn)) (MemoBernoulli p)) $
          Let (Val (Id ("a", 𝔸)) Fresh) $
            Pair (Variable (Id ("m", MemFn))) (Variable (Id ("a", 𝔸)))
        atomThenFn p =
          Let (Val (Id ("a", 𝔸)) Fresh) $
          Let (Val (Id ("m", MemFn)) (MemoBernoulli p)) $
            Pair (Variable (Id ("a", 𝔸))) (Variable (Id ("m", MemFn)))
    it "entry before application in denotational vs big-step" $ do
      let denOutcomes = Dist.decons (Dist.norm (runKeepingTable den (fnThenAtom 0.5)))
          denTable = [ (tableEdges g, p) | ((_, g), p) <- denOutcomes ]
      denTable `shouldBe` [ ([((Fn 0, Atm 0), False)], 1 % 2)
                          , ([((Fn 0, Atm 0), True)],  1 % 2) ]
      let bigOutcomes = Dist.decons (Dist.norm (runKeepingTable bigStep (fnThenAtom 0.5)))
          bigTable = [ (tableEdges g, p) | ((_, g), p) <- bigOutcomes ]
      bigTable `shouldBe` [ ([], 1 % 1) ]
    it "atom allocated before function" $ do
      let denOutcomes = Dist.decons (Dist.norm (runKeepingTable den (atomThenFn 0.5)))
          denTable = [ (tableEdges g, p) | ((_, g), p) <- denOutcomes ]
      denTable `shouldBe` [ ([((Fn 0, Atm 0), False)], 1 % 2)
                          , ([((Fn 0, Atm 0), True)],  1 % 2) ]
    it "entry at bias 1/4" $ do
      let denOutcomes = Dist.decons (Dist.norm (runKeepingTable den (fnThenAtom 0.25)))
          denTable = [ (tableEdges g, p) | ((_, g), p) <- denOutcomes ]
      denTable `shouldBe` [ ([((Fn 0, Atm 0), False)], 3 % 4)
                          , ([((Fn 0, Atm 0), True)],  1 % 4) ]
    it "new function at existing atoms" $ do
      let denOutcomes = Dist.decons (Dist.norm (runKeepingTable den (atomThenFn 0.25)))
          denTable = [ (tableEdges g, p) | ((_, g), p) <- denOutcomes ]
      denTable `shouldBe` [ ([((Fn 0, Atm 0), False)], 3 % 4)
                          , ([((Fn 0, Atm 0), True)],  1 % 4) ]
  it "fresh atom with different function biases" $ do
    let e = Let (Val (Id ("f1", MemFn)) (MemoBernoulli 0.5)) $
            Let (Val (Id ("f2", MemFn)) (MemoBernoulli 0.25)) $
            Let (Val (Id ("a", 𝔸)) Fresh) $
              Bool True
        outcomes = Dist.decons (Dist.norm (runKeepingTable den e))
        table = [ (tableEdges g, p) | ((_, g), p) <- outcomes ]
    table `shouldBe`
      [ ([((Fn 0, Atm 0), False), ((Fn 1, Atm 0), False)], 3 % 8)
      , ([((Fn 0, Atm 0), False), ((Fn 1, Atm 0), True)],  1 % 8)
      , ([((Fn 0, Atm 0), True),  ((Fn 1, Atm 0), False)], 3 % 8)
      , ([((Fn 0, Atm 0), True),  ((Fn 1, Atm 0), True)],  1 % 8) ]
  it "new function with two existing atoms" $ do
    let e = Let (Val (Id ("a1", 𝔸)) Fresh) $
            Let (Val (Id ("a2", 𝔸)) Fresh) $
            Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.25)) $
              Bool True
        outcomes = Dist.decons (Dist.norm (runKeepingTable den e))
        table = [ (tableEdges g, p) | ((_, g), p) <- outcomes ]
    table `shouldBe`
      [ ([((Fn 0, Atm 0), False), ((Fn 0, Atm 1), False)], 9 % 16)
      , ([((Fn 0, Atm 0), False), ((Fn 0, Atm 1), True)],  3 % 16)
      , ([((Fn 0, Atm 0), True),  ((Fn 0, Atm 1), False)], 3 % 16)
      , ([((Fn 0, Atm 0), True),  ((Fn 0, Atm 1), True)],  1 % 16) ]
  it "getDen: repeated reads and unchanged entry" $ do
    let T ev = do
          f <- freshFnDen 0.5
          a <- freshAtmDen
          (before, _) <- T State.get
          b1 <- getDen (f, a)
          b2 <- getDen (f, a)
          (after, _) <- T State.get
          return (contents before (f, a), b1, b2, contents after (f, a))
        outcomes = Dist.decons (Dist.norm (State.evalStateT ev (initMem, S Map.empty)))
    outcomes `shouldBe`
      [ ((Just False, False, False, Just False), 1 % 2)
      , ((Just True,  True,  True,  Just True),  1 % 2) ]
  it "repeated application: same bit and table entry" $ do
    let e = Let (Val (Id ("m", MemFn)) (MemoBernoulli 0.5)) $
            Let (Val (Id ("a", 𝔸)) Fresh) $
              Pair
                (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a", 𝔸))))
                (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a", 𝔸))))
        outcomes = Dist.decons (Dist.norm (runKeepingTable den e))
        readBack =
          [ ((b1, b2), entry, p)
          | ((PairVal (BoolVal b1) (BoolVal b2) _, g), p) <- outcomes
          , let entry = tableEdges g ]
    readBack `shouldBe`
      [ ((False, False), [((Fn 0, Atm 0), False)], 1 % 2)
      , ((True,  True),  [((Fn 0, Atm 0), True)],  1 % 2) ]

defArgsSpec :: Spec
defArgsSpec = describe "binding function arguments" $ do
  it "too few arguments rejected" $ do
    let fps = [This (Id ("x", 𝔹)), This (Id ("y", 𝔹))]
        args = [This (BoolVal True)]
    evaluate (forceEnv (defArgs initEnv fps args)) `shouldThrow` anyErrorCall
  it "type error names the variable and both types" $ do
    let fps = [This (Id ("flag", 𝔹))]
        args = [This (AtomVal (Atm 0))]
        env = defArgs initEnv fps args
    evaluate (find env (Id ("flag", 𝔹)))
      `shouldThrow` (errorCallsWithFragments
        ["flag", "TBool", "TAtom"])
  it "first duplicate binding" $ do
    let x = Id ("x", 𝔹)
        env = makeEnv [(x, BoolVal True), (x, BoolVal False)] :: EnvVal
    find env x `shouldBe` BoolVal True
  where
    forceEnv env = envSize env `seq` env
    errorCallsWithFragments fragments (ErrorCall msg) =
      all (`List.isInfixOf` msg) fragments

simplifySpec :: Spec
simplifySpec = describe "simplifying evaluator states" $ do
  it "missing function bias raises an error" $ do
    let (_, table) = freshLeft (initMem :: MemDen)
        inconsistent = (table, S Map.empty :: StateOfBiases MemDen)
    evaluate (simplify ((), inconsistent)) `shouldThrow` anyErrorCall
  it "repeated reads of a cached bit" $ do
    let e = Let (Val (Id ("m", MemFn)) (MemoBernoulli 0.5)) $
              Let (Val (Id ("a", 𝔸)) Fresh) $
                Pair
                  (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a", 𝔸))))
                  (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a", 𝔸))))
    jointLaw den e `shouldBe` [((False, False), 0.5), ((True, True), 0.5)]
    where
      jointLaw :: Evaluator
        -> Expr ('TProduct 'TBool 'TBool) -> [((Bool, Bool), Rational)]
      jointLaw sem e =
        let T ev = sem e initEnv
            values = fmap fst $ State.runStateT ev (initMem, S Map.empty)
            Dist.Cons outcomes = Dist.norm values
        in map (\(PairVal (BoolVal b1) (BoolVal b2) _, p) -> ((b1, b2), p)) outcomes

expressionSpec :: Spec
expressionSpec = describe "Expression structure" $ do
  let namedTrue = Id ("True", 𝔹)
      literal = Bool True
      variable = Variable namedTrue
      constant = Lambda namedTrue literal
      identity = Lambda namedTrue variable
  it "distinguishes a literal from an identically printed variable" $ do
    show literal `shouldBe` show variable
    (literal == variable) `shouldBe` False
  it "keeps identically printed expressions distinct in ordered sets" $ do
    Set.size (Set.fromList [literal, variable]) `shouldBe` 2
  it "retains the types of existentially hidden identifiers" $ do
    let boolSequence = Sequence (Variable (Id ("x", 𝔹))) (Bool True)
        atomSequence = Sequence (Variable (Id ("x", 𝔸))) (Bool True)
    show boolSequence `shouldBe` show atomSequence
    (boolSequence == atomSequence) `shouldBe` False
    compare boolSequence atomSequence `shouldNotBe` EQ
  let closureCase :: String -> Evaluator -> Spec
      closureCase name sem = it ("distinguishes colliding closures in " ++ name) $ do
        booleanLaw sem (Apply constant (Bool False)) `shouldBe` [(True, 1)]
        booleanLaw sem (Apply identity (Bool False)) `shouldBe` [(False, 1)]
        booleanLaw sem (Eq constant identity) `shouldBe` [(False, 1)]
  closureCase "big-step equality" bigStep
  closureCase "small-step equality" smallStepIterated
  closureCase "denotational equality" den

orderingSpec :: Spec
orderingSpec = describe "Value ordering" $ do
  it "orders pairs lexicographically" $ do
    let u = PairVal (BoolVal False) (BoolVal True) (Prod 𝔹 𝔹)
        v = PairVal (BoolVal True) (BoolVal False) (Prod 𝔹 𝔹)
    compare u v `shouldBe` LT
    compare v u `shouldBe` GT
  it "is reflexive on returned functions" $ do
    let x = Id ("x", 𝔹)
        T ev = bigStep (Lambda x (Variable x)) initEnv
        Dist.Cons outcomes = fmap fst $ State.runStateT ev (initMem, S Map.empty)
    case outcomes of
      [(f, _)] ->
        compare f f `shouldBe` EQ
      _ -> expectationFailure "identity closure must have a singleton law"

captured :: Bool -> Expr ('TArrow '[ 'TBool] 'TBool)
captured b =
  let x = Id ("captured", 𝔹)
      y = Id ("argument", 𝔹)
  in Let (Val x (Bool b)) (Lambda y (Variable x))

functionEqSpec :: Spec
functionEqSpec = describe "equality and behaviour of functions" $ do
  it "equal expressions with different captures" $ do
    booleanLaw bigStep (Eq (captured True) (captured False))
      `shouldBe` [(True, 1)]
  it "application with different captures" $ do
    booleanLaw bigStep (Apply (captured True) (Bool False))
      `shouldBe` [(True, 1)]
    booleanLaw bigStep (Apply (captured False) (Bool False))
      `shouldBe` [(False, 1)]

observationSpec :: Spec
observationSpec = describe "Returned observations" $ do
  observationCases "big-step" bigStepComplete
  observationCases "small-step" smallStepIteratedComplete
  observationCases "denotational" den
  where
    observationCases :: String -> Evaluator -> Spec
    observationCases name sem = describe name $ do
      it "distinguishes the environments of identically written closures" $ do
        booleanLaw sem (Apply (captured True) (Bool False)) `shouldBe` [(True, 1)]
        booleanLaw sem (Apply (captured False) (Bool False)) `shouldBe` [(False, 1)]
        Dist.equal (run sem (captured True))
                    (run sem (captured False)) `shouldBe` False
      it "distinguishes biases of memo functions allocated by returned closures" $ do
        let make p = Lambda (Id ("argument", 𝔹)) (MemoBernoulli p)
        Dist.equal (run sem (make 0)) (run sem (make 1)) `shouldBe` False
      it "retains the two cached-bit outcomes of a returned memo label and atom" $ do
        let e = Pair (MemoBernoulli 0.5) Fresh
            Dist.Cons outcomes = run sem e
        length outcomes `shouldBe` 2
        map snd outcomes `shouldBe` [0.5, 0.5]
      it "second call: stored vs fresh bits" $ do
        let correlated =
              Let (Val (Id ("m", MemFn)) (MemoBernoulli 0.5)) $
                Lambda (Id ("argument", 𝔸))
                  (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("argument", 𝔸))))
            independent =
              Let (Val (Id ("m", MemFn)) (MemoBernoulli 0.5)) $
                Lambda (Id ("argument", 𝔸))
                  (MemoApply (Variable (Id ("m", MemFn))) Fresh)
        Dist.equal (run sem correlated) (run sem independent) `shouldBe` False
      it "product argument: shared vs fresh atoms" $ do
        let h = Id ("h", Arr (Prod 𝔸 𝔸) 𝔹)
            arg = Id ("argument", Prod 𝔸 𝔸)
            x1 = Id ("x1", 𝔸)
            x2 = Id ("x2", 𝔸)
            body = Match (Variable arg) (x1, x2) (Variable x1 `Eq` Variable x2)
            diagonal =
              Let (Val h (Lambda arg body)) $
                Let (Val (Id ("a", 𝔸)) Fresh) $
                  Apply (Variable h) (Pair (Variable (Id ("a", 𝔸))) (Variable (Id ("a", 𝔸))))
            offDiagonal =
              Let (Val h (Lambda arg body)) $
                Apply (Variable h) (Pair Fresh Fresh)
        booleanLaw sem diagonal `shouldBe` [(True, 1)]
        booleanLaw sem offDiagonal `shouldBe` [(False, 1)]
        Dist.equal (run sem diagonal) (run sem offDiagonal) `shouldBe` False

totalMass :: T a -> Rational
totalMass (T ev) =
  let Dist.Cons outcomes = State.runStateT ev (initMem, S Map.empty)
  in sum $ map snd outcomes

invalidBiases :: [(String, Double)]
invalidBiases = [("negative", -0.1), ("above one", 1.1),
  ("NaN", 0/0), ("positive infinity", 1/0), ("negative infinity", -1/0)]

biasSpec :: Spec
biasSpec = describe "Bias validation" $ do
  biasCases "big-step" bigStep
  biasCases "small-step" smallStepIterated
  biasCases "denotational" den
  forM_ invalidBiases $ \(name, p) ->
    it ("rejects " ++ name ++ " in the Bernoulli primitive") $
      evaluate (let Dist.Cons xs = bernoulli p in sum (map snd xs))
        `shouldThrow` anyErrorCall
  where
    biasCases :: String -> Evaluator -> Spec
    biasCases name sem = describe name $ do
      forM_ invalidBiases $ \(label, p) ->
        it ("rejects " ++ label ++ " before allocating an unused memo function") $
          evaluate (totalMass $ sem (MemoBernoulli p) initEnv)
            `shouldThrow` anyErrorCall
      forM_ [(0, False), (1, True)] $ \(p, bit) ->
        it ("accepts the endpoint " ++ show p) $
          booleanLaw sem (MemoApply (MemoBernoulli p) Fresh)
            `shouldBe` [(bit, 1)]
