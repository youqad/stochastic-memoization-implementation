{-# LANGUAGE DataKinds, GADTs, RankNTypes #-}
module RegressionSpec (spec) where

import Test.Hspec
import Control.Exception (evaluate)
import Control.Monad (forM_)
import qualified Data.List as List
import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Syntax
import Environment
import Values
import Semantics

booleanLaw :: Evaluator -> Expr 'TBool -> [(Bool, Double)]
booleanLaw sem e =
  let T ev = sem e initEnv
      values = fmap (\(BoolVal b, _) -> b) $
        State.runStateT ev (initMem, S Map.empty)
      Dist.Cons law = Dist.norm values
  in law

spec :: Spec
spec = do
  expressionSpec
  orderingSpec
  observationSpec
  biasSpec

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
    (u <= v) `shouldBe` True
    compare u v `shouldBe` LT
    compare v u `shouldBe` GT
  it "is reflexive on returned functions" $ do
    let x = Id ("x", 𝔹)
        T ev = bigStep (Lambda x (Variable x)) initEnv
        Dist.Cons outcomes = fmap fst $ State.runStateT ev (initMem, S Map.empty)
    case outcomes of
      [(f, _)] -> do
        (f <= f) `shouldBe` True
        compare f f `shouldBe` EQ
      _ -> expectationFailure "identity closure must have a singleton law"

captured :: Bool -> Expr ('TArrow '[ 'TBool] 'TBool)
captured b =
  let x = Id ("captured", 𝔹)
      y = Id ("argument", 𝔹)
  in Let (Val x (Bool b)) (Lambda y (Variable x))

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
        approx'' (run sem (captured True))
                 (run sem (captured False)) `shouldBe` False
      it "distinguishes biases of memo functions allocated by returned closures" $ do
        let make p = Lambda (Id ("argument", 𝔹)) (MemoBernoulli p)
        approx'' (run sem (make 0)) (run sem (make 1)) `shouldBe` False
      it "retains the two cached-bit outcomes of a returned memo label and atom" $ do
        let e = Pair (MemoBernoulli 0.5) Fresh
            Dist.Cons outcomes = run sem e
        List.length outcomes `shouldBe` 2
        map snd outcomes `shouldBe` [0.5, 0.5]

totalMass :: T a -> Double
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
