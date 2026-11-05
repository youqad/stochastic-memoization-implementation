{-# LANGUAGE DataKinds, GADTs, RankNTypes #-}
module RegressionSpec (spec) where

import Test.Hspec
import Control.Exception (ErrorCall (ErrorCall), evaluate)
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
booleanLaw = runBooleanLaw

spec :: Spec
spec = do
  expressionSpec
  orderingSpec
  observationSpec
  biasSpec
  simplifySpec
  defArgsSpec

defArgsSpec :: Spec
defArgsSpec = describe "Definition of arguments" $ do
  it "rejects fewer arguments than parameters instead of dropping some" $ do
    let fps = [This (Id ("x", 𝔹)), This (Id ("y", 𝔹))]
        args = [This (BoolVal True)]
    evaluate (forceEnv (defArgs initEnv fps args)) `shouldThrow` anyErrorCall
  it "names the ident and both types on a type mismatch" $ do
    let fps = [This (Id ("flag", 𝔹))]
        args = [This (AtomVal (Atm 0))]
        env = defArgs initEnv fps args
    evaluate (find env (Id ("flag", 𝔹)))
      `shouldThrow` (errorCallsWithFragments
        ["flag", "TBool", "TAtom"])
  where
    forceEnv env = envSize env `seq` env
    errorCallsWithFragments fragments (ErrorCall msg) =
      all (`List.isInfixOf` msg) fragments

simplifySpec :: Spec
simplifySpec = describe "Simplified states" $ do
  it "fails loudly when the bias map is missing an allocated function" $ do
    let (_, table) = freshLeft (initMem :: MemDen)
        inconsistent = (table, S Map.empty :: StateOfBiases MemDen)
    evaluate (simplify ((), inconsistent)) `shouldThrow` anyErrorCall
  it "returns the same cached bit on two queries of one key" $ do
    -- A memo-table bit is sampled once and stored, so two queries of the
    -- same (function, atom) key always agree. At bias 1/2 the joint law is
    -- (False,False) and (True,True) with mass 1/2 each and the mixed pairs
    -- with mass 0.
    let e = Let (Val (Id ("m", MemFn)) (MemoBernoulli 0.5)) $
              Let (Val (Id ("a", 𝔸)) Fresh) $
                Pair
                  (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a", 𝔸))))
                  (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a", 𝔸))))
    jointLaw den e `shouldBe` [((False, False), 0.5), ((True, True), 0.5)]
    where
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
        Dist.approx (run sem (captured True))
                    (run sem (captured False)) `shouldBe` False
      it "distinguishes biases of memo functions allocated by returned closures" $ do
        let make p = Lambda (Id ("argument", 𝔹)) (MemoBernoulli p)
        Dist.approx (run sem (make 0)) (run sem (make 1)) `shouldBe` False
      it "retains the two cached-bit outcomes of a returned memo label and atom" $ do
        let e = Pair (MemoBernoulli 0.5) Fresh
            Dist.Cons outcomes = run sem e
        length outcomes `shouldBe` 2
        map snd outcomes `shouldBe` [0.5, 0.5]
      it "distinguishes a stored bit from a freshly sampled bit on a second call" $ do
        -- correlated applies m to the probe atom, so two calls on the same
        -- atom return the same stored bit; independent applies m to a fresh
        -- atom each call, so two calls are independent.
        let correlated =
              Let (Val (Id ("m", MemFn)) (MemoBernoulli 0.5)) $
                Lambda (Id ("argument", 𝔸))
                  (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("argument", 𝔸))))
            independent =
              Let (Val (Id ("m", MemFn)) (MemoBernoulli 0.5)) $
                Lambda (Id ("argument", 𝔸))
                  (MemoApply (Variable (Id ("m", MemFn))) Fresh)
        Dist.approx (run sem correlated) (run sem independent) `shouldBe` False

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
