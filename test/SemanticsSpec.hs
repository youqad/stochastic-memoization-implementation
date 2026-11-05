{-# LANGUAGE DataKinds #-}

module SemanticsSpec (spec) where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Control.Monad (forM_)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State
import qualified Data.Map as Map

import Syntax
import Environment
import Values
import Semantics

-- | The joint law of two independent memo-table queries at the same bias,
-- computed by hand: P(T,T)=p^2, P(T,F)=p(1-p), P(F,T)=(1-p)p, P(F,F)=(1-p)^2.
-- The two queries use distinct atoms, so their outcomes are independent.
jointProgram :: Double -> Expr ('TProduct 'TBool 'TBool)
jointProgram p = Let (Val (Id ("m", MemFn)) (MemoBernoulli p)) $
          Let (Val (Id ("a1", 𝔸)) Fresh) $
          Let (Val (Id ("a2", 𝔸)) Fresh) $
            Pair
              (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a1", 𝔸))))
              (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a2", 𝔸))))

runJoint :: (Expr ('TProduct 'TBool 'TBool) -> EnvVal -> T (Value ('TProduct 'TBool 'TBool)))
  -> Double -> [((Bool, Bool), Double)]
runJoint sem p =
  let T ev = sem (jointProgram p) initEnv
      values = fmap fst $ State.runStateT ev (initMem, S Map.empty)
      Dist.Cons outcomes = Dist.norm values
  in map (\(PairVal (BoolVal b1) (BoolVal b2) _, q) -> ((b1, b2), q)) outcomes

-- | Hand-computed joint law at bias p, as an association list in the order
-- Dist.norm produces (lexicographic on the (False<True) pair).
expectedJoint :: Double -> [((Bool, Bool), Double)]
expectedJoint p =
  [ ((False, False), (1 - p) * (1 - p))
  , ((False, True),  (1 - p) * p)
  , ((True,  False), p * (1 - p))
  , ((True,  True),  p * p)
  ]

-- | Pointwise approximate equality of the two association lists: same keys,
-- probabilities within Dist.approx's rounding-error margin.
jointApprox :: [((Bool, Bool), Double)] -> [((Bool, Bool), Double)] -> Bool
jointApprox xs ys =
  map fst xs == map fst ys
    && all (\(x, y) -> abs (x - y) < Dist.errorMargin) (zip (map snd xs) (map snd ys))

spec :: Spec
spec = do
    describe "Big-step semantics" $ do
      modifyMaxSize (const 4)
        $ modifyMaxSuccess (const 1500)
        $ prop "is equivalent to denotational semantics" $ \(This expr) ->
          let bigStepResult = run bigStepComplete expr
              denResult = run den expr in
          (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |denotational| \n\n" ++ Dist.pretty show denResult)
          `counterexample`
          Dist.approx bigStepResult denResult
      modifyMaxSize (const 4)
        $ modifyMaxSuccess (const 1500)
        $ prop "is equivalent to small-step semantics" $ \(This expr) ->
          let bigStepResult = run bigStepComplete expr
              smallStepResult = run smallStepIteratedComplete expr in
          (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |smallStep| \n\n" ++ Dist.pretty show smallStepResult)
          `counterexample`
          Dist.approx bigStepResult smallStepResult
    describe "Independent joint laws per evaluator" $ do
      let evaluators =
            [ ("big-step", bigStep)
            , ("small-step", smallStepIterated)
            , ("denotational", den)
            ]
      forM_ evaluators $ \(name, sem) -> do
        it (name ++ ": two independent fair-bit queries give 1/4 each") $
          runJoint sem 0.5 `shouldSatisfy` jointApprox (expectedJoint 0.5)
        it (name ++ ": two independent bias-1/3 queries give 1/9, 2/9, 2/9, 4/9") $
          runJoint sem (1/3) `shouldSatisfy` jointApprox (expectedJoint (1/3))