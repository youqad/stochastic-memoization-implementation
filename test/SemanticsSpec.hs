{-# LANGUAGE DataKinds #-}

module SemanticsSpec (spec) where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Test.QuickCheck.Random (mkQCGen)
import Control.Monad (forM_)
import Data.Ratio ((%))

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State
import qualified Data.Map as Map

import Syntax
import Environment
import Values
import Semantics

jointProgram :: Double -> Expr ('TProduct 'TBool 'TBool)
jointProgram p = Let (Val (Id ("m", MemFn)) (MemoBernoulli p)) $
          Let (Val (Id ("a1", 𝔸)) Fresh) $
          Let (Val (Id ("a2", 𝔸)) Fresh) $
            Pair
              (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a1", 𝔸))))
              (MemoApply (Variable (Id ("m", MemFn))) (Variable (Id ("a2", 𝔸))))

runJoint :: (Expr ('TProduct 'TBool 'TBool) -> EnvVal -> T (Value ('TProduct 'TBool 'TBool)))
  -> Double -> [((Bool, Bool), Rational)]
runJoint sem p =
  let T ev = sem (jointProgram p) initEnv
      values = fmap fst $ State.runStateT ev (initMem, S Map.empty)
      Dist.Cons outcomes = Dist.norm values
  in map (\(PairVal (BoolVal b1) (BoolVal b2) _, q) -> ((b1, b2), q)) outcomes

-- seed 566 for 1,500 expressions of size at most 8 (some seeds can exceed memory)
fixedTerms :: Args -> Args
fixedTerms args = args {maxSize = 8, maxSuccess = 1500, replay = Just (mkQCGen 566, 0)}

spec :: Spec
spec = do
    describe "Big-step semantics" $ do
      modifyArgs fixedTerms
        $ prop "is equivalent to denotational semantics" $ \(This expr) ->
          let bigStepResult = run bigStepComplete expr
              denResult = run den expr in
          (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |denotational| \n\n" ++ Dist.pretty show denResult)
          `counterexample`
          Dist.equal bigStepResult denResult
      modifyArgs fixedTerms
        $ prop "is equivalent to small-step semantics" $ \(This expr) ->
          let bigStepResult = run bigStepComplete expr
              smallStepResult = run smallStepIteratedComplete expr in
          (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |smallStep| \n\n" ++ Dist.pretty show smallStepResult)
          `counterexample`
          Dist.equal bigStepResult smallStepResult
    describe "independent memo queries in each evaluator" $ do
      let evaluators =
            [ ("big-step", bigStep)
            , ("small-step", smallStepIterated)
            , ("denotational", den)
            ]
      forM_ evaluators $ \(name, sem) -> do
        it (name ++ ": two independent fair-bit queries give 1/4 each") $
          runJoint sem 0.5 `shouldBe`
            [ ((False, False), 1 % 4), ((False, True), 1 % 4)
            , ((True, False),  1 % 4), ((True, True),  1 % 4) ]
        it (name ++ ": two independent quarter-bit queries give 9/16, 3/16, 3/16, 1/16") $
          runJoint sem 0.25 `shouldBe`
            [ ((False, False), 9 % 16), ((False, True), 3 % 16)
            , ((True, False),  3 % 16), ((True, True),  1 % 16) ]