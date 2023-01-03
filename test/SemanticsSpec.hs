{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, DerivingVia, FlexibleInstances #-}

module SemanticsSpec (spec) where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import qualified Numeric.Probability.Distribution as Dist

import Syntax
import Semantics

spec :: Spec
spec = do
    describe "Big-step semantics" $ do
      modifyMaxSize (const 8) 
        $ modifyMaxSuccess (const 1000) 
        $ prop "is equivalent to denotational semantics" $ \(This expr) ->
          let bigStepResult = run bigStepComplete expr
              denResult = run den expr in
          -- test that the two semantics agree on the distribution with @approx''@, and if they don't, display the two distributions
          (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |denotational| \n\n" ++ Dist.pretty show denResult) 
          `counterexample` 
          approx'' bigStepResult denResult
      modifyMaxSize (const 8) 
        $ modifyMaxSuccess (const 1000) 
        $ prop "is equivalent to small-step semantics" $ \(This expr) ->
          let bigStepResult = run bigStepComplete expr
              smallStepResult = run smallStepIteratedComplete expr in
          (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |smallStep| \n\n" ++ Dist.pretty show smallStepResult) 
          `counterexample` 
          approx'' bigStepResult smallStepResult