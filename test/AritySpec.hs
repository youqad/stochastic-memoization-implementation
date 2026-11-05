{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# LANGUAGE GADTs, DataKinds #-}

-- Guards the types of Lambda and Apply: each expression below is ill-typed,
-- by its argument type or by its number of arguments, and
-- should-not-typecheck asserts the type checker rejects it, driven by
-- deferred type errors. The positive control is a well-typed
-- single-argument application evaluated in each semantics.
module AritySpec (spec) where

import Test.Hspec
import Test.ShouldNotTypecheck (shouldNotTypecheck)
import Control.DeepSeq (NFData (..))

import Syntax
import Semantics (runBooleanLaw, bigStep, smallStepIterated, den)
import Values

-- Hand-written rnf for the GADT; DeriveGeneric does not apply here.
instance NFData (Expr a) where
  rnf expr = case expr of
    Atom a -> rnf a
    Bool b -> rnf b
    If a b c -> rnf a `seq` rnf b `seq` rnf c
    Pair a b -> rnf a `seq` rnf b
    Match a _ b -> rnf a `seq` rnf b
    Variable x -> x `seq` ()
    Lambda x b -> x `seq` rnf b
    Apply f a -> rnf f `seq` rnf a
    MemoBernoulli p -> rnf p
    MemoApply f a -> rnf f `seq` rnf a
    Eq a b -> rnf a `seq` rnf b
    Let d b -> d `seq` rnf b
    Sequence a b -> rnf a `seq` rnf b
    Fresh -> ()
    Flip -> ()

spec :: Spec
spec = describe "Single-argument arity" $ do
  it "rejects applying a non-function" $
    shouldNotTypecheck
      (Apply (Bool True) (Bool True) :: Expr 'TBool)
  it "rejects applying a function to an argument of the wrong type" $
    shouldNotTypecheck
      (Apply (Lambda (Id ("x", 𝔹)) (Variable (Id ("x", 𝔹)))) Fresh :: Expr 'TBool)
  it "rejects an atom where a memo function is expected" $
    shouldNotTypecheck
      (MemoApply (Atom (Atm 0)) Fresh :: Expr 'TBool)
  it "rejects a memo function applied to a boolean atom" $
    shouldNotTypecheck
      (MemoApply (MemoBernoulli 0.5) (Bool True) :: Expr 'TBool)
  it "rejects a lambda with no binders" $
    shouldNotTypecheck
      (Lambda [] (Bool True) :: Expr ('TArrow '[ 'TBool] 'TBool))
  it "rejects a lambda with a list of binders instead of one" $
    shouldNotTypecheck
      (Lambda [Id ("x", 𝔹)] (Bool True) :: Expr ('TArrow '[ 'TBool] 'TBool))
  it "rejects a lambda with two binders" $
    shouldNotTypecheck
      (Lambda [Id ("x", 𝔹), Id ("y", 𝔹)] (Bool True) :: Expr ('TArrow '[ 'TBool] 'TBool))
  it "rejects an apply with no arguments" $
    shouldNotTypecheck
      (Apply (Variable (Id ("f", Arr 𝔹 𝔹))) [] :: Expr 'TBool)
  it "rejects an apply with a list of arguments instead of one" $
    shouldNotTypecheck
      (Apply (Variable (Id ("f", Arr 𝔹 𝔹))) [Bool True] :: Expr 'TBool)
  it "rejects an apply with two arguments" $
    shouldNotTypecheck
      (Apply (Variable (Id ("f", Arr 𝔹 𝔹))) [Bool True, Bool False] :: Expr 'TBool)
  it "evaluates a well-typed single-argument application in big-step" $
    runBooleanLaw bigStep valid `shouldBe` [(True, 1)]
  it "evaluates a well-typed single-argument application in small-step" $
    runBooleanLaw smallStepIterated valid `shouldBe` [(True, 1)]
  it "evaluates a well-typed single-argument application in denotational" $
    runBooleanLaw den valid `shouldBe` [(True, 1)]
  where
    valid = Apply (Lambda (Id ("x", 𝔹)) (Variable (Id ("x", 𝔹)))) (Bool True)
