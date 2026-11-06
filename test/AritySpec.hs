{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# LANGUAGE GADTs, DataKinds #-}

module AritySpec (spec) where

import Test.Hspec
import Test.ShouldNotTypecheck (shouldNotTypecheck)
import Control.DeepSeq (NFData (..))

import Syntax
import Semantics (runBooleanLaw, bigStep, smallStepIterated, den)
import Values

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
spec = describe "function applications: types and arity" $ do
  it "non-function application rejected" $
    shouldNotTypecheck
      (Apply (Bool True) (Bool True) :: Expr 'TBool)
  it "wrong argument type rejected" $
    shouldNotTypecheck
      (Apply (Lambda (Id ("x", 𝔹)) (Variable (Id ("x", 𝔹)))) Fresh :: Expr 'TBool)
  it "atom in place of a memo function rejected" $
    shouldNotTypecheck
      (MemoApply (Atom (Atm 0)) Fresh :: Expr 'TBool)
  it "boolean memo argument rejected" $
    shouldNotTypecheck
      (MemoApply (MemoBernoulli 0.5) (Bool True) :: Expr 'TBool)
  it "lambda with no binder rejected" $
    shouldNotTypecheck
      (Lambda [] (Bool True) :: Expr ('TArrow '[ 'TBool] 'TBool))
  it "lambda binder list rejected" $
    shouldNotTypecheck
      (Lambda [Id ("x", 𝔹)] (Bool True) :: Expr ('TArrow '[ 'TBool] 'TBool))
  it "lambda with two binders rejected" $
    shouldNotTypecheck
      (Lambda [Id ("x", 𝔹), Id ("y", 𝔹)] (Bool True) :: Expr ('TArrow '[ 'TBool] 'TBool))
  it "application with no argument rejected" $
    shouldNotTypecheck
      (Apply (Variable (Id ("f", Arr 𝔹 𝔹))) [] :: Expr 'TBool)
  it "application argument list rejected" $
    shouldNotTypecheck
      (Apply (Variable (Id ("f", Arr 𝔹 𝔹))) [Bool True] :: Expr 'TBool)
  it "application with two arguments rejected" $
    shouldNotTypecheck
      (Apply (Variable (Id ("f", Arr 𝔹 𝔹))) [Bool True, Bool False] :: Expr 'TBool)
  it "single argument under big-step" $
    runBooleanLaw bigStep valid `shouldBe` [(True, 1)]
  it "single argument under small-step" $
    runBooleanLaw smallStepIterated valid `shouldBe` [(True, 1)]
  it "single argument under denotational semantics" $
    runBooleanLaw den valid `shouldBe` [(True, 1)]
  where
    valid = Apply (Lambda (Id ("x", 𝔹)) (Variable (Id ("x", 𝔹)))) (Bool True)
