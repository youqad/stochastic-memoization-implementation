{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, DerivingVia, FlexibleInstances #-}

module Main where

import qualified Data.Map as Map

import Control.Monad (forM_)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State

import Test.QuickCheck
-- import System.IO.Unsafe (unsafePerformIO)
import Text.Pretty.Simple (pPrint, pPrintString)

import Syntax
import Environment
import Values
import Semantics


-- let-bind two atoms and apply a function comparing two atoms to them
exp1 :: Expr 'TBool
exp1 =
  Let (Val (Id ("x", 𝔹)) Flip) $
  Let (Val (Id ("y", 𝔹)) Flip) $
  Apply
    (Lambda [Id ("x'", 𝔹)] (Eq (Variable (Id ("x'", 𝔹))) (Variable (Id ("x", 𝔹)))))
    [Variable (Id ("y", 𝔹))]

-- assign two atoms to two variables and applyBigStep a bernoulli function of bias 0.5 to them, then applyBigStep a memoized application of the bernoulli function to the two atoms and compare them 

-- | NB: The memoization state/memory is global, not local to the body of Lambda expressions (does carry over outside the scope of the body)
-- | cf. exp2 vs exp3

exp2 :: Expr 'TBool
exp2 =
  Let (Val (Id ("x", 𝔸)) Fresh) $
  Let (Val (Id ("y", 𝔸)) Fresh) $
  Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.5)) $
  Let (Val (Id ("g", Arr 𝔸 (Arr 𝔸 𝔹))) 
    (Lambda [Id ("x'", 𝔸)] $ Lambda [Id ("y'", 𝔸)] $ 
      Eq
        (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("x'", 𝔸))))
        (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("y'", 𝔸)))))) $
  Apply
    (Apply (Variable (Id ("g", Arr 𝔸 (Arr 𝔸 𝔹)))) [Variable (Id ("x", 𝔸))]) 
    [Variable (Id ("y", 𝔸))]

exp3 :: Expr 'TBool
exp3 =
  Let (Val (Id ("x", 𝔸)) Fresh) $
  Let (Val (Id ("y", 𝔸)) Fresh) $
  Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.5)) $
  Eq (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("x", 𝔸)))) (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("y", 𝔸))))

exp4 :: Expr 'TBool
exp4 =
  Let (Val (Id ("x", 𝔸)) Fresh) $
  Let (Val (Id ("y", 𝔸)) Fresh) $
  Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.5)) $
  Eq (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("x", 𝔸)))) (Bool True)

exp5 :: Expr 'TBool 
-- exp5 is the expression (where == is syntactic sugar for the Eq construct):
-- "if (λ (x_1) flip())((λ (x_1) fresh())(flip())) then (λ (x_1) fresh())(flip()) == (if flip() then fresh() else fresh()) else (if flip() then fresh() else fresh()), (if flip() then fresh() else fresh())"
exp5 = 
  If (Apply (Lambda [Id ("x_1", 𝔸)] Flip) [Apply (Lambda [Id ("x_2", 𝔹)] Fresh) [Flip]]) 
    (Apply (Lambda [Id ("x_3", 𝔹)] Fresh) [Flip]
    `Eq`  
    If Flip Fresh Fresh) $
    If Flip Flip Flip

-- exp6: if ((λx_1. Flip) [(λx_2. Fresh) [Flip]]) then (((λx_3. Fresh) [Flip]) == (if (Flip) then (Fresh) else (Fresh))) else (if (Flip) then (Flip) else (Flip))
exp6 :: Expr 'TBool
exp6 = 
  If (Apply (Lambda [Id ("x_1", 𝔸)] Flip) [Apply (Lambda [Id ("x_2", 𝔹)] Fresh) [Flip]]) 
    (Apply (Lambda [Id ("x_3", 𝔹)] Fresh) [Flip]
    `Eq`  
    If Flip Fresh Fresh) $
    If Flip Flip Flip

-- exp7: ((λx_1. Fresh) [memoBernoulli 0.166 `memoApply` (Fresh)]) == (let (x_1 := (λx_1. x_1)) in (λx_2. Fresh) [(λx_1. Flip)])
exp7 :: Expr 'TBool
exp7 = 
  Apply (Lambda [Id ("x_1", 𝔹)] Fresh) [MemoBernoulli 0.166 `MemoApply` Fresh]
  `Eq`
  Let (Val (Id ("x_1", Arr 𝔸 𝔸)) (Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸))))) 
  (Apply (Lambda [Id ("x_2", Arr 𝔸 𝔸)] Fresh) [Lambda [Id ("x_1", 𝔸)] Fresh])

-- exp8: Match (Match ((Fresh) == (Fresh), let (x_1 := (λx_1. x_1)) in Fresh) with (x_1, x_2) -> (let (x_3 := (λx_3. Fresh)) in memoBernoulli 0.403), Match (if (Flip) then ((λx_1. Fresh)) else ((λx_1. Fresh)), let (x_1 := (λx_1. x_1)) in Flip) with (x_1, x_2) -> (if (x_2) then (memoBernoulli 0.795) else (memoBernoulli 0.826))) with (x_1, x_2) -> (Fresh)
exp8 :: Expr 'TAtom
exp8 = 
  Match (
    Pair
    (Match
      (Pair (Fresh `Eq` Fresh) (Let (Val (Id ("x_1", Arr 𝔹 𝔹)) (Lambda [Id ("x_1", 𝔹)] (Variable (Id ("x_1", 𝔹))))) Fresh)) 
      (Id ("x_1", 𝔹), Id ("x_2", 𝔸))
      (Let (Val (Id ("x_3", Arr 𝔹 𝔸)) (Lambda [Id ("x_3", 𝔹)] Fresh)) (MemoBernoulli 0.403)))
    (Match 
      (Pair
      (If Flip (Lambda [Id ("x_1", 𝔸)] Fresh) (Lambda [Id ("x_1", 𝔸)] Fresh))
      (Let (Val (Id ("x_1", Arr 𝔹 𝔹)) (Lambda [Id ("x_1", 𝔹)] (Variable (Id ("x_1", 𝔹))))) Flip))
      (Id ("x_1", Arr 𝔸 𝔸), Id ("x_2", 𝔹))
      (If (Variable (Id ("x_2", 𝔹))) (MemoBernoulli 0.795) (MemoBernoulli 0.826)))
  )
  (Id ("x_1", MemFn), Id ("x_2", MemFn)) 
  Fresh

-- exp9 = If ((λx_1. Flip) [Match (MemoBernoulli 0.207, Fresh) with (x_1, x_2) -> ((λx_3. x_2))]) then (If ((Flip) == (Flip)) then (Match (Fresh, Flip) with (x_1, x_2) -> ((λx_3. Fresh))) else ((λx_1. x_1))) else ((λx_1. Fresh))
exp9 :: Expr ('TArrow '[ 'TAtom] 'TAtom)
exp9 = 
  If (Apply (Lambda [Id ("x_1", Arr 𝔸 𝔸)] Flip) [Match (Pair (MemoBernoulli 0.207) Fresh) (Id ("x_1", MemFn), Id ("x_2", 𝔸)) (Lambda [Id ("x_3", 𝔸)] (Variable (Id ("x_2", 𝔸))))])
  (If (Flip `Eq` Flip) (Match (Pair Fresh Flip) (Id ("x_1", 𝔸), Id ("x_2", 𝔹)) (Lambda [Id ("x_3", 𝔸)] Fresh)) (Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸)))))
  (Lambda [Id ("x_1", 𝔸)] Fresh)


prop_semanticsEquivalent :: Property
prop_semanticsEquivalent =
  forAll (resize 4 arbitrary :: Gen (Exists Expr)) $ \(This expr) ->
      let bigStepResult = run bigStepComplete expr
          denResult = run den expr
          smallStepResult = run smallStepIteratedComplete expr
      in
      -- test that the two semantics agree on the distribution with @approx'@,
      -- and if they don't, display the two distributions
      counterexample 
        (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |denotational| \n\n" ++ Dist.pretty show denResult) 
        (approx' bigStepResult denResult)
      .&&. 
      counterexample 
        (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |smallStep| \n\n" ++ Dist.pretty show smallStepResult) 
        (approx' bigStepResult smallStepResult)

-- QuickCheck to test equivalence of the various semantics
-- prop_semantics :: Expr a -> Property
-- prop_semantics e =
--   forAll (choose (0, 10)) $ \n ->
--     let res = runSems <*> [e] in
--     all (== head res) (tail res)

-- | run several steps of the small-step semantics and print the result
testSmallStep :: Expr a -> IO ()
testSmallStep e = do
  putStrLn "______________________________________________"
  pPrint e
  forM_ [1..4] $ \i -> do
    let T ev = smallStepIterate i e initEnv
        res = simplify <$> State.runStateT ev (initMem, S Map.empty)
    pPrintString $ "smallStepIterate " ++ show i ++ ": \n" ++ Dist.pretty show (Dist.norm res)
    putStrLn "______________________________________________"

-- | run the various semantics on a list of expressions several and print the result
testSemantics :: [Exists Expr] -> IO ()
testSemantics exps =
  forM_ exps $ \(This e) -> do
    putStrLn "______________________________________________"
    pPrint e
    let res = runSems <*> [e]
    forM_ res (putStrLn . Dist.pretty show)
    putStrLn "______________________________________________"

main :: IO ()
main = do
  -- let exps = [This exp8, This exp2, This exp3, This exp4]
  -- exps <- generate (vectorOf 2 (resize 4 arbitrary :: Gen (Exists Expr)))
  -- testSemantics exps
  -- quickCheck prop_semanticsEquivalent
  testSemantics [This exp9]
