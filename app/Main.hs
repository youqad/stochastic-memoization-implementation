{-# LANGUAGE ScopedTypeVariables, ExtendedDefaultRules, TypeFamilies, ConstraintKinds, FlexibleContexts, AllowAmbiguousTypes, GADTs, DataKinds, PolyKinds, RankNTypes, PartialTypeSignatures, UndecidableInstances, DerivingVia, FlexibleInstances, TypeOperators #-}

module Main where

import qualified Data.Map as Map

import Control.Monad (forM_)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State

import Test.QuickCheck.Counterexamples
-- import System.IO.Unsafe (unsafePerformIO)
import Text.Pretty.Simple (pPrint, pPrintString)

import Syntax
import Environment
import Values
import Semantics


-- let-bind two atoms and apply a function comparing two atoms to them
-- exp1 = 
-- Let (x := Flip) in Let (y := Flip) in (λx'. (x') == (x)) `Apply` [y]
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

-- exp2 =
-- Let (x := Fresh) in Let (y := Fresh) in Let (f := MemoBernoulli 0.5) in Let (g := (λx'. (λy'. (f `MemoApply` (x')) == (f `MemoApply` (y'))))) in g `Apply` [x] `Apply` [y]
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

-- exp3 =
-- Let (x := Fresh) in Let (y := Fresh) in Let (f := MemoBernoulli 0.5) in (f `MemoApply` (x)) == (f `MemoApply` (y))
exp3 :: Expr 'TBool
exp3 =
  Let (Val (Id ("x", 𝔸)) Fresh) $
  Let (Val (Id ("y", 𝔸)) Fresh) $
  Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.5)) $
  Eq (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("x", 𝔸)))) (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("y", 𝔸))))

-- exp4 =
-- Let (x := Fresh) in Let (y := Fresh) in Let (f := MemoBernoulli 0.5) in (f `MemoApply` (x)) == (True)
exp4 :: Expr 'TBool
exp4 =
  Let (Val (Id ("x", 𝔸)) Fresh) $
  Let (Val (Id ("y", 𝔸)) Fresh) $
  Let (Val (Id ("f", MemFn)) (MemoBernoulli 0.5)) $
  Eq (MemoApply (Variable (Id ("f", MemFn))) (Variable (Id ("x", 𝔸)))) (Bool True)

-- exp5 =
-- If ((λx_1. Flip) `Apply` [(λx_2. Fresh) `Apply` [Flip]]) then (((λx_3. Fresh) `Apply` [Flip]) == (If (Flip) then (Fresh) else (Fresh))) else (If (Flip) then (Flip) else (Flip))
exp5 :: Expr 'TBool
exp5 = 
  If (Apply (Lambda [Id ("x_1", 𝔸)] Flip) [Apply (Lambda [Id ("x_2", 𝔹)] Fresh) [Flip]]) 
    (Apply (Lambda [Id ("x_3", 𝔹)] Fresh) [Flip]
    `Eq`  
    If Flip Fresh Fresh) $
    If Flip Flip Flip

-- exp6 =
-- If ((λx_1. Flip) `Apply` [(λx_2. Fresh) `Apply` [Flip]]) then (((λx_3. Fresh) `Apply` [Flip]) == (If (Flip) then (Fresh) else (Fresh))) else (If (Flip) then (Flip) else (Flip))
exp6 :: Expr 'TBool
exp6 = 
  If (Apply (Lambda [Id ("x_1", 𝔸)] Flip) [Apply (Lambda [Id ("x_2", 𝔹)] Fresh) [Flip]]) 
    (Apply (Lambda [Id ("x_3", 𝔹)] Fresh) [Flip]
    `Eq`  
    If Flip Fresh Fresh) $
    If Flip Flip Flip

-- exp7 =
-- ((λx_1. Fresh) `Apply` [MemoBernoulli 0.166 `MemoApply` (Fresh)]) == (Let (x_1 := (λx_1. x_1)) in (λx_2. Fresh) `Apply` [(λx_1. Fresh)])
exp7 :: Expr 'TBool
exp7 = 
  Apply (Lambda [Id ("x_1", 𝔹)] Fresh) [MemoBernoulli 0.166 `MemoApply` Fresh]
  `Eq`
  Let (Val (Id ("x_1", Arr 𝔸 𝔸)) (Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸))))) 
  (Apply (Lambda [Id ("x_2", Arr 𝔸 𝔸)] Fresh) [Lambda [Id ("x_1", 𝔸)] Fresh])

-- exp8 = 
-- Match Pair (Match Pair ((Fresh) == (Fresh), Let (x_1 := (λx_1. x_1)) in Fresh) with (x_1, x_2) -> (Let (x_3 := (λx_3. Fresh)) in MemoBernoulli 0.403), Match Pair (If (Flip) then ((λx_1. Fresh)) else ((λx_1. Fresh)), Let (x_1 := (λx_1. x_1)) in Flip) with (x_1, x_2) -> (If (x_2) then (MemoBernoulli 0.795) else (MemoBernoulli 0.826))) with (x_1, x_2) -> (Fresh)
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

-- exp9 = 
-- If ((λx_1. Flip) `Apply` [Match Pair (MemoBernoulli 0.207, Fresh) with (x_1, x_2) -> ((λx_3. x_2))]) then (If ((Flip) == (Flip)) then (Match Pair (Fresh, Flip) with (x_1, x_2) -> ((λx_3. Fresh))) else ((λx_1. x_1))) else ((λx_1. Fresh))
exp9 :: Expr ('TArrow '[ 'TAtom] 'TAtom)
exp9 = 
  If (Apply (Lambda [Id ("x_1", Arr 𝔸 𝔸)] Flip) [Match (Pair (MemoBernoulli 0.207) Fresh) (Id ("x_1", MemFn), Id ("x_2", 𝔸)) (Lambda [Id ("x_3", 𝔸)] (Variable (Id ("x_2", 𝔸))))])
  (If (Flip `Eq` Flip) (Match (Pair Fresh Flip) (Id ("x_1", 𝔸), Id ("x_2", 𝔹)) (Lambda [Id ("x_3", 𝔸)] Fresh)) (Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸)))))
  (Lambda [Id ("x_1", 𝔸)] Fresh)


-- prop_semanticsEquivalent :: Property
-- prop_semanticsEquivalent =
--   forAll (resize 4 arbitrary :: Gen (Exists Expr)) $ \(This expr) ->
--       let bigStepResult = run bigStepComplete expr
--           denResult = run den expr
--           smallStepResult = run smallStepIteratedComplete expr
--       in
--       -- test that the two semantics agree on the distribution with @approx''@,
--       -- and if they don't, display the two distributions
--       counterexample 
--         (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |denotational| \n\n" ++ Dist.pretty show denResult) 
--         (approx'' bigStepResult denResult)
--       .&&. 
--       counterexample 
--         (Dist.pretty show bigStepResult ++ "\n  |bigStep| ≠ |smallStep| \n\n" ++ Dist.pretty show smallStepResult) 
--         (approx'' bigStepResult smallStepResult)

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

-- exp10 =
-- Pair (Let (x_1 := (λx_1. (λx_2. Fresh)) `Apply` [(λx_1. x_1)]) in Let (x_2 := Fresh) in x_2, Match Pair (Let (x_1 := MemoBernoulli 0.995) in (λx_2. x_2), Match Pair (MemoBernoulli 0.232, (λx_1. Fresh)) with (x_1, x_2) -> (Fresh)) with (x_1, x_2) -> (Match Pair ((λx_3. Fresh), x_2) with (x_3, x_4) -> (Fresh)))
exp10 :: Expr ('TProduct 'TAtom 'TAtom)
exp10 =
  Pair
  (
    Let 
      (Val 
        (Id ("x_1", Arr 𝔸 𝔸)) 
        (Apply (Lambda [Id ("x_1", Arr 𝔸 𝔸)] (Lambda [Id ("x_2", 𝔸)] Fresh)) [Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸)))]))
      (Let (Val (Id ("x_2", 𝔸)) Fresh) $
        Variable (Id ("x_2", 𝔸)))
  )
  (
    Match
      (Pair
        (Let (Val (Id ("x_1", MemFn)) (MemoBernoulli 0.995)) $ 
        Lambda [Id ("x_2", 𝔸)] (Variable (Id ("x_2", 𝔸))))
        (Match 
          (Pair (MemoBernoulli 0.232) (Lambda [Id ("x_1", 𝔸)] Fresh)) 
          (Id ("x_1", MemFn), Id ("x_2", Arr 𝔸 𝔸)) 
          Fresh)
      )
      (Id ("x_1", Arr 𝔸 𝔸), Id ("x_2", 𝔸))
      (Match 
        (Pair 
          (Lambda [Id ("x_3", 𝔸)] Fresh) 
          (Variable (Id ("x_2", 𝔸)))) 
        (Id ("x_3", Arr 𝔸 𝔸), Id ("x_4", 𝔸)) 
        Fresh)
  )

-- exp11 =
-- Pair (Match Pair (Let (x_1 := Fresh) in x_1, Let (x_1 := Fresh) in (λx_2. Flip)) with (x_1, x_2) -> (If (Flip) then (Fresh) else (x_1)), Match Pair (Let (x_1 := Fresh) in x_1, (λx_1. x_1) `Apply` [(λx_1. x_1)]) with (x_1, x_2) -> ((λx_3. Fresh) `Apply` [MemoBernoulli 0.346]))
exp11 :: Expr ('TProduct 'TAtom 'TAtom)
exp11 =
  Pair
  (
    Match
      (Pair
        (Let (Val (Id ("x_1", 𝔸)) Fresh) $ Variable (Id ("x_1", 𝔸)))
        (Let (Val (Id ("x_1", 𝔸)) Fresh) $ Lambda [Id ("x_2", 𝔸)] Flip))
      (Id ("x_1", 𝔸), Id ("x_2", Arr 𝔸 𝔹))
      (If Flip Fresh (Variable (Id ("x_1", 𝔸)))))
  (
    Match
      (Pair
        (Let (Val (Id ("x_1", 𝔸)) Fresh) $ Variable (Id ("x_1", 𝔸)))
        (Lambda [Id ("x_1", Arr 𝔸 𝔸)] (Variable (Id ("x_1", Arr 𝔸 𝔸))) `Apply` [Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸)))]))
      (Id ("x_1", 𝔸), Id ("x_2", Arr 𝔸 𝔸))
      (Lambda [Id ("x_3", MemFn)] Fresh `Apply` [MemoBernoulli 0.346])
  )

-- exp11' =
-- Pair
--     ( Let ( x_1 := Fresh ) in ( If ( Flip ) then ( Fresh ) else ( x_1 ) )
--     , Let ( x_1 := Fresh ) in x_1
--     )
exp11' :: Expr ('TProduct 'TAtom 'TAtom)
exp11' =
  Pair
  (
    Let (Val (Id ("x_1", 𝔸)) Fresh) $
      If Flip Fresh (Variable (Id ("x_1", 𝔸)))
  )
  (
    Let (Val (Id ("x_1", 𝔸)) Fresh) $
      Variable (Id ("x_1", 𝔸))
  )

-- exp12 = 
-- Let ( x_1 := ( λx_1. ( λx_2. Fresh ) ) `Apply` [ ( λx_1. x_1 ) ]) 
-- in Let ( x_2 := Fresh ) in x_2

exp12 :: Expr 'TAtom
exp12 = 
  Let 
    (Val 
      (Id ("x_1", Arr 𝔸 𝔸)) 
      (Apply (Lambda [Id ("x_1", Arr 𝔸 𝔸)] (Lambda [Id ("x_2", 𝔸)] Fresh)) [Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸)))]))
    (Let (Val (Id ("x_2", 𝔸)) Fresh) $
      Variable (Id ("x_2", 𝔸)))

exp13 :: Expr 'TAtom
exp13 =
    Let 
      (Val (Id ("x", 𝔸)) Fresh) 
      (Lambda [Id ("y", 𝔸)] (Variable (Id ("x", 𝔸))))
    `Apply` [Fresh]


-- exp14:
exp14:: Expr 'TAtom
exp14 = 
  Lambda [Id ("x_1", 𝔸)] (Lambda [Id ("x_2", Arr 𝔸 𝔸)] (Variable (Id ("x_1", 𝔸))))
  `Apply` [Fresh]
  `Apply` [Let (Val (Id ("x_3", 𝔹)) (Bool True)) $ Lambda [Id ("x_4", 𝔸)] (Variable (Id ("x_4", 𝔸)))]

-- exp15 =
-- (λx_1. (λx_2. x_1)) `Apply` [MemoBernoulli 0.42] `Apply` [(λx_1. Flip) `Apply` [MemoBernoulli 0.64]]
exp15 :: Expr 'TMemoFun
exp15 = 
  Lambda [Id ("x_1", MemFn)] (Lambda [Id ("x_2", 𝔹)] (Variable (Id ("x_1", MemFn))))
  `Apply` [MemoBernoulli 0.42]
  `Apply` [Lambda [Id ("x_1", MemFn)] Flip `Apply` [MemoBernoulli 0.64]]

-- exp16 =
-- (λx_1. x_1 `Apply` [Flip]) `Apply` [(λx_1. Fresh)]
exp16:: Expr 'TAtom
exp16 =
  Lambda [Id ("x_1", Arr 𝔹 𝔸)] (Variable (Id ("x_1", Arr 𝔹 𝔸)) `Apply` [Flip])
  `Apply` [Lambda [Id ("x_1", 𝔹)] Fresh]

-- exp17 =
exp17 :: Expr 'TAtom
exp17 =
  If (Bool False)
    (Lambda [Id ("x_1", Arr 𝔸 𝔸)] Fresh)
    (Lambda [Id ("x_1", Arr 𝔸 𝔸)] Fresh) `Apply` [Lambda [Id ("x_1", Arr 𝔸 𝔸)] (Variable (Id ("x_1", Arr 𝔸 𝔸))) `Apply` [Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸)))]]

-- exp18 =
-- Let (x_1 := Let (x_1 := (λx_1. x_1)) in (λx_2. x_2) `Apply` [(λx_2. Fresh)]) in (Fresh) == (x_1 `Apply` [Flip])
exp18 :: Expr 'TBool
exp18 = 
  Let (Val 
    (Id ("x_1", Arr 𝔹 𝔸)) 
    (Let (Val 
      (Id ("x_1", Arr 𝔸 𝔸)) 
      (Lambda [Id ("x_1", 𝔸)] (Variable (Id ("x_1", 𝔸))))) 
      (Lambda [Id ("x_2", Arr 𝔹 𝔸)] (Variable (Id ("x_2", Arr 𝔹 𝔸))) `Apply` [Lambda [Id ("x_2", 𝔹)] Fresh]))) $
    Fresh `Eq` (Variable (Id ("x_1", Arr 𝔹 𝔸)) `Apply` [Flip])


prop_smallStep :: PropertyOf (Exists Expr :&: (Exists Expr :&: ()))
prop_smallStep =
  forAll (resize 5 arbitrary :: Gen (Exists Expr)) $ \(This expr) ->
  let bigStepResult = run bigStepComplete expr
      smallStepResult = run smallStepIteratedComplete expr
  in typedCounterexample 
      (This expr)
      $ approx'' bigStepResult smallStepResult === True

testExps :: Foldable t => t (Exists Expr) -> IO ()
testExps exps = do
  forM_ exps $ \(This e) -> do
    pPrint e
    let T ev1 = bigStepComplete e initEnv
        T ev2 = smallStepIteratedDebug e initEnv
        res1 = Dist.norm $ Dist.norm $ simplify' <$> State.runStateT ev1 (initMem, S Map.empty)
        res2 = Dist.norm $ Dist.norm $ simplify' <$> State.runStateT ev2 (initMem, S Map.empty)
    putStrLn $ "bigStepComplete: \n" ++ Dist.pretty show res1
    putStrLn $ "smallStepIterated: \n" ++ Dist.pretty show res2
    putStrLn "______________________________________________"

quickCheckSmallStep :: IO ()
quickCheckSmallStep = do
  Just (This e :&: _) <- quickCheckWith 
    (stdArgs {maxSuccess = 2000, maxSize = 8}) 
    prop_smallStep
  let T ev = smallStepIteratedDebug e initEnv
      res = Dist.norm $ Dist.norm $ simplify' <$> State.runStateT ev (initMem, S Map.empty)
  putStrLn $ "smallStepIteratedDebug: \n" ++ Dist.pretty show res

main :: IO ()
main = do
  let exps = [This exp18]
  testExps exps
  -- let exps = [This exp8, This exp2, This exp3, This exp4]
  -- exps <- generate (vectorOf 2 (resize 4 arbitrary :: Gen (Exists Expr)))
  -- testSemantics exps

