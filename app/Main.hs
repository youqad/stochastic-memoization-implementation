{-# LANGUAGE DataKinds #-}

module Main where

import qualified Data.Map as Map

import Control.Monad (forM_)

import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State

import Text.Pretty.Simple (pPrint)

import Syntax
import Environment
import Values
import Semantics


-- exp18 =
-- Let (x_1 := Let (x_1 := (λx_1. x_1)) in (λx_2. x_2) `Apply` [(λx_2. Fresh)]) in (Fresh) == (x_1 `Apply` [Flip])
exp18 :: Expr 'TBool
exp18 = 
  Let (Val 
    (Id ("x_1", Arr 𝔹 𝔸)) 
    (Let (Val 
      (Id ("x_1", Arr 𝔸 𝔸)) 
      (Lambda (Id ("x_1", 𝔸)) (Variable (Id ("x_1", 𝔸)))))
      (Lambda (Id ("x_2", Arr 𝔹 𝔸)) (Variable (Id ("x_2", Arr 𝔹 𝔸))) `Apply` (Lambda (Id ("x_2", 𝔹)) Fresh)))) $
    Fresh `Eq` (Variable (Id ("x_1", Arr 𝔹 𝔸)) `Apply` (Flip))


testExps :: Foldable t => t (Exists Expr) -> IO ()
testExps exps = do
  forM_ exps $ \(This e) -> do
    pPrint e
    let T ev1 = bigStepComplete e initEnv
        T ev2 = smallStepIteratedTraced e initEnv
        res1 = Dist.norm $ simplify <$> State.runStateT ev1 (initMem, S Map.empty)
        res2 = State.runStateT ev2 (initMem, S Map.empty)
    putStrLn $ "bigStepComplete: \n" ++ Dist.pretty show res1
    putStrLn $ "smallStepIteratedTraced: \n" ++ Dist.pretty show (Dist.norm $ (\((v, tr), s) -> (simplify (v, s), tr)) <$> res2)
    putStrLn "______________________________________________"

main :: IO ()
main = do
  let exps = [This exp18]
  testExps exps

