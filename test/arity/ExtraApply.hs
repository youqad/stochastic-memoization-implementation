{-# LANGUAGE DataKinds #-}
module ExtraApply where
import Syntax
bad :: Expr 'TBool
bad = Apply (Variable (Id ("f", Arr 𝔹 𝔹))) [Bool True, Bool False]
