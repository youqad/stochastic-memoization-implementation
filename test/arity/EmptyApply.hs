{-# LANGUAGE DataKinds #-}
module EmptyApply where
import Syntax
bad :: Expr 'TBool
bad = Apply (Variable (Id ("f", Arr 𝔹 𝔹))) []
