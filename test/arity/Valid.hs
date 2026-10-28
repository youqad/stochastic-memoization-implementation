{-# LANGUAGE DataKinds #-}
module Valid where
import Syntax
valid :: Expr 'TBool
valid = Apply (Lambda (Id ("x", 𝔹)) (Variable (Id ("x", 𝔹)))) (Bool True)
