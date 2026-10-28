{-# LANGUAGE DataKinds #-}
module ExtraLambda where
import Syntax
bad :: Expr ('TArrow '[ 'TBool] 'TBool)
bad = Lambda [Id ("x", 𝔹), Id ("y", 𝔹)] (Bool True)
