{-# LANGUAGE DataKinds #-}
module EmptyLambda where
import Syntax
bad :: Expr ('TArrow '[ 'TBool] 'TBool)
bad = Lambda [] (Bool True)
