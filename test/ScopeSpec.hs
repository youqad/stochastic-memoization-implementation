{-# LANGUAGE DataKinds, GADTs #-}
module ScopeSpec (spec) where
import Test.Hspec
import Control.Exception (ErrorCall (ErrorCall), evaluate)
import qualified Data.List as List
import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State
import qualified Data.Map as Map
import Syntax
import Environment
import Values
import Semantics

booleanLaw :: (Expr 'TBool -> EnvVal -> T (Value 'TBool)) -> Expr 'TBool -> [(Bool, Double)]
booleanLaw = runBooleanLaw

scopeWitness :: String -> Expr 'TBool
scopeWitness inner =
  let x = Id ("x", 𝔹)
      y = Id (inner, 𝔹)
  in Let (Val x (Bool True)) $
       If (Let (Val y (Bool False)) (Bool True))
         (Variable x) (Bool False)

spec :: Spec
spec = lexicalSpec

lexicalSpec :: Spec
lexicalSpec = describe "Lexical scope" $ do
  it "restores the caller after a shadowing If guard" $ do
    booleanLaw bigStep (scopeWitness "x") `shouldBe` [(True, 1)]
    booleanLaw den (scopeWitness "x") `shouldBe` [(True, 1)]
    booleanLaw smallStepIterated (scopeWitness "x") `shouldBe` [(True, 1)]
  it "agrees on the alpha-renamed If guard" $ do
    booleanLaw bigStep (scopeWitness "inner") `shouldBe` [(True, 1)]
    booleanLaw den (scopeWitness "inner") `shouldBe` [(True, 1)]
    booleanLaw smallStepIterated (scopeWitness "inner") `shouldBe` [(True, 1)]
  it "retains a guard's memo writes when restoring lexical scope" $ do
    let f = Id ("f", MemFn)
        a = Id ("a", 𝔸)
        b = Id ("b", 𝔹)
        query = MemoApply (Variable f) (Variable a)
        e = Let (Val f (MemoBernoulli 0.5)) $
              Let (Val a Fresh) $
                If (Let (Val b query) (Variable b)) query
                  (Eq query (Bool False))
    booleanLaw bigStep e `shouldBe` [(True, 1)]
    booleanLaw den e `shouldBe` [(True, 1)]
    booleanLaw smallStepIterated e `shouldBe` [(True, 1)]

  it "retains the probability weights of a guard with a local binding" $ do
    let x = Id ("x", 𝔹)
        f = Id ("f", MemFn)
        a = Id ("a", 𝔸)
        e = Let (Val x (Bool True)) $
              Let (Val f (MemoBernoulli 0.25)) $
                Let (Val a Fresh) $
                  If (Let (Val x (Bool False)) (MemoApply (Variable f) (Variable a)))
                     (Variable x) (Bool False)
    booleanLaw bigStep e `shouldBe` [(False, 0.75), (True, 0.25)]
    booleanLaw den e `shouldBe` [(False, 0.75), (True, 0.25)]
    booleanLaw smallStepIterated e `shouldBe` [(False, 0.75), (True, 0.25)]
  it "restores the caller after a shadowing binding in a sequence" $ do
    -- Lexical scope: the inner x does not escape, so the result is True.
    let x = Id ("x", 𝔹)
        e = Let (Val x (Bool True)) $
              Sequence
                (Let (Val x (Bool False)) (Bool True))
                (Variable x)
    booleanLaw bigStep e `shouldBe` [(True, 1)]
    booleanLaw den e `shouldBe` [(True, 1)]
    booleanLaw smallStepIterated e `shouldBe` [(True, 1)]
  it "never captures a source variable with a generated temporary name" $ do
    let xTemp2 = Id ("xTemp_2", 𝔹)
        e = Let (Val xTemp2 (Bool True)) $
              Pair (Bool False) (Variable xTemp2)
    smallStepPairSecond e `shouldBe` [(True, 1)]
  it "rejects a source program that uses the reserved temporary prefix" $ do
    let bad = Let (Val (Id ("#x", 𝔹)) (Bool True)) (Variable (Id ("#x", 𝔹)))
        entryPoints =
          [ ("big-step", bigStep)
          , ("denotational", den)
          , ("small-step", smallStepIterated)
          ]
    mapM_ (\(_, sem) ->
        evaluate (booleanLaw sem bad) `shouldThrow` reservedPrefixError)
      entryPoints
  it "rejects the reserved prefix through the traced small-step entry point" $ do
    let bad = Let (Val (Id ("#x", 𝔹)) (Bool True)) (Variable (Id ("#x", 𝔹)))
    evaluate (tracedLaw bad) `shouldThrow` reservedPrefixError
    where
      tracedLaw e =
        let T ev = smallStepIteratedTraced e initEnv
            values = fmap fst $ State.runStateT ev (initMem, S Map.empty)
            Dist.Cons outcomes = Dist.norm values
        in outcomes

smallStepPairSecond :: Expr ('TProduct 'TBool 'TBool) -> [(Bool, Double)]
smallStepPairSecond e =
  let T ev = smallStepIterated e initEnv
      values = fmap fst $ State.runStateT ev (initMem, S Map.empty)
      Dist.Cons outcomes = Dist.norm values
  in map (\(PairVal _ (BoolVal b) _, p) -> (b, p)) outcomes

reservedPrefixError :: ErrorCall -> Bool
reservedPrefixError (ErrorCall msg) =
  List.isInfixOf "reserved prefix" msg && List.isInfixOf "#x" msg
