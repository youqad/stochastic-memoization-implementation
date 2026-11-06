{-# LANGUAGE DataKinds, GADTs #-}
module ScopeSpec (spec) where
import Test.Hspec
import qualified Data.List as List
import qualified Numeric.Probability.Distribution as Dist
import qualified Control.Monad.State as State
import qualified Data.Map as Map
import Syntax
import Environment
import Values
import Semantics

booleanLaw :: (Expr 'TBool -> EnvVal -> T (Value 'TBool)) -> Expr 'TBool -> [(Bool, Rational)]
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
  it "sequence shadowing preserves the caller's binding" $ do
    let x = Id ("x", 𝔹)
        e = Let (Val x (Bool True)) $
              Sequence
                (Let (Val x (Bool False)) (Bool True))
                (Variable x)
    booleanLaw bigStep e `shouldBe` [(True, 1)]
    booleanLaw den e `shouldBe` [(True, 1)]
    booleanLaw smallStepIterated e `shouldBe` [(True, 1)]
  it "source binding survives a generated temporary" $ do
    let xTemp2 = Id ("xTemp_2", 𝔹)
        e = Let (Val xTemp2 (Bool True)) $
              Pair (Bool False) (Variable xTemp2)
    smallStepPairSecond e `shouldBe` [(True, 1)]
  it "# prefix on generated names in traces" $ do
    let e = Let (Val (Id ("xTemp_2", 𝔹)) (Bool True)) $
              Pair (Bool False) (Variable (Id ("xTemp_2", 𝔹)))
        T ev = smallStepIteratedTraced e initEnv
        dist = State.evalStateT ev (initMem, S Map.empty)
    Dist.pretty show dist `shouldSatisfy` List.isInfixOf "#xTemp_2"
  it "extra # for source names beginning with #" $ do
    let e = Let (Val (Id ("#xTemp_2", 𝔹)) (Bool True)) $
              Pair (Bool False) (Variable (Id ("#xTemp_2", 𝔹)))
        T ev = smallStepIteratedTraced e initEnv
        trace = Dist.pretty show (State.evalStateT ev (initMem, S Map.empty))
    trace `shouldSatisfy` List.isInfixOf "##xTemp_2"
    List.isInfixOf "#xTemp_2" (replace "##xTemp_2" "" trace) `shouldBe` True
  it "source names beginning with #" $ do
    let e = Let (Val (Id ("#xTemp_2", 𝔹)) (Bool True)) (Variable (Id ("#xTemp_2", 𝔹)))
    booleanLaw bigStep e `shouldBe` [(True, 1)]
    booleanLaw den e `shouldBe` [(True, 1)]
    booleanLaw smallStepIterated e `shouldBe` [(True, 1)]

smallStepPairSecond :: Expr ('TProduct 'TBool 'TBool) -> [(Bool, Rational)]
smallStepPairSecond e =
  let T ev = smallStepIterated e initEnv
      values = fmap fst $ State.runStateT ev (initMem, S Map.empty)
      Dist.Cons outcomes = Dist.norm values
  in map (\(PairVal _ (BoolVal b) _, p) -> (b, p)) outcomes

replace :: String -> String -> String -> String
replace old new = go
  where
    go [] = []
    go s@(c : cs)
      | old `List.isPrefixOf` s = new ++ go (drop (length old) s)
      | otherwise = c : go cs
