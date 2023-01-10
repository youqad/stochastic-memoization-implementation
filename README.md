# Mini Stochastic Memoization Language

This project implements a mini probabilistic language in Haskell, with fresh name generation of atoms (cf. Pitt's nominal sets) and stochastic memoization of constant Bernoulli functions, by updating a bipartite graph (acting as a memoization table). 

To bypass Haskell's default type-system limitations, we used a trick with singleton GADTs (mentioned, e.g. here: https://homepages.inf.ed.ac.uk/slindley/papers/hasochism.pdf) to implement a fragment of dependent types, which enabled us to get "sound by construction" (big-step, small-step operational, and denotational) semantics. 

```hs
smallStep :: Expr a -> EnvVal -> T (ExprOrValue a)
bigStep :: Expr a -> EnvVal -> T (Value a)
den :: Expr a -> EnvVal -> T (Value a)
```

To build the project, use `stack build`. To run the automatic tests, use `stack build --test` or `stack test`. The Main module can be run with `stack run minimemo-exe`.

The Main module is in `app/Main.hs`, and all the libraries (specifying syntax, semantics, values (where the monad and values are defined), environments (where the environment and the bigraph memo-table are written)) are in the folder `src`. 

NB: when we say "complete" for `bigStep` and `smallStep`, we mean "completing" the bipartite graph: all the edges between left nodes (function labels) and right nodes (atom labels) that haven't been determined yet are chosen at random.