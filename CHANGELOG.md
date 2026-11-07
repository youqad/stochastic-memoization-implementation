# Changelog for `minimemo`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

## 0.3.0.0 - 2026-11-07

### Fixed

- Small-step evaluation with a shadowed name: a shadowing `let` in a `match` scrutinee or in a nested `if` guard gave a different result from big-step and denotational evaluation.
- `stack test` with `lts-20.2` (GHC 9.2.5): `test/SemanticsSpec.hs` now enables `GADTs`.

### Changed

- Small-step keeps a stack of saved environments: the construct at spine depth d pushes a frame when the stack has at most d frames, and pops it when its subterm becomes a value (`withRestore`, also used by `match`).
- The small-step state `𝒯`, which the observer of `iterateSmallStep` receives, is a triple (saved environments, environment of temporaries, current environment) instead of a 4-tuple with a flag.
- Random test programs reuse names in scope, so the equivalence properties test shadowing.
- `package.yaml` and `minimemo.cabal` point to this repository.
- `src/Environment.hs`, `src/Semantics.hs`, `src/Syntax.hs` and `src/Values.hs` are no longer executable.

### Removed

- `Flag` and `setFlag`.

## 0.2.0.0 - 2026-11-06

### Changed

- Memo entries are sampled at allocation, following the paper.
- Laws use exact rational weights and are compared with `Dist.equal`, without tolerance; `runBooleanLaw` returns `Rational` weights.
- `Semantics` exports all remaining definitions except `storeTemp` and `withTemp`.
- Generated names are internal, so source names are unrestricted; a source name starting with `#` prints with an extra `#`.
- `makeEnv` keeps the first binding for duplicate keys.
- The `probability` dependency is `>= 0.2.7`.

### Removed

- `smallStepIterate`, `subst` and `valueToExpr`.

## 0.1.0.0 - 2022-12-30

### Added

- First version.
