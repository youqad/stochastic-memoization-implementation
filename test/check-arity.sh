#!/bin/sh
set -eu
cabal exec -- ghc -v0 -fno-code -isrc test/arity/Valid.hs
failed=0
for fixture in test/arity/EmptyLambda.hs test/arity/ExtraLambda.hs test/arity/EmptyApply.hs test/arity/ExtraApply.hs; do
  if diagnostic=$(cabal exec -- ghc -v0 -fno-code -isrc "$fixture" 2>&1); then
    printf '%s unexpectedly typechecked\n' "$fixture"
    failed=1
  else
    case "$diagnostic" in
      *"Couldn't match"*) printf '%s rejected by the type checker\n' "$fixture" ;;
      *) printf '%s\n' "$diagnostic"; exit 2 ;;
    esac
  fi
done
exit "$failed"
