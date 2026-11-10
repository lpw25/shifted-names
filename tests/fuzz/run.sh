#!/bin/sh
# Search for expressions that are semantically equal under many random
# interpretations of their atoms but normalise differently.
# Usage: tests/fuzz/run.sh [iterations] [seed]   (after `make`)
set -e
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$(mktemp -d)
cp "$root/tests/fuzz/NormExtract.v" "$root/tests/fuzz/fuzz.ml" "$out/"
cd "$out"
rocq compile -w none -R "$root/theories" ShiftedNames NormExtract.v
ocamlfind ocamlopt -w -a -package zarith -linkpkg norm.mli norm.ml fuzz.ml -o fuzz
./fuzz "$@"
