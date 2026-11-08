#!/bin/sh
# Extract the lambda example, compile it against Zarith and run a smoke test.
# Usage: tests/extraction/run.sh   (after `make`)
set -e
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$(mktemp -d)
cp "$root/tests/extraction/LambdaExtract.v" "$root/tests/extraction/main.ml" "$out/"
cd "$out"; echo "build dir: $out"
rocq compile -w none -R "$root/theories" ShiftedNames LambdaExtract.v
ocamlfind ocamlopt -package zarith -linkpkg lambda.mli lambda.ml main.ml -o main
./main
