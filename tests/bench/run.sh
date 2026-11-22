#!/bin/sh
# Extract the λ example's substitution with workloads and time them.
# Usage: tests/bench/run.sh [depth] [width] [church]   (after `make`)
set -e
root=$(cd "$(dirname "$0")/../.." && pwd)
out=$(mktemp -d)
cp "$root/tests/bench/LambdaBench.v" "$root/tests/bench/bench.ml" "$out/"
cd "$out"
rocq compile -w none -R "$root/theories" ShiftedNames LambdaBench.v
ocamlfind ocamlopt -w -a -O3 -package zarith,unix -linkpkg lambda.mli lambda.ml bench.ml -o bench 2>/dev/null \
  || ocamlfind ocamlopt -w -a -package zarith,unix -linkpkg lambda.mli lambda.ml bench.ml -o bench
./bench "$@"
