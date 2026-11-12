#!/bin/sh
# Runs the layered-form fuzzer over a few seeds and modes.  From the repository root, after make.
set -e
dir=$(mktemp -d)
for cfg in "1 500 4 conc" "2 500 4 var" "3 500 4 part" "4 200 6 var"; do
  set -- $cfg
  python3 tests/fuzz/layers.py "$1" "$2" "$3" "$4" > "$dir/t.v"
  echo "seed $1, $2 expressions, depth $3, $4:"
  (cd "$dir" && rocq compile -q -R "$OLDPWD/theories" ShiftedNames t.v 2>&1 | grep "= " )
done
rm -rf "$dir"
