#!/bin/sh
# Time names on a generated goal family: tactic time, then Qed (and, for
# MV and MO, cbn first).  Usage (after `make`):
#   tests/bench/names/run.sh FAMILY N...
# FAMILY is one of D PC SN VR VT VA NS MV MO (see gen.py).
set -e
root=$(cd "$(dirname "$0")/../../.." && pwd)
gen="$root/tests/bench/names/gen.py"
fam=$1; shift
out=$(mktemp -d)
for n in "$@"; do
  f="$out/B${fam}${n}.v"
  python3 "$gen" "$fam" "$n" > "$f"
  times=$(cd "$out" && rocq compile -w none -Q "$root/theories" ShiftedNames "$(basename "$f")" 2>&1 \
          | grep -o "Finished transaction in [0-9.]* secs" | grep -o "[0-9.]* secs" | tr '\n' ' ')
  echo "$fam $n: $times"
done
