# Comprehension models: test harness

See `docs/comprehension.md`.

- `gmodel.py`, `gmodel2.py`: comprehension models in sets. Each label has
  a tape; its comprehension pops that tape after an invertible mixing of
  the leading cells of a few tapes (`gmodel2.GModel`). Labels the facts
  order get disjoint tapes and regions, so their comprehensions commute.
- `examples.py`: the named examples, checked in random models.
- `gen2.py`: writes `coq/NAME.v`, which normalises every word up to a
  length with `HNorm` against one shared table and prints the ids.
- `check3.py NAME`: groups the words by `HNorm` id and compares with the
  meaning in random models: an "unsound" class has words of different
  meaning; "merged" classes have the same meaning in every sampled model.

Run from this directory:

    mkdir -p coq && python3 gen2.py
    (cd coq && rocq c -R ../../../theories ShiftedNames abv4.v > abv4.out)
    python3 check3.py abv4
