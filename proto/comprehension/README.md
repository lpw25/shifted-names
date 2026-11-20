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
- `forms.py`: the context-form pass of `Core/CForm.v`, followed by
  `HNorm` without `relnf`, compared on every word with `HNorm` with
  `relnf` (`python3 forms.py`, a few minutes).
- `rforms.py`: the same pass, reworked so that a step only touches what moves (the expression
  is processed from its end; new items are placed by insertion; only items that just arrived
  are tried against the next form). `rforms_check.py`: the canonicity check;
  `rforms_time.py`: timings with moves counted.

- `pipe_check.py`: canonicity of the whole pipeline (a pass, then `HNorm`
  without `relnf`) against meaning in sampled generic models.
  `python3 pipe_check.py [rl|rlr] N`.

  Length 4, 12 models (unsound / missed meanings):

  | set | words | meanings | `rforms` | `rlr` | `HNorm`+`relnf` |
  |---|---|---|---|---|---|
  | g, h, k; g<h, k<h; no lifts | 309,325 | 126,316 | 0 / 8 | 0 / 360 | 0 / 0 |
  | a<b<c; lifts | 780,391 | 41,878 | 0 / 0 | 0 / 0 | 0 / 0 |

  With every pair of labels ordered, both passes are canonical. Where some
  labels are unordered:

  - `rforms` misses aliases across forms that do not compose, e.g.
    `Wh Eg(g1) Eg(k0) Eg(h0)` and `Wh Eg(h0) Eg(k0) Eg(h0)`. The left
    form reads the `g` the right form pushed (`g0`), or the `h0` it
    stands for; with `h0` the output `h` cannot move right.
  - `rlr` (`rlr.py`, the same steps processed left to right) also leaves
    reads below outputs placed after them, e.g. `Eg(g0) Wk Wh`.
