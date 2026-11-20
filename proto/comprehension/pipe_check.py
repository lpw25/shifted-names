"""Canonicity of the whole normaliser against comprehension models.

The pipeline: a context-form pass (rforms.R, or another with the same interface), then HNorm
without relnf (pnorm.N(fix=False)) on its forms.  Every word up to a length is grouped by its
meaning in sampled generic comprehension models (gmodel2.GModel), as in checkpy.py:

- unsound: two words with the same output and different meanings;
- missed:  words with the same meaning (in every sampled model) and different outputs.

HNorm with relnf (pnorm.N(fix=True)) is reported alongside, as a reference.

    python3 pipe_check.py [rlr]      (rlr: the left-to-right pass of rlr.py)
"""
import sys, random
sys.path.insert(0, '.')
from gmodel import env
from gmodel2 import GModel, check_commute
from check3 import run, fmt
from pnorm import N, BOUND
from forms import norm_forms
from rforms import R, of_word
import checkpy

def main(Pass, labels, LT, n, nmodels=30, seed=0, vidx=(0, 1), lifts=True, show=2):
    rng = random.Random(seed)
    models = [GModel(labels, LT, rng) for _ in range(nmodels)]
    for m in models: check_commute(m, rng)
    xs = [env(m.tapes, rng=rng) for m in models]
    nn = N(LT, False); nf = N(LT, True)
    by_sig = {}      # meaning -> {pipeline output: word}
    by_out = {}      # pipeline output -> {meaning: word}
    ref = {}         # meaning -> set of HNorm-with-relnf outputs
    nw = 0
    for w in checkpy.words(labels, n, vidx, lifts):
        nw += 1
        sg = tuple(tuple(sorted(run(m, w, x).items())) for m, x in zip(models, xs))
        out = norm_forms(nn, Pass(nn).run(of_word(w, BOUND)))
        by_sig.setdefault(sg, {}).setdefault(out, w)
        by_out.setdefault(out, {}).setdefault(sg, w)
        ref.setdefault(sg, set()).add(nf.norm(tuple(w)))
    unsound = [v for v in by_out.values() if len(v) > 1]
    missed = [v for v in by_sig.values() if len(v) > 1]
    ref_missed = sum(len(v) - 1 for v in ref.values())
    print(f"{labels} {sorted(LT)} n<={n} lifts={lifts}: words={nw} meanings={len(by_sig)} "
          f"unsound={len(unsound)} missed={sum(len(v) - 1 for v in missed)} (HNorm+relnf missed={ref_missed})", flush=True)
    for v in unsound[:show]: print('   unsound:', ' | '.join(fmt(w) for w in v.values()))
    for v in sorted(missed, key=lambda v: sum(len(w) for w in v.values()))[:show]:
        print('   missed: ', ' | '.join(fmt(w) for w in v.values()))
    return len(unsound), sum(len(v) - 1 for v in missed)

SETS = [
    (['g', 'h', 'k'], {('g', 'h'), ('k', 'h')}),
    (['a', 'b', 'c'], {('a', 'b'), ('b', 'c')}),
    (['a', 'b'], set()),
    (['g', 'h', 'm'], {('g', 'h')}),
    (['a', 'b', 'c', 'd'], {('a', 'c'), ('b', 'c'), ('c', 'd')}),
]

if __name__ == '__main__':
    Pass = R
    if len(sys.argv) > 1 and sys.argv[1] == 'rlr':
        from rlr import RLR as Pass
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    for labels, LT in SETS:
        main(Pass, labels, LT, n if len(labels) <= 3 else min(n, 2))
