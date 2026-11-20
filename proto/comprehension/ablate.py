"""Ablation: which of the HNorm optimisations earn their keep (Python wall time and growth).

  A   lists, lookups as in Coq (hcost follow='coq')
  A'  lists, per-cell summaries + trimming walk + memoised payloads (hcost follow='fast')
  B   lists, cones as (explicit set, whole suffix) (hcone)
  C   blocks of treaps, trimming walk (htrie mode='walk')
  D   blocks of treaps, cones as tries (htrie mode='cone')

python3 ablate.py N [family ...]
"""
import sys, time
sys.setrecursionlimit(200000)
import hcost, hcone, htrie
from hcost import FAMILIES

def run(variant, fam, n):
    mk, _ = FAMILIES[fam]; facts = htrie.facts_of(fam, n); e = mk(n)
    if variant in ('A', "A'"):
        h = hcost.H(facts); hcost.H.follow = 'coq' if variant == 'A' else 'fast'
    elif variant == 'B':
        h = hcone.HC(facts); hcone.HC.follow = 'cone'
    else:
        h = htrie.T(facts); htrie.T.mode = 'walk' if variant == 'C' else 'cone'
    t0 = time.time(); h.norm(e, 1); return time.time() - t0

if __name__ == '__main__':
    n = int(sys.argv[1]); fams = sys.argv[2:] or list(FAMILIES)
    vs = ['A', "A'", 'B', 'C', 'D']
    print(f'n={n}  ' + '  '.join(f'{v:>8s}' for v in vs))
    for f in fams:
        row = []
        for v in vs:
            # small sizes: repeat for a measurable time
            reps = max(1, 2000 // max(n, 1)) if n <= 200 else 1
            row.append(sum(run(v, f, n) for _ in range(reps)) / reps)
        print(f'{f:8s} ' + '  '.join(f'{t*1000:7.2f}ms' for t in row), flush=True)
