# Prototype of the canonical graph

Executable model of `docs/canonical-graph.md`, for testing the design
before mechanising it.

| File | Contents |
|---|---|
| `graph.py` | the canonical graph: hash-consed nodes and per-label cons lists, post-shifts on references (co-de Bruijn style factoring), and evaluation of expressions (the `aexp`/`texp`/`pexp` of `Core/Normalise.v`, plus `share`) |
| `sem.py` | reference semantics: the free model (`Unique.fres`) as closures, observed on probes |
| `printer3.py` | linearisation: graph to expression, with `share` for objects referenced twice or more |
| `test_canon.py` | random expressions; graph meaning equals reference meaning (soundness); equal meanings give the same graph (canonicity) |
| `test_print.py` | round trip `graph (print (graph e)) = graph e`, and sizes |
| `test_size.py` | graph sizes and evaluation counts on families |
| `test_history.py` | start share-free, normalise, apply random operations, repeat; work and size against the share-free size of the history |
| `pretty.py` | examples, printed readably |

Run with `python3 test_canon.py SEED COUNT DEPTH` and so on.
