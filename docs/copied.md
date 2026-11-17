# Copied models

A wider class of models than the interleaved models of `Core/IModel.v`,
defined in `Core/CModel.v`.

## The models

- **Copies.** A label denotes several disjoint sequences of variables,
  its *copies*, indexed by a *phase* `p`. `cseq h p i` is index `i` of
  copy `p` of `h`.
- **Entries.** An entry on `h` takes index 0 of every copy of `h`. A
  variable named in its target is read in the phase of the variable it
  consumed. For example, `⟦ h as v; · as v \ · as v ⟧` sends index 0 of
  copy `p` of `h` to index 0 of copy `p` of `·`.
- **Weakenings.** Weakenings and entries act on each copy of their own
  label as in an interleaved model, and leave every other variable
  alone.
- **Consistency with the facts** (`ccons`):
  - labels the facts order share no variable, in any copies;
  - if index 0 of a copy of `g` is index 0 of a copy of `h`, the two
    copies have the same phase.
- **Interleaved models are copied models** (`emb`, `emb_ccons`). Each
  variable is repeated once per phase, with no sharing between phases.
  The embedding keeps the meaning (`emb_cden`). So equality in every
  copied model implies equality in every interleaved model, and in
  every standard interpretation.

## Why

In an interleaved model, "`v` is `a`" and "`⟦ \ b as _ ⟧ v` is `a`"
together force `⟦ \ b as _ ⟧` to fix `v`, and so to fix
`⟦ \ b as _ ⟧ v`. That makes `r1` and `r2` of `Core/HEtaGap.v` equal,
which the normaliser cannot see. In a copied model, `v` and
`⟦ \ b as _ ⟧ v` may be index 0 of two different copies of `a`.
"Is `a`" behaves as a join of "is index 0 of copy `p` of `a`" over all
`p`, distinct from each of them.

## The normaliser's laws hold

Each rule of `HNorm` and of the eta pass in `HEta`, with what justifies
it in copied models (all in `Core/CModel.v`):

| Rule | Justification |
|---|---|
| `⟦ \ h as _ ⟧` then an entry on `h` cancel | `ca_cancel` |
| an entry on `h` whose target is what `h`'s index 0 becomes, then `⟦ \ h as _ ⟧`, goes (absorption) | `ca_id_rename`, plus: steps on `h` keep a variable's copy, and steps on ordered labels keep its place (`cpos_csh`, `cpos_cush`) |
| steps on ordered labels commute (sorting) | `csh_comm`, `cush_comm`, `csh_cush_comm`, `cat0_csh_ord`, `cat0_cush_ord` |
| lifts keep index 0 of every copy | `ca_lift_at0` |
| a payload without a payload atom drops bound-label steps before its first atom | `bound_off` |
| dead entries: after `⟦ \ h as _ ⟧` and steps that cancel to steps on labels ordered against `h`, no variable is at index 0 of any copy of `h` | `cat0_csh`, `cush_csh`, `csh_cush`, `cpos_csh`, `cpos_cush` |
| stuck lookups and payloads keep only the steps the walk can reach | `cpos_off`, `cpos_csh` |
| **new:** two tests with the same target commute | `ctest_comm` (uses the phase condition) |

**What is not proved.** `HNorm` has no formal semantics for its words in
either class of models. The rows above are proved at the level of
expressions and single variables, and the step from them to each word
rule is argued, not mechanised.
