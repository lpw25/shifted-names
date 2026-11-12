"""Random adjustment expressions for the layered form (Core/Layers.v).

    python3 layers.py SEED COUNT DEPTH MODE > t.v

MODE is conc (concrete labels), var (label variables in a known order)
or part (label variables, the order of one unknown).  Compiling the
output prints four counts: expressions the normaliser gave up on (an
order it needed is unknown), expressions with no layered form,
expressions whose layered form normalises to a different stored word,
and expressions whose layered form normalises to the same one.  The
second and third should be 0.  Then the indices of any of those, and
the total sizes of the layered forms, the stored forms, the trees and
the expressions themselves, all counting entries, outputs, lifts, atoms
and terms.
"""
import random, sys
seed=int(sys.argv[1]); n=int(sys.argv[2]); depth=int(sys.argv[3]); mode=sys.argv[4] if len(sys.argv)>4 else "conc"
random.seed(seed)
if mode=="conc":
    LABS=['(LCon "a")','(LCon "b")','(LCon "c")','LNone']
    FACTS="[]"
elif mode=="var":
    LABS=['(LAtom 0)','(LAtom 1)','(LAtom 2)','LNone']
    FACTS="[(LAtom 0, LAtom 1); (LAtom 1, LAtom 2)]"
else:
    LABS=['(LAtom 0)','(LAtom 1)','(LAtom 2)','LNone']
    FACTS="[(LAtom 0, LAtom 1)]"
def lab(named=False):
    return random.choice(LABS[:3] if named else LABS)
def aexp(d):
    if d<=0: return random.choice(["AId","AId","(AAtom %d)"%random.randint(0,1)])
    r=random.random()
    if r<0.30: return "(ACompose %s %s)"%(aexp(d-1),aexp(d-1))
    if r<0.45: return "(AOuter %s %s)"%(lab(),aexp(d-1))
    if r<0.80: return "(AInner %s %s %s)"%(lab(),texp(d-1),aexp(d-1))
    if r<0.90: return "(ALift %s %s)"%(lab(),aexp(d-1))
    if r<0.95: return "(AAtom %d)"%random.randint(0,1)
    return "AId"
def texp(d):
    r=random.random()
    if r<0.35: return "(TVarE %s %d)"%(lab(),random.randint(0,2))
    if r<0.92 or d<=0: return "(TBindE %d %s)"%(random.randint(0,3),pexp(d-1))
    return "(TShiftE %s (TVarE %s %d))"%(lab(),lab(),random.randint(0,1))
def pexp(d):
    if d<=0: return random.choice(["PId","PId","PId","(PAtom 0)"])
    r=random.random()
    if r<0.45: return "PId"
    if r<0.85: return "(PComp %s %s)"%(aexp(d-1),pexp(d-2))
    if r<0.92: return "(PShift %s %s)"%(lab(True),pexp(d-1))
    return "(PAtom %d)"%random.randint(0,1)
print("""From Stdlib Require Import String List NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise Unique Normal Shared Eval Layers.
Import ListNotations. Open Scope string_scope.
Definition O := order_of (%s : list (lexp * lexp)).
Definition classify (e : aexp) : nat * (nat * N * N * nat) :=
  let n := apmax e in
  match anorm_s n O 4 e sst0 with
  | Some (st, w) =>
      match layers n O 4 (sdefs st) w with
      | Some le =>
          let ok := match anorm_s n O 4 le st with Some (_, w') => word_eqb w w' | None => false end in
          ((if ok then 3 else 2), (csize le, N.of_nat (stored_size (sdefs st) w), N.of_nat (match tree_size n (sdefs st) w with Some k => k | None => 0 end), csize e))
      | None => (1, (0, 0%%N, 0%%N, 0))
      end
  | None => (0, (0, 0%%N, 0%%N, 0))
  end.
Definition tests : list aexp := ["""%FACTS)
print(";\n".join(aexp(depth) for _ in range(n)))
print("""].
Definition rs := Eval vm_compute in map classify tests.
Definition count k := List.length (filter (fun r => Nat.eqb (fst r) k) rs).
Eval vm_compute in (count 0, count 1, count 2, count 3).
(* how many used the rule that shares what some parties have *)
Eval vm_compute in (List.length (filter (fun e => let n := apmax e in match anorm_s n O 4 e sst0 with Some (st, w) => match layers_s n O 4 (sdefs st) w with Some _ => true | None => false end | None => false end) tests)).
Eval vm_compute in (map fst (filter (fun p => Nat.eqb (fst (snd p)) 2) (combine (seq 0 (List.length rs)) rs))).
Eval vm_compute in (map fst (filter (fun p => Nat.eqb (fst (snd p)) 1) (combine (seq 0 (List.length rs)) rs))).
Eval vm_compute in (fold_right (fun r acc => let '(a,b,c,d) := acc in let '(x,y,z,v) := snd r in (a + x, (b + y)%N, (c + z)%N, d + v)) (0, 0%N, 0%N, 0) (filter (fun r => Nat.eqb (fst r) 3) rs)).
""")
