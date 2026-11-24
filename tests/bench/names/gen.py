# Goal families for timing names (run by run.sh): python3 gen.py FAMILY N
import sys
fam, n = sys.argv[1], int(sys.argv[2])
def x(i): return '"x%04d"' % i
hdrA = '''From Stdlib Require Import String StrictProp NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Names.
Open Scope string_scope.
Section S. Context {T : nat -> Type}.
'''
hdrL = '''From Stdlib Require Import String StrictProp NArith.
From ShiftedNames.Core Require Import Label Var Adjustment Indexed Syntax Subst Names.
From ShiftedNames.Examples Require Import Lambda.
Open Scope string_scope.
Section S.
'''
def lnest(items):
    s = items[0]
    for it in items[1:]: s = '(%s ⨾ %s)' % (s, it)
    return s
def tail(extra=''):
    return f'''{extra}Time names. intros _; exact I.
Time Qed.
End S.
'''
if fam == 'D':
    a = lnest(['⟦ %s := (f %d%%N) ⟧' % (x(i), i) for i in range(1, n+1)])
    print(hdrA + f'Lemma L {{N}} (f : BinNums.N -> T N) (P : adj T N N -> Prop) : P ({a}) -> True.\nProof.\n' + tail())
elif fam == 'PC':
    a = lnest(['⟦ %s := (f %d%%N); %s := (f %d%%N) ⟧' % (x(1), 2*i, x(2), 2*i+1) for i in range(1, n+1)])
    print(hdrA + f'Lemma L {{N}} (f : BinNums.N -> T N) (P : adj T N N -> Prop) : P ({a}) -> True.\nProof.\n' + tail())
elif fam == 'PN':   # an opaque term under a chain of n pairs (payloads shown)
    a = lnest(['⟦ %s := (f %d%%N); %s := (f %d%%N) ⟧' % (x(1), 2*i, x(2), 2*i+1) for i in range(1, n+1)])
    print(hdrL + f'Lemma L (M : tm 0) (f : BinNums.N -> tm 0) (P : tm 0 -> Prop) : P (M [{a}]) -> True.\nProof.\n' + tail())
elif fam == 'SN':   # n nested substitutions on an opaque term
    t = 'M'
    for i in range(1, n+1): t = '(%s [⟦ %s := (f %d%%N) ⟧])' % (t, x(i), i)
    print(hdrL + f'Lemma L (M : tm 0) (f : BinNums.N -> tm 0) (P : tm 0 -> Prop) : P {t} -> True.\nProof.\n' + tail())
elif fam == 'VR':   # a variable through a chain of renamings
    a = lnest(['⟦ %s as (fvar %s 0) ⟧' % (x(i), x(i+1)) for i in range(1, n+1)])
    print(hdrL + f'Lemma L (P : tm 0 -> Prop) : P ((tvar (fvar {x(1)} 0) : tm 0) [{a}]) -> True.\nProof.\n' + tail())
elif fam == 'VT':   # a variable through a chain of substitutions by variables (converted)
    a = lnest(['⟦ %s := (tvar (fvar %s 0)) ⟧' % (x(i), x(i+1)) for i in range(1, n+1)])
    print(hdrL + f'Lemma L (P : tm 0 -> Prop) : P ((tvar (fvar {x(1)} 0) : tm 0) [{a}]) -> True.\nProof.\n' + tail())
elif fam == 'VA':   # a variable through a chain ending in an atom (stuck lookup)
    a = lnest(['⟦ %s := (tvar (fvar %s 0)) ⟧' % (x(i), x(i+1)) for i in range(1, n+1)] + ['s'])
    print(hdrL + f'Lemma L (s : sub 0 0) (P : tm 0 -> Prop) : P ((tvar (fvar {x(1)} 0) : tm 0) [{a}]) -> True.\nProof.\n' + tail())
elif fam == 'NS':   # substitutions nested in payloads, depth n
    t = 'u0'
    for i in range(1, n+1): t = '(u [⟦ %s := %s ⟧])' % (x(i), t)
    print(hdrL + f'Lemma L (M u u0 : tm 0) (P : tm 0 -> Prop) : P (M [⟦ "y" := {t} ⟧]) -> True.\nProof.\n' + tail())
elif fam == 'MV':   # a term with n variables substituted by an n-entry substitution
    t = '(tconst 0)'
    for i in range(n, 0, -1): t = '(tapp (tvar (fvar %s 0)) %s)' % (x(i), t)
    a = lnest(['⟦ %s := (tconst %d) ⟧' % (x(i), i) for i in range(1, n+1)])
    print(hdrL + f'Lemma L (P : tm 0 -> Prop) : P (({t} : tm 0) [{a}]) -> True.\nProof.\n' + tail('Time cbn. '))
elif fam == 'MO':   # a term with n opaque subterms substituted (n nodes, one adjustment)
    t = '(tconst 0)'
    for i in range(n, 0, -1): t = '(tapp (g %d%%N) %s)' % (i, t)
    a = lnest(['⟦ %s := (tconst %d) ⟧' % (x(i), i) for i in range(1, n+1)])
    print(hdrL + f'Lemma L (g : BinNums.N -> tm 0) (P : tm 0 -> Prop) : P (({t} : tm 0) [{a}]) -> True.\nProof.\n' + tail('Time cbn. '))
