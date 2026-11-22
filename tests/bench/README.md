# Timing the extracted substitution

`run.sh [depth] [width] [church]` extracts the λ example's substitution
(`LambdaBench.v`) and times, in OCaml:

- opening every binder of `λ^depth. body` with a name and closing it again;
- instantiating the outermost binder of that term, under the rest;
- composing `width` singleton substitutions `⟦ x := u ⟧`, and `width`
  renamings in a chain, and applying them to a term of `width` names;
- the same substitutions applied one by one;
- normalising `mult c c` on Church numerals with a locally nameless
  normal-order normaliser (binders opened with fresh names, redexes
  instantiated).
