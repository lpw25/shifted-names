(** * Extraction settings for the library

    Import this file before extracting code that uses the library.

    - Numbers ([nat]) become Zarith integers, and so do extension witnesses
      ([ext]): a witness is extracted as the number of binders it stands
      for, so going under a binder is [succ] and [ext_depth] is the
      identity.
    - Strings become OCaml strings, and trie keys are computed from them
      without building intermediate lists.
    - The realizers below are trusted (unverified) OCaml code, in the same
      way as the stdlib's [ExtrOcamlNatBigInt]; each one computes exactly
      the Rocq function it replaces. *)

From Stdlib Require Extraction.
From Stdlib Require Import PArith Arith ExtrOcamlBasic ExtrOcamlNatBigInt ExtrOcamlNativeString.
From ShiftedNames.Core Require Import Label Syntax Lookup.

(** Comparisons on [nat] that [ExtrOcamlNatBigInt] does not cover. *)
Extract Inlined Constant Nat.ltb => "Big_int_Z.lt_big_int".
Extract Inlined Constant Nat.leb => "Big_int_Z.le_big_int".
Extract Inlined Constant Compare_dec.lt_dec => "Big_int_Z.lt_big_int".

(** Halving, used for the sizes of skew-binary trees, and [min]. *)
Extract Inlined Constant Init.Nat.div2 => "(fun n -> Big_int_Z.shift_right_big_int n 1)".
Extract Inlined Constant PeanoNat.Nat.div2 => "(fun n -> Big_int_Z.shift_right_big_int n 1)".
Extract Inlined Constant Init.Nat.min => "Big_int_Z.min_big_int".
Extract Inlined Constant PeanoNat.Nat.min => "Big_int_Z.min_big_int".

(** Extension witnesses are their depth. *)
Extraction Implicit ext_under [K L].
Extract Inductive ext => "Big_int_Z.big_int"
  [ "Big_int_Z.zero_big_int" "Big_int_Z.succ_big_int" ]
  "(fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO () else fS (Big_int_Z.pred_big_int n))".
Extraction Implicit ext_depth [N M K L].
Extraction Implicit ext_shift [N M K L].
Extraction Implicit ext_unshift [N M K L].
Extraction Implicit ext_app [N M K L K' L'].
Extraction Implicit ext_mid [N P K L].
Extraction Implicit ext_left [N P K L].
Extraction Implicit ext_right [N P K L].
Extract Inlined Constant ext_depth => "(fun e -> e)".

(** Trie keys of labels, without going through character lists: the same
    bits as [string_key], last character innermost, bit 7 first. *)
Extract Constant string_key =>
  "(fun s -> let p = ref XH in
     for i = String.length s - 1 downto 0 do
       let c = Char.code s.[i] in
       for b = 7 downto 0 do
         p := (if (c lsr b) land 1 = 1 then XI !p else XO !p)
       done
     done; !p)".

(** Decoding a key back to its label ([key_label]), reading eight bits per
    character into a buffer instead of through bit lists. *)
Extract Constant key_label =>
  "(fun k -> match k with
     | XH -> Some None
     | XI _ -> None
     | XO q ->
       let buf = Buffer.create 16 in
       let rec go p c i = match p with
         | XH -> if i = 0 then Some (Some (Buffer.contents buf)) else None
         | XO q -> step q c i
         | XI q -> step q (c lor (1 lsl i)) i
       and step q c i =
         if i = 7 then (Buffer.add_char buf (Char.chr c); go q 0 0)
         else go q c (i + 1) in
       go q 0 0)".

(** The lookups' section variables [k0 t0 B0] / [i0 s0 B0] only appear in
    the types of their location proofs. *)
Extraction Implicit aget_with' [k0 t0 B0].
Extraction Implicit ktnth_with' [i0 s0 B0].
Extraction Implicit spnth_with' [i0 s0 B0].
Extraction Implicit knth_with' [i0 s0 B0].
