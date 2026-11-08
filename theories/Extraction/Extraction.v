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
From Stdlib Require Import Arith ExtrOcamlBasic ExtrOcamlNatBigInt ExtrOcamlNativeString.
From ShiftedNames.Core Require Import Label Syntax.

(** Comparisons on [nat] that [ExtrOcamlNatBigInt] does not cover. *)
Extract Inlined Constant Nat.ltb => "Big_int_Z.lt_big_int".
Extract Inlined Constant Nat.leb => "Big_int_Z.le_big_int".
Extract Inlined Constant Compare_dec.lt_dec => "Big_int_Z.lt_big_int".

(** Parity and halving, used to index Braun trees. *)
Extract Inlined Constant Init.Nat.even =>
  "(fun n -> Big_int_Z.sign_big_int (Big_int_Z.and_big_int n Big_int_Z.unit_big_int) = 0)".
Extract Inlined Constant Init.Nat.div2 => "(fun n -> Big_int_Z.shift_right_big_int n 1)".
Extract Inlined Constant PeanoNat.Nat.even =>
  "(fun n -> Big_int_Z.sign_big_int (Big_int_Z.and_big_int n Big_int_Z.unit_big_int) = 0)".
Extract Inlined Constant PeanoNat.Nat.div2 => "(fun n -> Big_int_Z.shift_right_big_int n 1)".

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
