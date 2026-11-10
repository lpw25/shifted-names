(** Extract the normaliser and the raw denotation for the normal-form
    fuzzer ([tests/fuzz/run.sh]). *)
From ShiftedNames.Extraction Require Import Extraction.
From ShiftedNames.Core Require Import Label Var Adjustment Normalise.
Extraction "norm.ml" anorm aeden rapply rpidentity ridentity.
