(** Extract the λ example's substitution with the library's extraction
    settings (run by [tests/extraction/run.sh]). *)
From ShiftedNames.Extraction Require Import Extraction.
From ShiftedNames.Examples Require Import Lambda.
Extraction "lambda.ml" LS.subst topen tclose inst.
