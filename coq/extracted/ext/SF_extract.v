Require Import SF_imp.
Require Import SF_tests.
Require Import RelDec.
Require Import List.
Import ListNotations.

Extraction Language Haskell.

Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Set Extraction AccessOpaque.

Extract Inductive unit    => "()" [ "()" ].
Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sum     => "Prelude.Either" [ "Prelude.Left" "Prelude.Right" ].
Extract Inductive list    => "[]" ["[]" "(:)"].
Extract Inductive prod    => "(,)" ["(,)"].
Extract Inductive sigT    => "(,)" ["(,)"].
Extract Inductive option  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor   => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(* this stuff is for quickcheck, should not have soundness implications *)
Extract Inlined Constant Bool.eqb => "(Prelude.==)".
Extract Inlined Constant option_eq_t => "(Prelude.==)".
Extract Constant T => "Prelude.Int".
 (*we should be able to change this out for any type with equality *)
Extract Inlined Constant eqb_t => "(Prelude.==)".
Extract Inlined Constant reldec_t => "(Prelude.==)".

Separate Extraction SF_imp SF_tests.
