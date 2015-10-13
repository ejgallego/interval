Require Import Reals.
Require Import List.
Require Import Coquelicot.
Require Import Interval_missing.
Require Import ZArith.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float_full.
Require Import Interval_integral.
Require Import Interval_bisect.

Module IntervalTactic (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.
Module A := IntervalAlgos I.

Section Integrability.

Lemma eval_implies_integrable prog a b boundsa boundsb proga progb prec bounds i:
  let ia := nth 0 (A.BndValuator.eval prec proga (map A.interval_from_bp boundsa)) I.nai in
  let ib := nth 0 (A.BndValuator.eval prec progb (map A.interval_from_bp boundsb)) I.nai in
  let f := fun x => nth 0 (eval_real prog (x::map A.real_from_bp bounds)) R0 in
  let fi := nth 0 (A.BndValuator.eval prec prog (i::map A.interval_from_bp bounds)) I.nai in 
  (match fi with Interval_interval_float.Inan => false | _ => true end = true) ->
 contains (I.convert i) (Xreal a) ->
 contains (I.convert i) (Xreal b) ->
 ex_RInt f a b.
Proof.
elim: prog.
Print term.
Print binary_op.
move => ia ib f fi Hreasonable Hconta Hcontb.

About eval_inductive_prop.
Search _ term eval_real.
Check eval_generic.
Search _ term.

End Integrability.
