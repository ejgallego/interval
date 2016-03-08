Require Import List.
Require Import ZArith.
Require Import Coquelicot coquelicot_compl.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float_full.
Require Import Interval_bisect.

Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrnat.

Section Prelude.

Variable Ftype : Type.

Definition notInan (fi : Interval_interval_float.f_interval Ftype) :=
  match fi with
    | Interval_interval_float.Inan => false
    | _ => true end = true.

End Prelude.

Module Integrability (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.
Module A := IntervalAlgos I.

Section Integrability.

Variable prec : I.precision.
Definition notInan := notInan F.type.

(* we ensure that we get the former result by using the new one *)
Lemma continuousProg :
  forall prog bounds m i x,
  contains (I.convert i) (Xreal x) ->
  notInan (nth m (A.BndValuator.eval prec prog (i :: map A.interval_from_bp bounds)) I.nai) ->
  continuous (fun x => nth m (eval_real prog (x :: map A.real_from_bp bounds)) R0) x.
Proof.
move => prog bounds m i x Hcontains HnotInan.
apply: A.continuous_eval_ext.
generalize (A.BndValuator.eval_correct_ext prec prog bounds m i (Xreal x) Hcontains).
revert HnotInan.
case: (nth _ _ _) => //.
case: (nth _ _ _) => //.
Qed.

Lemma integrableProg :
  forall prog bounds m a b i,
  (forall x, Rmin a b <= x <= Rmax a b -> contains (I.convert i) (Xreal x)) ->
  notInan (nth m (A.BndValuator.eval prec prog (i :: map A.interval_from_bp bounds)) I.nai) ->
  ex_RInt (fun x => nth m (eval_real prog (x :: map A.real_from_bp bounds)) R0) a b.
Proof.
move => prog bounds m a b i Hcontains HnotInan.
apply: ex_RInt_continuous.
intros z Hz.
apply: continuousProg HnotInan.
by apply: Hcontains.
Qed.

End Integrability.
End Integrability.
