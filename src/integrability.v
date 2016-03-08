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

Lemma domain_correct unop a b x :
  (notXnan b -> b = Xreal (a x) /\ continuous a x) ->
  notXnan ((unary ext_operations unop) b) ->
  (unary ext_operations unop) b = Xreal (unary real_operations unop (a x)) /\
  continuous (fun x0 : R => unary real_operations unop (a x0)) x.
Proof.
move => Hb HbnotXnan.
case Hbnan: b Hb => [|b1] // Hb.
rewrite Hbnan /= in HbnotXnan.
by case unop in HbnotXnan.
case: Hb => // Hb Hcontax.
move: HbnotXnan.
rewrite Hbnan Hb => {Hbnan Hb b1} HnotXnan.
split.
case: unop HnotXnan => //=.
- by case is_zero.
- by case is_negative.
- rewrite /Xtan /tan /Xdiv /Xcos /Xsin.
  by case is_zero.
- by case is_positive.
- case => [||p] // .
  by case is_zero.
case: unop HnotXnan => /=.
- move => _. by apply: continuous_opp.
- move => _. by apply: continuous_Rabs_comp.
- move => HnotXnan.
  apply: continuous_Rinv_comp => // Ha.
  move: HnotXnan.
  by rewrite Ha is_zero_correct_zero.
- move => _. by apply: continuous_mult.
- move => HnotXnan.
  apply: continuous_sqrt_comp => //.
  by case: is_negative_spec HnotXnan.
- move => _. by apply: continuous_cos_comp.
- move => _. by apply: continuous_sin_comp.
- move => HnotXnan.
  apply: continuous_comp => //.
  apply: continuous_tan => Ha.
    move: HnotXnan.
    by rewrite /Xtan /Xsin /Xcos /Xdiv Ha is_zero_correct_zero.
- move => _. by apply: continuous_atan_comp.
- move => _. by apply: continuous_exp_comp.
- move => HnotXnan.
  apply: continuous_comp => //.
  apply: continuous_ln.
  by case: is_positive_spec HnotXnan.
- move => n.
  rewrite /powerRZ.
  case: n => [|n|n] HnotXnan.
  + exact: continuous_const.
  + apply: (continuous_comp a (fun x => pow x _)) => //.
    apply: ex_derive_continuous.
    apply: ex_derive_pow.
    exact: ex_derive_id.
  + case: is_zero_spec HnotXnan => // Ha _.
    apply: continuous_comp.
    apply: (continuous_comp a (fun x => pow x _)) => //.
    apply: ex_derive_continuous.
    apply: ex_derive_pow.
    exact: ex_derive_id.
    apply: continuous_Rinv.
    exact: pow_nonzero.
Qed.

Module Integrability (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.
Module A := IntervalAlgos I.

Section Integrability.

Variable prec : I.precision.
Definition notInan := notInan F.type.

Lemma continuousProg2 :
  forall prog bounds x m,
  notXnan (nth m (eval_ext prog (Xreal x :: map A.xreal_from_bp bounds)) Xnan) ->
  continuous (fun x => nth m (eval_real prog (x :: map A.real_from_bp bounds)) R0) x.
Proof.
intros prog bounds x.
rewrite /eval_ext /eval_real.
intros m H.
eapply proj2.
revert H.
apply: (eval_inductive_prop_fun _ _ (fun (f : R -> R) v => notXnan v -> v = Xreal (f x) /\ continuous f x)) => //.
intros f1 f2 Heq b H Hb.
case: (H Hb) => {H} H H'.
split.
by rewrite -Heq.
now eapply continuous_ext.
move => unop a b Hb HnotXnan.
exact: domain_correct.
(* case of binary operator *)
case => a1 a2 b1 b2 Ha1 Ha2 HnotXnan /=.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_plus.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_minus.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => _ [] // -> Hconta1 [] // -> Hconta2.
  by split => //; apply: continuous_mult.
- move: HnotXnan Ha1 Ha2.
  case: b1 => [|b1] // ;case: b2 => [|b2] // .
  move => HnotXnan [] // Heq1 Hconta1 [] // Heq2 Hconta2.
  split => // .
  + move: HnotXnan.
    rewrite /binary /ext_operations /Xdiv.
    case: (is_zero b2) => // .
    by inversion Heq1; inversion Heq2.
  + apply: continuous_mult => // .
    apply: continuous_Rinv_comp => // Habs .
    by move: Heq2 HnotXnan => ->; rewrite Habs /= is_zero_correct_zero.
intros [|n].
simpl.
intros _.
apply (conj eq_refl).
apply continuous_id.
simpl.
destruct (le_or_lt (length bounds) n).
rewrite nth_overflow => //.
by rewrite map_length.
rewrite (nth_indep _ _ (Xreal 0)).
replace (map A.xreal_from_bp bounds) with (map Xreal (map A.real_from_bp bounds)).
rewrite map_nth.
intros _.
apply (conj eq_refl).
apply continuous_const.
rewrite map_map.
apply map_ext.
now intros [].
by rewrite map_length.
Qed.

(* we ensure that we get the former result by using the new one *)
Lemma continuousProg :
  forall prog bounds m i x,
  contains (I.convert i) (Xreal x) ->
  notInan (nth m (A.BndValuator.eval prec prog (i :: map A.interval_from_bp bounds)) I.nai) ->
  continuous (fun x => nth m (eval_real prog (x :: map A.real_from_bp bounds)) R0) x.
Proof.
move => prog bounds m i x Hcontains HnotInan.
apply: continuousProg2.
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
