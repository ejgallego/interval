Require Import Reals.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_float_sig.
Require Import Interval_generic.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Interval_transcend.

Module FloatIntervalFull (F : FloatOps with Definition even_radix := true) <: IntervalOps.

Module T := TranscendentalFloatFast F.
Module I := FloatInterval F.

Definition Fle x y :=
  match F.cmp x y with
  | Xlt | Xeq => true
  | Xgt | Xund => false
  end.

Lemma Fle_correct :
  forall x y,
  Fle x y = true ->
  match I.convert_bound x, I.convert_bound y with
  | Xreal xr, Xreal yr => (xr <= yr)%R
  | _, _ => False
  end.
Proof.
intros x y.
unfold Fle.
rewrite F.cmp_correct, Interval_generic_proof.Fcmp_correct.
I.xreal_tac x.
easy.
I.xreal_tac y.
easy.
simpl.
now case Fcore_Raux.Rcompare_spec ; auto with real.
Qed.

Definition Flt x y :=
  match F.cmp x y with
  | Xlt  => true
  | _ => false
  end.

Lemma Flt_correct :
  forall x y,
  Flt x y = true ->
  match I.convert_bound x, I.convert_bound y with
  | Xreal xr, Xreal yr => (xr < yr)%R
  | _, _ => False
  end.
Proof.
intros x y.
unfold Flt.
rewrite F.cmp_correct, Interval_generic_proof.Fcmp_correct.
I.xreal_tac x.
easy.
I.xreal_tac y.
easy.
simpl.
now case Fcore_Raux.Rcompare_spec.
Qed.

(* useful only for |xi| <= pi *)
Definition cos prec xi :=
  match I.abs xi with
  | Ibnd xl xu =>
    if Fle xu (F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 2%Z)) then
      I.bnd (I.lower (T.cos_fast prec xu)) (I.upper (T.cos_fast prec xl))
    else
      I.bnd (F.fromZ (-1)) (F.fromZ 1)
  | Inan => Inan
  end.

Lemma cos_correct :
  forall prec, I.extension Xcos (cos prec).
Proof.
intros prec xi x Hx.
unfold cos.
generalize (I.abs_correct xi x Hx) (I.abs_ge_0 xi).
destruct (I.abs xi) as [|xl xu].
easy.
intros Ha Hal.
simpl in Hal.
destruct x as [|x] ; try easy.
simpl Xcos.
replace (Rtrigo_def.cos x) with (Rtrigo_def.cos (Rabs x)).
2: unfold Rabs ; case Rcase_abs ; intros _ ; try easy ; apply cos_neg.
case_eq (Fle xu (F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 2))).
- intros Hle.
  apply Fle_correct in Hle.
  simpl in Ha.
  assert (Hcxu := T.cos_fast_correct prec xu).
  unfold I.convert_bound in Ha, Hle.
  destruct (FtoX (F.toF xu)) as [|xur] ; try easy.
  assert (Hxur: (xur <= PI)%R).
    rewrite F.scale2_correct in Hle by easy.
    rewrite Interval_generic_proof.Fscale2_correct with (1 := F.even_radix_correct) in Hle.
    generalize (T.pi4_correct prec).
    destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl in Hle.
    now rewrite F.nan_correct in Hle.
    simpl.
    unfold T.I.convert_bound.
    intros [H _].
    destruct (FtoX (F.toF pi4l)) as [|pi4r] ; try easy.
    apply Rle_trans with (1 := Hle).
    rewrite <- (Rmult_1_r PI).
    rewrite <- (Rinv_l 4) at 5.
    2: now apply (Fcore_Raux.Z2R_neq 4 0).
    rewrite <- (Rmult_assoc PI).
    apply Rmult_le_compat_r with (2 := H).
    now apply (Fcore_Raux.Z2R_le 0 4).
  split.
  + apply proj2 in Ha.
    destruct (T.cos_fast prec xu) as [|cu cu'].
    unfold I.convert_bound.
    simpl.
    now rewrite F.nan_correct.
    simpl.
    destruct Hcxu as [Hu _].
    unfold T.I.convert_bound in Hu.
    unfold I.convert_bound.
    destruct (FtoX (F.toF cu)) as [|cur] ; try easy.
    apply Rle_trans with (1 := Hu).
    apply cos_decr_1 with (4 := Hxur) (5 := Ha).
    apply Rabs_pos.
    now apply Rle_trans with xur.
    apply Rle_trans with (2 := Ha).
    apply Rabs_pos.
  + generalize (T.cos_fast_correct prec xl).
    destruct (T.cos_fast prec xl) as [|cl' cl].
    intros _.
    unfold I.convert_bound.
    simpl.
    now rewrite F.nan_correct.
    destruct (FtoX (F.toF xl)) as [|xlr] ; try easy.
    simpl.
    unfold T.I.convert_bound, I.convert_bound.
    intros [_ Hl].
    destruct (FtoX (F.toF cl)) as [|clr] ; try easy.
    apply Rle_trans with (2 := Hl).
    apply cos_decr_1 with (1 := Hal).
    apply Rle_trans with (2 := Hxur).
    now apply Rle_trans with (Rabs x).
    apply Rabs_pos.
    now apply Rle_trans with xur.
    apply Ha.
- intros _.
  unfold I.convert, I.convert_bound, I.bnd.
  rewrite 2!F.fromZ_correct.
  apply COS_bound.
Qed.

(* useful only for |xi| <= pi/2 *)
Definition sin prec xi :=
  match xi with
  | Ibnd xl xu =>
    let pi2 := F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 1%Z) in
    match Fle (F.neg pi2) xl, Fle xu pi2 with
    | true, true =>
      I.bnd (I.lower (T.sin_fast prec xl)) (I.upper (T.sin_fast prec xu))
    | _, _ => I.bnd (F.fromZ (-1)) (F.fromZ 1)
    end
  | Inan => Inan
  end.

Theorem sin_correct :
  forall prec, I.extension Xsin (sin prec).
Proof.
intros prec [|xl xu] [|x] ; try easy.
intros (Hxl, Hxu).
simpl.
set (pi2 := F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 1)).
case_eq (Fle (F.neg pi2) xl) ; intros Hpl.
generalize (Fle_correct _ _ Hpl).
I.xreal_tac xl. now case (I.convert_bound (F.neg pi2)).
clear Hpl. intros Hpl.
case_eq (Fle xu pi2) ; intros Hpu.
generalize (Fle_correct _ _ Hpu).
I.xreal_tac xu. easy.
I.xreal_tac pi2. easy.
clear Hpu. intros Hpu.
revert Hpl.
unfold I.convert_bound.
rewrite F.neg_correct, Interval_generic_proof.Fneg_correct.
fold (I.convert_bound pi2).
rewrite X1.
simpl.
intros Hpl.
generalize (F.scale2_correct (I.lower (T.pi4 prec)) 1 (refl_equal _)).
rewrite Interval_generic_proof.Fscale2_correct with (1 := F.even_radix_correct).
intros X2.
change (I.convert_bound pi2 = Xmul (I.convert_bound (I.lower (T.pi4 prec))) (Xreal 2)) in X2.
rewrite X1 in X2. clear X1.
revert X2.
generalize (T.pi4_correct prec).
case (T.pi4 prec).
simpl.
now unfold I.convert_bound ; rewrite F.nan_correct.
simpl.
intros p.
change (T.I.convert_bound p) with (I.convert_bound p).
I.xreal_tac p. easy.
intros _ (Hp,_) H.
injection H.
clear H X1. intros H.
(* *)
assert (Hpl': (-(PI/2) <= r)%R).
apply Rle_trans with (2 := Hpl).
apply Ropp_le_contravar.
rewrite H.
replace (PI / 2)%R with (PI / 4 * 2)%R by field.
apply Rmult_le_compat_r with (2 := Hp).
now apply (Fcore_Raux.Z2R_le 0 2).
assert (Hpu': (r0 <= PI/2)%R).
apply Rle_trans with (1 := Hpu).
rewrite H.
replace (PI / 2)%R with (PI / 4 * 2)%R by field.
apply Rmult_le_compat_r with (2 := Hp).
now apply (Fcore_Raux.Z2R_le 0 2).
split.
(* *)
generalize (T.sin_fast_correct prec xl).
destruct (T.sin_fast prec xl) as [|yl yu].
unfold I.convert_bound. simpl.
now rewrite F.nan_correct.
fold (I.convert_bound xl). rewrite X.
simpl.
change (T.I.convert_bound yl) with (I.convert_bound yl).
I.xreal_tac yl. easy.
change (T.I.convert_bound yu) with (I.convert_bound yu).
intros (Hy,_).
apply Rle_trans with (1 := Hy).
assert (H' := Rle_trans _ _ _ Hxu Hpu').
apply sin_incr_1 ; try easy.
now apply Rle_trans with x.
now apply Rle_trans with r.
(* *)
generalize (T.sin_fast_correct prec xu).
destruct (T.sin_fast prec xu) as [|yl yu].
unfold I.convert_bound. simpl.
now rewrite F.nan_correct.
fold (I.convert_bound xu). rewrite X0.
simpl.
change (T.I.convert_bound yu) with (I.convert_bound yu).
I.xreal_tac yu. easy.
intros (_, Hy).
apply Rle_trans with (2 := Hy).
assert (H' := Rle_trans _ _ _ Hpl' Hxl).
apply sin_incr_1 ; try easy.
now apply Rle_trans with r0.
now apply Rle_trans with x.
(* *)
simpl.
unfold I.convert_bound.
rewrite 2!F.fromZ_correct.
apply SIN_bound.
simpl.
unfold I.convert_bound.
rewrite 2!F.fromZ_correct.
apply SIN_bound.
Qed.

(* meaningful only for |xi| <= pi/2 *)
Definition tan prec xi :=
  match xi with
  | Ibnd xl xu =>
    let pi2 := F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 1%Z) in
    match Fle (F.neg pi2) xl, Fle xu pi2 with
    | true, true =>
      I.bnd (I.lower (T.tan_fast prec xl)) (I.upper (T.tan_fast prec xu))
    | _, _ => Inan
    end
  | Inan => Inan
  end.

Axiom tan_correct : forall prec, I.extension Xtan (tan prec).

Definition atan prec xi :=
  match xi with
  | Ibnd xl xu =>
    Ibnd
     (if F.real xl then I.lower (T.atan_fast prec xl)
      else F.neg (F.scale2 (I.upper (T.pi4 prec)) (F.ZtoS 1%Z)))
     (if F.real xu then I.upper (T.atan_fast prec xu)
      else F.scale2 (I.upper (T.pi4 prec)) (F.ZtoS 1%Z))
  | Inan => Inan
  end.

Axiom atan_correct : forall prec, I.extension Xatan (atan prec).

Definition exp prec xi :=
  match xi with
  | Ibnd xl xu =>
    Ibnd
     (if F.real xl then I.lower (T.exp_fast prec xl) else F.zero)
     (if F.real xu then I.upper (T.exp_fast prec xu) else F.nan)
  | Inan => Inan
  end.

Theorem exp_correct :
  forall prec, I.extension Xexp (exp prec).
Proof.
intros prec [|xl xu].
trivial.
intros [|x].
trivial.
intros (Hxl, Hxu).
split.
(* lower *)
clear Hxu.
rewrite I.real_correct.
I.xreal_tac xl.
unfold I.convert_bound.
rewrite F.zero_correct.
simpl.
apply Rlt_le.
apply exp_pos.
generalize (T.exp_fast_correct prec xl).
destruct (T.exp_fast prec xl) as [|yl yu].
unfold I.convert_bound, I.lower.
now rewrite F.nan_correct.
unfold I.convert_bound in X.
rewrite X.
intros (H, _).
simpl.
unfold T.I.convert_bound in H.
I.xreal_tac2.
apply Rle_trans with (1 := H).
now apply Fcore_Raux.exp_le.
(* upper *)
clear Hxl.
rewrite I.real_correct.
I.xreal_tac xu.
unfold I.convert_bound.
now rewrite F.nan_correct.
generalize (T.exp_fast_correct prec xu).
destruct (T.exp_fast prec xu) as [|yl yu].
unfold I.convert_bound, I.upper.
now rewrite F.nan_correct.
unfold I.convert_bound in X.
rewrite X.
intros (_, H).
simpl.
unfold T.I.convert_bound in H.
I.xreal_tac2.
apply Rle_trans with (2 := H).
now apply Fcore_Raux.exp_le.
Qed.

Definition bound_type := I.bound_type.
Definition convert_bound := I.convert_bound.
Definition type := I.type.
Definition convert := I.convert.
Definition nai := I.nai.
Definition bnd := I.bnd.
Definition bnd_correct := I.bnd_correct.
Definition nai_correct := I.nai_correct.
Definition subset := I.subset.
Definition subset_correct := I.subset_correct.
Definition overlap := I.overlap.
Definition join := I.join.
Definition join_correct := I.join_correct.
Definition meet := I.meet.
Definition mask := I.mask.
Definition meet_correct := I.meet_correct.
Definition mask_correct := I.mask_correct.
Definition sign_large := I.sign_large.
Definition sign_large_correct := I.sign_large_correct.
Definition sign_strict := I.sign_strict.
Definition sign_strict_correct := I.sign_strict_correct.
Definition midpoint := I.midpoint.
Definition midpoint_correct := I.midpoint_correct.
Definition precision := I.precision.
Definition neg := I.neg.
Definition abs := I.abs.
Definition inv := I.inv.
Definition sqr := I.sqr.
Definition sqrt := I.sqrt.
Definition add := I.add.
Definition sub := I.sub.
Definition mul := I.mul.
Definition div := I.div.
Definition power_int := I.power_int.
Definition neg_correct := I.neg_correct.
Definition abs_correct := I.abs_correct.
Definition inv_correct := I.inv_correct.
Definition sqr_correct := I.sqr_correct.
Definition sqrt_correct := I.sqrt_correct.
Definition add_correct := I.add_correct.
Definition sub_correct := I.sub_correct.
Definition mul_correct := I.mul_correct.
Definition div_correct := I.div_correct.
Definition power_int_correct := I.power_int_correct.
Definition bounded := I.bounded.
Definition lower_bounded := I.lower_bounded.
Definition upper_bounded := I.upper_bounded.
Definition lower_bounded_correct := I.lower_bounded_correct.
Definition upper_bounded_correct := I.upper_bounded_correct.
Definition bounded_correct := I.bounded_correct.
Definition lower_extent := I.lower_extent.
Definition upper_extent := I.upper_extent.
Definition whole := I.whole.
Definition lower_extent_correct := I.lower_extent_correct.
Definition upper_extent_correct := I.upper_extent_correct.
Definition whole_correct := I.whole_correct.
Definition lower := I.lower.
Definition upper := I.upper.
Definition lower_correct := I.lower_correct.
Definition upper_correct := I.upper_correct.
Definition fromZ := I.fromZ.
Definition fromZ_correct := I.fromZ_correct.
Definition extension := I.extension.
Definition extension_2 := I.extension_2.
Definition bounded_prop := I.bounded_prop.

End FloatIntervalFull.
