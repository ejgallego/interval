(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2015, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

Require Import Reals.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_float_sig.
Require Import Interval_float_ext.
Require Import Interval_generic.
Require Import Interval_interval.
Require Import Interval_interval_float.
Require Import Interval_transcend.

Module FloatIntervalFull (F : FloatOps with Definition even_radix := true) <: IntervalOps.

Module F' := FloatExt F.
Module T := TranscendentalFloatFast F.
Module I := FloatInterval F.

Definition pi prec :=
  I.scale2 (T.pi4 prec) (F.ZtoS 2).

Lemma pi_correct :
  forall prec, contains (I.convert (pi prec)) (Xreal PI).
Proof.
intros prec.
unfold pi.
replace (Xreal PI) with (Xmul (Xreal (PI/4)) (Xreal (Fcore_Raux.bpow radix2 2))).
  apply I.scale2_correct, T.pi4_correct.
simpl.
f_equal.
now field.
Qed.

(* useful only for |xi| <= 2 * pi *)
Definition cos prec xi :=
  match I.abs xi with
  | Ibnd xl xu =>
    if F'.le xu xl then T.cos_fast prec xl else
    let pi4 := T.pi4 prec in
    if F'.le xu (F.scale2 (I.lower pi4) (F.ZtoS 2%Z)) then
      I.bnd (I.lower (T.cos_fast prec xu)) (I.upper (T.cos_fast prec xl))
    else
      if F'.le xu (F.scale2 (I.lower pi4) (F.ZtoS 3%Z)) then
        if F'.le (F.scale2 (I.upper pi4) (F.ZtoS 2%Z)) xl then
          I.bnd (I.lower (T.cos_fast prec xl)) (I.upper (T.cos_fast prec xu))
        else
          I.bnd (F.fromZ (-1)) (F.max (I.upper (T.cos_fast prec xl)) (I.upper (T.cos_fast prec xu)))
      else
        I.bnd (F.fromZ (-1)) (F.fromZ 1)
  | Inan => Inan
  end.

Lemma cos_correct :
  forall prec, I.extension Xcos (cos prec).
Proof.
intros prec xi x Hx.
unfold cos.
generalize (I.abs_correct xi x Hx) (I.abs_ge_0' xi).
destruct (I.abs xi) as [|xl xu].
easy.
intros Ha Hal.
simpl in Hal.
destruct x as [|x] ; try easy.
simpl Xcos.
replace (Rtrigo_def.cos x) with (Rtrigo_def.cos (Rabs x)).
2: unfold Rabs ; case Rcase_abs ; intros _ ; try easy ; apply cos_neg.
clear Hx.
assert (Hcxl := T.cos_fast_correct prec xl).
assert (Hcxu := T.cos_fast_correct prec xu).
case_eq (F'.le xu xl).
  intros Hl.
  apply F'.le_correct in Hl.
  simpl in Ha.
  destruct (F.toX xu) as [|xur] ; try easy.
  destruct (F.toX xl) as [|xlr] ; try easy.
  replace (Rabs x) with xlr.
  exact Hcxl.
  apply Rle_antisym.
  apply Ha.
  now apply Rle_trans with (2 := Hl).
intros _.
case_eq (F'.le xu (F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 2))).
  intros Hu.
  apply F'.le_correct in Hu.
  simpl in Ha.
  destruct (F.toX xu) as [|xur] ; try easy.
  assert (Hxur: (xur <= PI)%R).
    revert Hu.
    rewrite <- F.toF_correct, F.scale2_correct by easy.
    rewrite Interval_generic_proof.Fscale2_correct with (1 := F.even_radix_correct).
    rewrite F.toF_correct.
    generalize (T.pi4_correct prec).
    destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl.
    now rewrite F.nan_correct.
    intros [H _] Hu.
    destruct (F.toX pi4l) as [|pi4r] ; try easy.
    apply Rle_trans with (1 := Hu).
    rewrite <- (Rmult_1_r PI).
    rewrite <- (Rinv_l 4) at 5.
    2: now apply (Fcore_Raux.Z2R_neq 4 0).
    rewrite <- (Rmult_assoc PI).
    apply Rmult_le_compat_r with (2 := H).
    now apply (Fcore_Raux.Z2R_le 0 4).
  clear Hu.
  split.
    apply proj2 in Ha.
    destruct (T.cos_fast prec xu) as [|cu cu'] ; simpl.
      now rewrite F.nan_correct.
    destruct Hcxu as [Hcu _].
    destruct (F.toX cu) as [|cur] ; try easy.
    apply Rle_trans with (1 := Hcu).
    apply cos_decr_1 with (4 := Hxur) (5 := Ha).
    apply Rabs_pos.
    now apply Rle_trans with xur.
    apply Rle_trans with (2 := Ha).
    apply Rabs_pos.
  generalize (T.cos_fast_correct prec xl).
  destruct (T.cos_fast prec xl) as [|cl' cl] ; simpl.
    intros _.
    now rewrite F.nan_correct.
  destruct (F.toX xl) as [|xlr] ; try easy.
  intros [_ Hl].
  destruct (F.toX cl) as [|clr] ; try easy.
  apply Rle_trans with (2 := Hl).
  apply cos_decr_1 with (1 := Hal).
  apply Rle_trans with (2 := Hxur).
  now apply Rle_trans with (Rabs x).
  apply Rabs_pos.
  now apply Rle_trans with xur.
  apply Ha.
intros _.
case_eq (F'.le xu (F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 3))).
  intros Hu.
  apply F'.le_correct in Hu.
  simpl in Ha.
  destruct (F.toX xu) as [|xur] ; try easy.
  assert (Hxur: (xur <= 2 * PI)%R).
    revert Hu.
    rewrite <- F.toF_correct, F.scale2_correct by easy.
    rewrite Interval_generic_proof.Fscale2_correct with (1 := F.even_radix_correct).
    generalize (T.pi4_correct prec).
    rewrite F.toF_correct.
    destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl.
    now rewrite F.nan_correct.
    intros [H _] Hu.
    destruct (F.toX pi4l) as [|pi4r] ; try easy.
    apply Rle_trans with (1 := Hu).
    rewrite <- (Rmult_1_r PI).
    rewrite <- (Rinv_l 4) at 9.
    2: now apply (Fcore_Raux.Z2R_neq 4 0).
    rewrite <- (Rmult_assoc PI).
    replace (2 * (PI * / 4 * 4))%R with (PI * / 4 * 8)%R by ring.
    apply Rmult_le_compat_r with (2 := H).
    now apply (Fcore_Raux.Z2R_le 0 8).
  clear Hu.
  case_eq (F'.le (F.scale2 (I.upper (T.pi4 prec)) (F.ZtoS 2)) xl).
    intros Hl.
    apply F'.le_correct in Hl.
    destruct (F.toX xl) as [|xlr].
    now destruct (F.toX (F.scale2 (I.upper (T.pi4 prec)) (F.ZtoS 2))).
    assert (Hxlr: (PI <= xlr)%R).
      revert Hl.
      rewrite <- F.toF_correct, F.scale2_correct by easy.
      rewrite Interval_generic_proof.Fscale2_correct with (1 := F.even_radix_correct).
      rewrite F.toF_correct.
      generalize (T.pi4_correct prec).
      destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl.
      now rewrite F.nan_correct.
      intros [_ H] Hl.
      destruct(F.toX pi4u) as [|pi4r] ; try easy.
      apply Rle_trans with (2 := Hl).
      rewrite <- (Rmult_1_r PI).
      rewrite <- (Rinv_l 4) at 1.
      2: now apply (Fcore_Raux.Z2R_neq 4 0).
      rewrite <- (Rmult_assoc PI).
      apply Rmult_le_compat_r with (2 := H).
      now apply (Fcore_Raux.Z2R_le 0 4).
    clear Hl.
    split.
      destruct (T.cos_fast prec xl) as [|cl cl'] ; simpl.
        now rewrite F.nan_correct.
      destruct Hcxl as [Hcl _].
      destruct (F.toX cl) as [|clr] ; try easy.
      apply Rle_trans with (1 := Hcl).
      apply cos_incr_1 with (1 := Hxlr) (5 := proj1 Ha).
      apply Rle_trans with (2 := Hxur).
      apply Rle_trans with (1 := proj1 Ha) (2 := proj2 Ha).
      apply Rle_trans with (1 := Hxlr) (2 := proj1 Ha).
      apply Rle_trans with (1 := proj2 Ha) (2 := Hxur).
    destruct (T.cos_fast prec xu) as [|cu' cu] ; simpl.
      now rewrite F.nan_correct.
    destruct Hcxu as [_ Hcu].
    destruct (F.toX cu) as [|cur] ; try easy.
    apply Rle_trans with (2 := Hcu).
    apply cos_incr_1 with (4 := Hxur) (5 := proj2 Ha).
    apply Rle_trans with (1 := Hxlr) (2 := proj1 Ha).
    apply Rle_trans with (1 := proj2 Ha) (2 := Hxur).
    apply Rle_trans with (1 := Hxlr).
    apply Rle_trans with (1 := proj1 Ha) (2 := proj2 Ha).
  intros _.
  split.
    rewrite F.fromZ_correct.
    apply COS_bound.
  rewrite <- F.toF_correct, F.max_correct, Interval_generic_proof.Fmax_correct, 2!F.toF_correct.
  destruct (T.cos_fast prec xl) as [|cl' cl] ; simpl.
    now rewrite F.nan_correct.
  destruct (F.toX xl) as [|xlr] ; try easy.
  destruct Hcxl as [_ Hcl].
  destruct (F.toX cl) as [|clr] ; try easy.
  destruct (T.cos_fast prec xu) as [|cu' cu] ; simpl.
    now rewrite F.nan_correct.
  destruct Hcxu as [_ Hcu].
  destruct (F.toX cu) as [|cur] ; try easy.
  destruct (Rle_dec (Rabs x) PI) as [Hx|Hx].
    apply Rle_trans with (2 := Rmax_l _ _).
    apply Rle_trans with (2 := Hcl).
    apply cos_decr_1 with (1 := Hal) (3 := Rabs_pos _) (4 := Hx) (5 := proj1 Ha).
    apply Rle_trans with (1 := proj1 Ha) (2 := Hx).
  apply Rle_trans with (2 := Rmax_r _ _).
  apply Rle_trans with (2 := Hcu).
  apply Rnot_le_lt, Rlt_le in Hx.
  apply cos_incr_1 with (1 := Hx) (4 := Hxur) (5 := proj2 Ha).
  apply Rle_trans with (1 := proj2 Ha) (2 := Hxur).
  apply Rle_trans with (1 := Hx) (2 := proj2 Ha).
intros _.
unfold I.convert, I.bnd.
rewrite 2!F.fromZ_correct.
apply COS_bound.
Qed.

(* useful only for |xi| <= 5/2*pi *)
Definition sin prec xi :=
  match xi with
  | Ibnd xl xu =>
    if F'.le xu xl then T.sin_fast prec xl else
    let pi4 := T.pi4 prec in
    let s1 := F.ZtoS 1%Z in
    let pi2 := F.scale2 (I.lower pi4) s1 in
    match F'.le (F.neg pi2) xl, F'.le xu pi2 with
    | true, true =>
      I.bnd (I.lower (T.sin_fast prec xl)) (I.upper (T.sin_fast prec xu))
    | true, false =>
      cos prec (I.sub prec (I.scale2 pi4 s1) xi)
    | _, _ =>
      I.neg (cos prec (I.add prec xi (I.scale2 pi4 s1)))
    end
  | Inan => Inan
  end.

Theorem sin_correct :
  forall prec, I.extension Xsin (sin prec).
Proof.
intros prec [|xl xu] [|x] Hx ; try easy.
generalize Hx.
intros [Hxl Hxu].
simpl.
case_eq (F'.le xu xl).
  intros Hl.
  apply F'.le_correct in Hl.
  assert (Hsxl := T.sin_fast_correct prec xl).
  destruct (F.toX xu) as [|xur] ; try easy.
  destruct (F.toX xl) as [|xlr] ; try easy.
  replace x with xlr.
  exact Hsxl.
  apply Rle_antisym with (1 := Hxl).
  now apply Rle_trans with (2 := Hl).
intros _.
set (pi2 := F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 1)).
case_eq (F'.le (F.neg pi2) xl).
  intros Hpl.
  generalize (F'.le_correct _ _ Hpl).
  I.xreal_tac xl.
    now case (F.toX (F.neg pi2)).
  clear Hpl. intros Hpl.
  case_eq (F'.le xu pi2).
    intros Hpu.
    generalize (F'.le_correct _ _ Hpu).
    I.xreal_tac xu. easy.
    I.xreal_tac pi2. easy.
    clear Hpu. intros Hpu.
    revert Hpl.
    rewrite <- F.toF_correct, F.neg_correct, Interval_generic_proof.Fneg_correct, F.toF_correct.
    rewrite X1.
    simpl.
    intros Hpl.
    generalize (F.scale2_correct (I.lower (T.pi4 prec)) 1 (refl_equal _)).
    rewrite Interval_generic_proof.Fscale2_correct with (1 := F.even_radix_correct).
    rewrite 2!F.toF_correct.
    intros X2.
    change (F.toX pi2 = Xmul (F.toX (I.lower (T.pi4 prec))) (Xreal 2)) in X2.
    rewrite X1 in X2. clear X1.
    revert X2.
    generalize (T.pi4_correct prec).
    case (T.pi4 prec) ; simpl.
      now rewrite F.nan_correct.
    intros p.
    I.xreal_tac p. easy.
    intros _ [Hp _] H.
    injection H.
    clear H X1. intros H.
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
      generalize (T.sin_fast_correct prec xl).
      destruct (T.sin_fast prec xl) as [|yl yu].
        simpl.
        now rewrite F.nan_correct.
      rewrite X.
      simpl.
      I.xreal_tac yl. easy.
      intros [Hy _].
      apply Rle_trans with (1 := Hy).
      assert (H' := Rle_trans _ _ _ Hxu Hpu').
      apply sin_incr_1 ; try easy.
      now apply Rle_trans with x.
      now apply Rle_trans with r.
    generalize (T.sin_fast_correct prec xu).
    destruct (T.sin_fast prec xu) as [|yl yu].
      simpl.
      now rewrite F.nan_correct.
    rewrite X0.
    simpl.
    I.xreal_tac yu. easy.
    intros [_ Hy].
    apply Rle_trans with (2 := Hy).
    assert (H' := Rle_trans _ _ _ Hpl' Hxl).
    apply sin_incr_1 ; try easy.
    now apply Rle_trans with r0.
    now apply Rle_trans with x.
  intros _.
  rewrite <- cos_shift.
  change (Xreal (Rtrigo_def.cos (PI / 2 - x))) with (Xcos (Xsub (Xreal (PI / 2)) (Xreal x))).
  apply cos_correct.
  apply I.sub_correct with (2 := Hx).
  replace (PI / 2)%R with (PI / 4 * 2)%R by field.
  apply (I.scale2_correct _ (Xreal (PI / 4)) 1%Z).
  apply T.pi4_correct.
intros _.
rewrite <- (Ropp_involutive x).
rewrite sin_neg.
apply (I.neg_correct _ (Xreal _)).
rewrite <- cos_shift.
replace (PI / 2 - - x)%R with (x + PI / 2)%R by ring.
change (Xreal (Rtrigo_def.cos (x + PI / 2))) with (Xcos (Xadd (Xreal x) (Xreal (PI / 2)))).
apply cos_correct.
apply (I.add_correct _ _ _ _ _ Hx).
replace (PI / 2)%R with (PI / 4 * 2)%R by field.
apply (I.scale2_correct _ (Xreal (PI / 4)) 1%Z).
apply T.pi4_correct.
Qed.

(* meaningful only for |xi| <= pi/2 *)
Definition tan prec xi :=
  match xi with
  | Ibnd xl xu =>
    if F'.le xu xl then T.tan_fast prec xl else
    let pi2 := F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 1%Z) in
    match F'.lt (F.neg pi2) xl, F'.lt xu pi2 with
    | true, true =>
      I.bnd (I.lower (T.tan_fast prec xl)) (I.upper (T.tan_fast prec xu))
    | _, _ => Inan
    end
  | Inan => Inan
  end.

Lemma tan_correct :
  forall prec, I.extension Xtan (tan prec).
Proof.
intros prec [|xl xu] [|x] Hx ; try easy.
unfold tan.
case_eq (F'.le xu xl).
  intros Hl.
  apply F'.le_correct in Hl.
  assert (Htxl := T.tan_fast_correct prec xl).
  unfold I.convert in Hx, Hl.
  destruct (F.toX xu) as [|xur] ; try easy.
  destruct (F.toX xl) as [|xlr] ; try easy.
  replace x with xlr.
  exact Htxl.
  apply Rle_antisym with (1 := proj1 Hx).
  apply Rle_trans with (2 := Hl).
  apply Hx.
intros _.
case_eq (F'.lt (F.neg (F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 1))) xl) ; try easy.
intros Hlt1.
apply F'.lt_correct in Hlt1.
case_eq (F'.lt xu (F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 1))) ; try easy.
intros Hlt2.
apply F'.lt_correct in Hlt2.
generalize (T.tan_correct prec xl) (T.tan_correct prec xu).
simpl in Hx.
destruct (F.toX xl) as [|rl].
now destruct (F.toX (F.neg (F.scale2 (I.lower (T.pi4 prec)) (F.ZtoS 1)))).
destruct (F.toX xu) as [|ru] ; try easy.
intros Hl Hu.
rewrite I.bnd_correct.
rewrite <- F.toF_correct, F.neg_correct, Interval_generic_proof.Fneg_correct, F.toF_correct in Hlt1.
rewrite <- F.toF_correct, F.scale2_correct, Interval_generic_proof.Fscale2_correct, F.toF_correct in Hlt1, Hlt2 ;
  try easy ; try apply F.even_radix_correct.
generalize (T.pi4_correct prec).
destruct (T.pi4 prec) as [|pi4l pi4u].
simpl in Hlt1.
now rewrite F.nan_correct in Hlt1.
intros [Hpil _].
simpl in Hlt1, Hlt2.
destruct (F.toX pi4l) as [|pi4r] ; try easy.
simpl in Hlt1, Hlt2.
apply (Rmult_le_compat_r 2) in Hpil.
2: now apply (Fcore_Raux.Z2R_le 0 2).
unfold Rdiv in Hpil.
replace (PI * /4 * 2)%R with (PI / 2)%R in Hpil by field.
assert (H1: (- PI / 2 < rl)%R).
  apply Rle_lt_trans with (2 := Hlt1).
  unfold Rdiv.
  rewrite Ropp_mult_distr_l_reverse.
  now apply Ropp_le_contravar.
assert (H2: (ru < PI / 2)%R).
  now apply Rlt_le_trans with (pi4r * 2)%R.
unfold Xtan.
simpl.
case is_zero_spec.
simpl in Hx.
apply Rgt_not_eq, cos_gt_0.
apply Rlt_le_trans with (2 := proj1 Hx).
unfold Rdiv.
now rewrite <- Ropp_mult_distr_l_reverse.
now apply Rle_lt_trans with ru.
unfold Xtan in Hl, Hu.
intros _.
split.
- destruct (T.tan_fast prec xl) as [|tl tu].
  simpl.
  now rewrite F.nan_correct.
  revert Hl.
  simpl.
  case is_zero_spec ; try easy.
  intros _ [H _].
  destruct (F.toX tl) as [|rtl] ; try easy.
  apply Rle_trans with (1 := H).
  destruct (proj1 Hx) as [Hx'|Hx'].
  apply Rlt_le.
  apply tan_increasing ; try easy.
  now apply Rle_lt_trans with ru.
  rewrite Hx'.
  apply Rle_refl.
- destruct (T.tan_fast prec xu) as [|tl tu].
  simpl.
  now rewrite F.nan_correct.
  revert Hu.
  simpl.
  case is_zero_spec ; try easy.
  intros _ [_ H].
  destruct (F.toX tu) as [|rtu] ; try easy.
  apply Rle_trans with (2 := H).
  destruct (proj2 Hx) as [Hx'|Hx'].
  apply Rlt_le.
  apply tan_increasing ; try easy.
  now apply Rlt_le_trans with rl.
  rewrite Hx'.
  apply Rle_refl.
Qed.

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

Lemma atan_correct :
  forall prec, I.extension Xatan (atan prec).
Proof.
intros prec [|xl xu] [|x] Hx ; try easy.
assert (Hpi := T.pi4_correct prec).
simpl.
rewrite 2!I.real_correct.
simpl in Hx.
split.
- generalize (proj1 Hx). clear Hx.
  case_eq (F.toX xl).
  intros _ _.
  rewrite <- F.toF_correct, F.neg_correct, Interval_generic_proof.Fneg_correct.
  rewrite F.scale2_correct, Interval_generic_proof.Fscale2_correct, F.toF_correct ; try easy.
  2: apply F.even_radix_correct.
  destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl.
  now rewrite F.nan_correct.
  simpl in Hpi.
  destruct (F.toX pi4u) as [|rpi4] ; try easy.
  apply Rlt_le.
  apply Rle_lt_trans with (2 := proj1 (atan_bound x)).
  replace (- PI / 2)%R with (-(PI / 4 * 2))%R by field.
  apply Ropp_le_contravar.
  apply Rmult_le_compat_r with (2 := proj2 Hpi).
  now apply (Fcore_Raux.Z2R_le 0 2).
  intros rl Hl Hx.
  generalize (T.atan_correct prec xl).
  destruct (T.atan_fast prec xl) as [|al au].
  intros _.
  simpl.
  now rewrite F.nan_correct.
  simpl.
  rewrite Hl.
  destruct (F.toX al) as [|ral] ; try easy.
  intros [H _].
  apply Rle_trans with (1 := H).
  destruct Hx as [Hx|Hx].
  now apply Rlt_le, atan_increasing.
  rewrite Hx.
  apply Rle_refl.
- generalize (proj2 Hx). clear Hx.
  case_eq (F.toX xu).
  intros _ _.
  rewrite <- F.toF_correct, F.scale2_correct, Interval_generic_proof.Fscale2_correct, F.toF_correct ; try easy.
  2: apply F.even_radix_correct.
  destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl.
  now rewrite F.nan_correct.
  simpl in Hpi.
  destruct (F.toX pi4u) as [|rpi4] ; try easy.
  apply Rlt_le.
  apply Rlt_le_trans with (1 := proj2 (atan_bound x)).
  replace (PI / 2)%R with (PI / 4 * 2)%R by field.
  apply Rmult_le_compat_r with (2 := proj2 Hpi).
  now apply (Fcore_Raux.Z2R_le 0 2).
  intros rl Hl Hx.
  generalize (T.atan_correct prec xu).
  destruct (T.atan_fast prec xu) as [|al au].
  intros _.
  simpl.
  now rewrite F.nan_correct.
  simpl.
  rewrite Hl.
  destruct (F.toX au) as [|rau] ; try easy.
  intros [_ H].
  apply Rle_trans with (2 := H).
  destruct Hx as [Hx|Hx].
  now apply Rlt_le, atan_increasing.
  rewrite Hx.
  apply Rle_refl.
Qed.

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
rewrite F.zero_correct.
simpl.
apply Rlt_le.
apply exp_pos.
generalize (T.exp_fast_correct prec xl).
destruct (T.exp_fast prec xl) as [|yl yu].
unfold I.lower.
now rewrite F.nan_correct.
rewrite X.
intros (H, _).
simpl.
I.xreal_tac2.
apply Rle_trans with (1 := H).
now apply Fcore_Raux.exp_le.
(* upper *)
clear Hxl.
rewrite I.real_correct.
I.xreal_tac xu.
now rewrite F.nan_correct.
generalize (T.exp_fast_correct prec xu).
destruct (T.exp_fast prec xu) as [|yl yu].
unfold I.upper.
now rewrite F.nan_correct.
rewrite X.
intros (_, H).
simpl.
I.xreal_tac2.
apply Rle_trans with (2 := H).
now apply Fcore_Raux.exp_le.
Qed.

Definition ln prec xi :=
  match xi with
  | Ibnd xl xu =>
    if F'.lt F.zero xl then
      Ibnd
        (I.lower (T.ln_fast prec xl))
        (if F.real xu then I.upper (T.ln_fast prec xu) else F.nan)
    else Inan
  | Inan => Inan
  end.

Theorem ln_correct :
  forall prec, I.extension Xln (ln prec).
Proof.
intros prec [|xl xu].
easy.
intros [|x].
easy.
simpl.
intros [Hl Hu].
unfold ln.
case_eq (F'.lt F.zero xl) ; intros Hlt ; try easy.
apply F'.lt_correct in Hlt.
rewrite F.zero_correct in Hlt.
simpl in Hlt.
case is_positive_spec.
intros Hx.
split.
generalize (T.ln_fast_correct prec xl).
case T.ln_fast.
intros _.
simpl.
now rewrite F.nan_correct.
intros l u.
simpl.
case_eq (Xln (F.toX xl)).
easy.
intros lnx Hlnx.
intros [H _].
destruct (F.toX l) as [|lr].
easy.
apply Rle_trans with (1 := H).
destruct (F.toX xl) as [|xlr].
easy.
revert Hlnx.
simpl.
case is_positive_spec.
intros _ H'.
injection H'.
intros <-.
destruct Hl as [Hl|Hl].
now apply Rlt_le, ln_increasing.
rewrite Hl.
apply Rle_refl.
easy.
rewrite I.real_correct.
case_eq (F.toX xu).
now rewrite F.nan_correct.
intros xur Hxu.
rewrite Hxu in Hu.
generalize (T.ln_fast_correct prec xu).
case T.ln_fast.
intros _.
simpl.
now rewrite F.nan_correct.
intros l u.
simpl.
rewrite Hxu.
simpl.
case is_positive_spec.
intros _.
intros [_ H].
destruct (F.toX u) as [|ur].
easy.
apply Rle_trans with (2 := H).
destruct Hu as [Hu|Hu].
now apply Rlt_le, ln_increasing.
rewrite Hu.
apply Rle_refl.
easy.
intros Hx.
destruct (F.toX xl) as [|xlr].
easy.
elim Rle_not_lt with (1 := Hx).
now apply Rlt_le_trans with xlr.
Qed.

Lemma cos_propagate : forall prec, I.propagate (cos prec).
Proof. intros prec xi; destruct xi; easy. Qed.

Lemma sin_propagate : forall prec, I.propagate (sin prec).
Proof. intros prec xi; destruct xi; easy. Qed.

Lemma tan_propagate : forall prec, I.propagate (tan prec).
Proof. intros prec xi; destruct xi; easy. Qed.

Lemma atan_propagate : forall prec, I.propagate (atan prec).
Proof. intros prec xi; destruct xi; easy. Qed.

Lemma exp_propagate : forall prec, I.propagate (exp prec).
Proof. intros prec xi; destruct xi; easy. Qed.

Lemma ln_propagate : forall prec, I.propagate (ln prec).
Proof. intros prec xi; destruct xi; easy. Qed.

Include I.

End FloatIntervalFull.
