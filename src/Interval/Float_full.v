(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

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

From Coq Require Import Reals Psatz.

Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.
Require Import Float.
Require Import Transcend.

Module FloatIntervalFull (F : FloatOps with Definition sensible_format := true) <: IntervalOps.

Module T := TranscendentalFloatFast F.
Include FloatInterval F.

Definition c3 := F.fromZ 3.
Definition c4 := F.fromZ 4.
Definition c8 := F.fromZ 8.

Definition pi prec :=
  mul2 prec (mul2 prec (T.pi4 prec)).

Lemma pi_correct :
  forall prec, contains (convert (pi prec)) (Xreal PI).
Proof.
intros prec.
unfold pi.
replace (Xreal PI) with (Xmul (Xreal (PI/4)) (Xreal (Raux.bpow radix2 2))).
change (Xreal (Raux.bpow _ _)) with (Xreal 2 * Xreal 2)%XR.
rewrite <-Xmul_assoc.
do 2 apply mul2_correct.
apply T.pi4_correct.
change (Raux.bpow _ _) with 4%R.
simpl.
apply f_equal.
field.
Qed.

(* accurate only for |xi| <= 2 * pi *)
Definition cos prec xi :=
  match abs xi with
  | Ibnd xl xu =>
    if F'.le' xu xl then T.cos_fast prec xl else
    let pi4 := T.pi4 prec in
    if F'.le' xu (F.mul_DN prec (lower pi4) c4) then
      bnd (lower (T.cos_fast prec xu)) (upper (T.cos_fast prec xl))
    else
      if F'.le' xu (F.mul_DN prec (lower pi4) c8) then
        if F'.le' (F.mul_UP prec (upper pi4) c4) xl then
          bnd (lower (T.cos_fast prec xl)) (upper (T.cos_fast prec xu))
        else
          bnd cm1 (F.max (upper (T.cos_fast prec xl)) (upper (T.cos_fast prec xu)))
      else
        let d := F.sub_UP prec xu xl in
        if F'.le' d c3 then
          let m := F.midpoint xl xu in
          let d := F.max (F.sub_UP prec xu m) (F.sub_UP prec m xl) in
          let c := T.cos_fast prec m in
          meet (bnd cm1 c1) (add prec c (bnd (F.neg d) d))
        else bnd cm1 c1
  | Inan => Inan
  end.

Lemma cos_correct :
  forall prec, extension Xcos (cos prec).
Proof.
intros prec xi x Hx.
unfold cos.
generalize (abs_correct xi x Hx) (abs_ge_0' xi).
destruct (abs xi) as [|xl xu]; [easy|].
destruct x as [|x].
{ now simpl; case (_ && _)%bool. }
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; lra].
intros Vxu Vxl [Hxl Hxu].
intros Hal.
simpl in Hal.
assert (H : not_empty (convert xi)).
{ now exists x. }
specialize (Hal H); clear H.
unfold Xbind.
replace (Rtrigo_def.cos x) with (Rtrigo_def.cos (Rabs x)).
2: now unfold Rabs ; case Rcase_abs ; intros _ ; try easy ; apply cos_neg.
clear Hx.
assert (Hcxl := T.cos_fast_correct prec xl).
assert (Hcxu := T.cos_fast_correct prec xu).
case_eq (F'.le' xu xl).
{ intros Hl.
  apply F'.le'_correct in Hl.
  destruct (F.toX xu) as [|xur] ; [easy|].
  destruct (F.toX xl) as [|xlr] ; [easy|].
  replace (Rabs x) with xlr.
  { exact Hcxl. }
  apply Rle_antisym.
  { easy. }
  now apply Rle_trans with (2 := Hl). }
intros _.
unfold cm1, c1, c3, c4, c8.
assert (Hlb'_cos : F.valid_lb (lower (T.cos_fast prec xl)) = true).
{ generalize Hcxl.
  unfold T.I.convert.
  case (T.cos_fast prec xl).
  { now simpl; rewrite F'.valid_lb_nan. }
  simpl.
  intros l u.
  case (F.valid_lb l); [easy|].
  now simpl; case F.toX; [|intros r [H0 H1]; lra]. }
assert (Hub'_cos : F.valid_ub (upper (T.cos_fast prec xu)) = true).
{ generalize Hcxu.
  unfold T.I.convert.
  case (T.cos_fast prec xu).
  { now simpl; rewrite F'.valid_ub_nan. }
  simpl.
  intros l u.
  rewrite Bool.andb_comm.
  case (F.valid_ub u); [easy|].
  now simpl; case F.toX; [|intros r [H0 H1]; lra]. }
assert (Hub_cos : F.valid_ub (upper (T.cos_fast prec xl)) = true).
{ generalize Hcxl.
  unfold T.I.convert.
  case (T.cos_fast prec xl).
  { now simpl; rewrite F'.valid_ub_nan. }
  simpl.
  intros l u; rewrite Bool.andb_comm.
  case (F.valid_ub u); [easy|].
  now simpl; case F.toX; [|intros r [H0 H1]; lra]. }
assert (Hlb_cos : F.valid_lb (lower (T.cos_fast prec xu)) = true).
{ generalize Hcxu.
  unfold T.I.convert.
  case (T.cos_fast prec xu).
  { now simpl; rewrite F'.valid_lb_nan. }
  simpl.
  intros l u.
  now case (F.valid_lb l); [|simpl; case Xcos; [|intros r [H0 H1]; lra]]. }
case_eq (F'.le' xu (F.mul_DN prec (lower (T.pi4 prec)) (F.fromZ 4))).
{ intros Hu.
  apply F'.le'_correct in Hu.
  destruct (F.toX xu) as [|xur] ; try easy.
  assert (Hxur: (xur <= PI)%R).
  { revert Hu.
    elim (F.mul_DN_correct prec (lower (T.pi4 prec)) (F.fromZ 4)).
    2:{
      rewrite F.fromZ_correct by easy.
      rewrite (F'.valid_ub_real (F.fromZ 4)) by now rewrite F.real_correct, F.fromZ_correct.
      generalize (T.pi4_correct prec).
      unfold T.I.convert.
      case T.pi4.
      { simpl; intros _; do 3 right; rewrite F'.valid_lb_nan, F'.nan_correct.
        repeat split; lra. }
      intros l u; simpl.
      rewrite F.valid_lb_correct.
      case F.classify; [..|intros [H0 H1]; lra]; intros _;
      (case F.toX; [now do 3 right; repeat split; lra|]; intro rl);
      (case (Rle_or_lt 0 rl); intro Hrl;
        [now left; repeat split; lra|do 3 right; repeat split; lra]). }
    intros Vmdn.
    unfold le_lower, le_upper.
    case F.toX; [easy|]; intro Rmdn; simpl.
    rewrite F.fromZ_correct by easy.
    generalize (T.pi4_correct prec).
    destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl.
    { now rewrite F'.nan_correct. }
    case (_ && _)%bool; [|intros [H0 H1]; lra].
    case F.toX; [easy|]; intro pi4r.
    simpl.
    intros [H _] Hu.
    apply Ropp_le_cancel in Hu.
    intro H'; apply (Rle_trans _ _ _ H'); clear H'.
    apply Rle_trans with (1 := Hu).
    lra. }
  clear Hu.
  unfold convert; simpl.
  rewrite Hlb_cos; simpl.
  rewrite Hub_cos; simpl.
  split.
  { destruct (T.cos_fast prec xu) as [|cu cu'] ; simpl.
    { now rewrite F'.nan_correct. }
    generalize Hcxu; unfold T.I.convert;
      case (_ && _)%bool; [|intros [H0 H1]; lra].
    intros [Hcu _].
    destruct (F.toX cu) as [|cur] ; [easy|].
    apply Rle_trans with (1 := Hcu).
    apply cos_decr_1 with (4 := Hxur).
    { apply Rabs_pos. }
    { now apply Rle_trans with xur. }
    { revert Hxu; apply Rle_trans, Rabs_pos. }
    exact Hxu. }
  generalize (T.cos_fast_correct prec xl).
  unfold T.I.convert.
  case_eq (T.cos_fast prec xl); [now simpl; rewrite F'.nan_correct|].
  intros cl' cl Hcl.
  generalize Hub_cos; rewrite Hcl; simpl=> ->.
  generalize Hlb'_cos; rewrite Hcl; simpl=> ->; simpl.
  destruct (F.toX xl) as [|xlr] ; [easy|].
  intros [_ Hl].
  destruct (F.toX cl) as [|clr] ; [easy|].
  apply Rle_trans with (2 := Hl).
  apply cos_decr_1 with (1 := Hal).
  { apply Rle_trans with (2 := Hxur).
    now apply Rle_trans with (Rabs x). }
  { apply Rabs_pos. }
  { now apply Rle_trans with xur. }
  apply Hxl. }
intros _.
case_eq (F'.le' xu (F.mul_DN prec (lower (T.pi4 prec)) (F.fromZ 8))).
{ intros Hu.
  apply F'.le'_correct in Hu.
  destruct (F.toX xu) as [|xur] ; [easy|].
  assert (Hxur: (xur <= 2 * PI)%R).
  { revert Hu.
    elim (F.mul_DN_correct prec (lower (T.pi4 prec)) (F.fromZ 8)).
    2:{
      rewrite F.fromZ_correct by easy.
      rewrite (F'.valid_ub_real (F.fromZ 8))by now rewrite F.real_correct, F.fromZ_correct.
      generalize (T.pi4_correct prec).
      unfold T.I.convert.
      case T.pi4.
      { simpl; intros _; do 3 right; rewrite F'.valid_lb_nan, F'.nan_correct.
        repeat split; lra. }
      intros l u; simpl.
      rewrite F.valid_lb_correct.
      case F.classify; [..|intros [H0 H1]; lra]; intros _;
      (case F.toX; [now do 3 right; repeat split; lra|]; intro rl);
      (case (Rle_or_lt 0 rl); intro Hrl;
        [now left; repeat split; lra|do 3 right; repeat split; lra]). }
    intros Vmdn.
    unfold le_lower, le_upper.
    case F.toX; [easy|]; intro rmdn; simpl.
    rewrite F.fromZ_correct by easy.
    generalize (T.pi4_correct prec).
    unfold T.I.convert.
    case T.pi4; [now simpl; rewrite F'.nan_correct|]; intros l u.
    case (_ && _)%bool; [|intros [H0 H1]; lra].
    simpl.
    case F.toX; simpl; [easy|].
    intros rlpi4 [Hrlpi4 _].
    lra. }
  clear Hu.
  case_eq (F'.le' (F.mul_UP prec (upper (T.pi4 prec)) (F.fromZ 4)) xl).
  { intros Hl.
    apply F'.le'_correct in Hl.
    destruct (F.toX xl) as [|xlr].
    { now destruct (F.toX (F.mul_UP prec (upper (T.pi4 prec)) (F.fromZ 4))). }
    assert (Hxlr: (PI <= xlr)%R).
    { revert Hl.
      elim (F.mul_UP_correct prec (upper (T.pi4 prec)) (F.fromZ 4)).
      2:{
        rewrite F.fromZ_correct by easy.
        rewrite (F'.valid_ub_real (F.fromZ 4)) by now rewrite F.real_correct, F.fromZ_correct.
        generalize (T.pi4_correct prec).
        unfold T.I.convert.
        case T.pi4.
        { simpl; intros _; left; rewrite F'.valid_ub_nan, F'.nan_correct.
          repeat split; lra. }
        intros l u; simpl.
        rewrite F.valid_ub_correct, Bool.andb_comm.
        case F.classify; [..|intros [H0 H1]; lra|]; intros _;
          (case F.toX; [now left; repeat split; lra|]; intro ru);
          (case (Rle_or_lt 0 ru); intro Hru;
           [now left; repeat split; lra|do 2 right; left; lra]). }
      intros Vmup.
      rewrite F.fromZ_correct by easy.
      unfold le_upper.
      case F.toX; [easy|]; intro rmup.
      generalize (T.pi4_correct prec).
      unfold T.I.convert.
      case T.pi4; [now simpl; rewrite F'.nan_correct|]; intros l u.
      case (_ && _)%bool; [|intros [H0 H1]; lra].
      simpl.
      case (F.toX u); simpl; [easy|].
      intros rupi4 [_ Hrupi4].
      lra. }
    clear Hl.
    simpl.
    rewrite Hlb'_cos, Hub'_cos.
    split.
    { destruct (T.cos_fast prec xl) as [|cl cl'] ; simpl.
      { now rewrite F'.nan_correct. }
      revert Hcxl.
      unfold T.I.convert.
      case (_ && _)%bool; [|intros [H0 H1]; lra].
      intros [Hcl _].
      destruct (F.toX cl) as [|clr] ; [easy|].
      apply Rle_trans with (1 := Hcl).
      apply cos_incr_1 with (1 := Hxlr) (5 := Hxl).
      { apply Rle_trans with (2 := Hxur).
        apply Rle_trans with (1 := Hxl) (2 := Hxu). }
      { apply Rle_trans with (1 := Hxlr) (2 := Hxl). }
      apply Rle_trans with (1 := Hxu) (2 := Hxur). }
    destruct (T.cos_fast prec xu) as [|cu' cu] ; simpl.
    { now rewrite F'.nan_correct. }
    revert Hcxu.
    unfold T.I.convert.
    case (_ && _)%bool; [|intros [H0 H1]; lra].
    intros [_ Hcu].
    destruct (F.toX cu) as [|cur] ; [easy|].
    apply Rle_trans with (2 := Hcu).
    apply cos_incr_1 with (4 := Hxur) (5 := Hxu).
    { apply Rle_trans with (1 := Hxlr) (2 := Hxl). }
    { apply Rle_trans with (1 := Hxu) (2 := Hxur). }
    apply Rle_trans with (1 := Hxlr).
    apply Rle_trans with (1 := Hxl) (2 := Hxu). }
  intros _.
  unfold convert.
  simpl; rewrite F'.valid_lb_real.
  2: now rewrite F.real_correct, F.fromZ_correct; [..|lia].
  generalize (F'.max_valid_ub _ _ Hub_cos Hub'_cos).
  intros [Vmax Hmax].
  rewrite Vmax, Hmax.
  split.
  { rewrite F.fromZ_correct by easy.
    apply COS_bound. }
  destruct (T.cos_fast prec xl) as [|cl' cl] ; simpl.
  { now rewrite F'.nan_correct. }
  revert Hcxl.
  unfold T.I.convert; simpl.
  simpl in Hlb'_cos.
  rewrite Hlb'_cos.
  simpl in Hub_cos.
  rewrite Hub_cos.
  simpl.
  destruct (F.toX xl) as [|xlr] ; [easy|].
  intros [_ Hcl].
  destruct (F.toX cl) as [|clr] ; [easy|].
  destruct (T.cos_fast prec xu) as [|cu' cu] ; simpl.
  { now rewrite F'.nan_correct. }
  revert Hcxu.
  unfold T.I.convert.
  simpl in Hub'_cos.
  rewrite Hub'_cos.
  simpl in Hlb_cos.
  rewrite Hlb_cos.
  simpl.
  intros [_ Hcu].
  destruct (F.toX cu) as [|cur] ; [easy|].
  destruct (Rle_dec (Rabs x) PI) as [Hx|Hx].
  { apply Rle_trans with (2 := Rmax_l _ _).
    apply Rle_trans with (2 := Hcl).
    apply cos_decr_1 with (1 := Hal) (3 := Rabs_pos _) (4 := Hx) (5 := Hxl).
    apply Rle_trans with (1 := Hxl) (2 := Hx). }
  apply Rle_trans with (2 := Rmax_r _ _).
  apply Rle_trans with (2 := Hcu).
  apply Rnot_le_lt, Rlt_le in Hx.
  apply cos_incr_1 with (1 := Hx) (4 := Hxur) (5 := Hxu).
  { apply Rle_trans with (1 := Hxu) (2 := Hxur). }
  apply Rle_trans with (1 := Hx) (2 := Hxu). }
intros _.
case_eq (F'.le' (F.sub_UP prec xu xl) (F.fromZ 3)).
{ intros Hd.
  apply F'.le'_correct in Hd.
  revert Hd.
  elim (F.sub_UP_correct prec xu xl); [|easy..].
  intros Vsup.
  unfold le_upper.
  case F.toX; [easy|]; intro rsup.
  rewrite F.fromZ_correct by easy.
  case_eq (F.toX xu) ; [easy|] ; intros xur Hur.
  case_eq (F.toX xl) ; [easy|] ; intros xlr Hlr.
  rewrite Hur in Hxu.
  rewrite Hlr in Hxl.
  intros Hsup Hrsup3.
  simpl in Hsup.
  apply meet_correct.
  { unfold convert, bnd.
    rewrite F'.valid_ub_real, F'.valid_lb_real by now rewrite F.real_correct, F.fromZ_correct.
    rewrite 2!F.fromZ_correct by easy.
    apply COS_bound. }
  elim (F.midpoint_correct xl xu);
    [|easy|now rewrite F.real_correct, ?Hlr, ?Hur..
     |now unfold F.toR; rewrite Hlr, Hur; apply (Rle_trans _ _ _ Hxl)].
  set (m := F.midpoint xl xu).
  intros Rm [Hlm Hum].
  replace (Xreal (Rtrigo_def.cos (Rabs x)))
      with (Xadd (Xcos (Xreal (F.toR m))) (Xreal (Rtrigo_def.cos (Rabs x) - Rtrigo_def.cos (F.toR m))))
      by (apply (f_equal Xreal) ; ring).
  apply add_correct.
  { generalize (T.cos_fast_correct prec m).
    now rewrite (F'.real_correct _ Rm). }
  simpl.
  rewrite F'.valid_lb_neg.
  rewrite F'.neg_correct.
  elim (F.sub_UP_correct prec xu m);
    [|easy|now generalize (F.classify_correct m); rewrite Rm, F.valid_lb_correct;
           case F.classify].
  intros Vsxum Hsxum.
  elim (F.sub_UP_correct prec m xl);
    [|now generalize (F.classify_correct m); rewrite Rm, F.valid_ub_correct;
      case F.classify|easy].
  intros Vsmxl Hsmxl.
  elim (F'.max_valid_ub _ _ Vsxum Vsmxl).
  intros Vm Hm.
  rewrite Vm, Hm.
  revert Hsxum Hsmxl.
  rewrite Hlr, Hur, (F'.real_correct _ Rm).
  unfold le_upper.
  case F.toX; [easy|]; simpl.
  intros rsxum Hrsxum.
  case F.toX; [easy|]; simpl.
  intros rsmxl Hrsmxl.
  apply Raux.Rabs_le_inv.
  destruct (MVT_abs Rtrigo_def.cos (fun t => Ropp (sin t)) (F.toR m) (Rabs x)) as [v [-> _]].
  { intros c _.
    apply derivable_pt_lim_cos. }
  apply Rle_trans with (1 * Rabs (Rabs x - (F.toR m)))%R.
  { apply Rmult_le_compat_r.
    apply Rabs_pos.
    rewrite Rabs_Ropp.
    apply Rabs_le, SIN_bound. }
  rewrite Rmult_1_l.
  case (Rle_lt_dec (Rabs x) (F.toR m)); intro Hxm.
  { refine (Rle_trans _ _ _ _ (Rmax_r _ _)).
    rewrite Rabs_minus_sym, Rabs_pos_eq; [|lra].
    apply (Rle_trans _ ((F.toR m) - xlr)); lra. }
  refine (Rle_trans _ _ _ _ (Rmax_l _ _)).
  rewrite Rabs_pos_eq; [|lra].
  apply (Rle_trans _ (xur - (F.toR m))); lra. }
intros _.
unfold convert, bnd.
rewrite F'.valid_ub_real, F'.valid_lb_real by now rewrite F.real_correct, F.fromZ_correct.
rewrite 2!F.fromZ_correct by easy.
apply COS_bound.
Qed.

(* accurate only for |xi| <= 5/2*pi *)
Definition sin prec xi :=
  match xi with
  | Ibnd xl xu =>
    if F'.le' xu xl then T.sin_fast prec xl else
    let pi4 := T.pi4 prec in
    let pi2 := F.mul_DN prec (lower pi4) c2 in
    match F'.le' (F.neg pi2) xl, F'.le' xu pi2 with
    | true, true =>
      bnd (lower (T.sin_fast prec xl)) (upper (T.sin_fast prec xu))
    | true, false =>
      cos prec (sub prec (mul2 prec pi4) xi)
    | _, _ =>
      neg (cos prec (add prec xi (mul2 prec pi4)))
    end
  | Inan => Inan
  end.

Theorem sin_correct :
  forall prec, extension Xsin (sin prec).
Proof.
intros prec [|xl xu]; [easy|].
intros [|x].
{ now simpl; case (_ && _)%bool. }
intro Hx; generalize Hx.
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; lra].
intros Vxu Vxl [Hxl Hxu].
unfold sin, c2.
case_eq (F'.le' xu xl).
  intros Hl.
  apply F'.le'_correct in Hl.
  assert (Hsxl := T.sin_fast_correct prec xl).
  destruct (F.toX xu) as [|xur] ; try easy.
  destruct (F.toX xl) as [|xlr] ; try easy.
  replace x with xlr.
  exact Hsxl.
  apply Rle_antisym with (1 := Hxl).
  now apply Rle_trans with (2 := Hl).
intros _.
set (pi2 := F.mul_DN prec (lower (T.pi4 prec)) (F.fromZ 2)).
case_eq (F'.le' (F.neg pi2) xl).
  intros Hpl.
  generalize (F'.le'_correct _ _ Hpl).
  xreal_tac xl.
    now case (F.toX (F.neg pi2)).
  clear Hpl. intros Hpl.
  case_eq (F'.le' xu pi2).
    intros Hpu.
    generalize (F'.le'_correct _ _ Hpu).
    xreal_tac xu. easy.
    xreal_tac pi2. easy.
    clear Hpu. intros Hpu.
    revert Hpl.
    rewrite F'.neg_correct, X1.
    simpl.
    intros Hpl.
    elim (F.mul_DN_correct prec (lower (T.pi4 prec)) (F.fromZ 2)).
    2: {
      rewrite F.fromZ_correct by easy.
      rewrite (F'.valid_ub_real (F.fromZ 2)) by now rewrite F.real_correct, F.fromZ_correct.
      generalize (T.pi4_correct prec).
      unfold T.I.convert.
      case T.pi4.
      { intros _; do 3 right; simpl.
        rewrite F'.valid_lb_nan, F'.nan_correct; repeat split; lra. }
      intros pl pu; simpl.
      case (F.valid_lb pl); [|intros [H0 H1]; lra]; intros _.
      case F.toX; [do 3 right; repeat split; lra|].
      intro r'.
      case (Rle_or_lt 0 r'); intro Hr'; [left; split; lra|].
      do 3 right; repeat split; lra. }
    fold pi2.
    intros Vpi2.
    unfold le_lower, le_upper.
    rewrite X1, F.fromZ_correct by easy.
    simpl.
    generalize (T.pi4_correct prec).
    unfold T.I.convert.
    case T.pi4; [now simpl; rewrite F'.nan_correct|].
    intros pl pu.
    case (_ && _)%bool; [|intros [H0 H1]; lra].
    simpl.
    case F.toX; [easy|].
    intros rpl [Hrpl _].
    simpl.
    intro Hrpl'.
    assert (Hpl' : (-(PI/2) <= r)%R) by lra.
    assert (Hpu' : (r0 <= PI/2)%R) by lra.
    cut (match F.toX (upper (T.sin_fast prec xu)) with
         | Xnan => True
         | Xreal r3 => (Rtrigo_def.sin x <= r3)%R
         end).
    { cut (match F.toX (lower (T.sin_fast prec xl)) with
           | Xnan => True
           | Xreal r3 => (r3 <= Rtrigo_def.sin x)%R
           end).
      { generalize (T.sin_fast_correct prec xu).
        generalize (T.sin_fast_correct prec xl).
        destruct (T.sin_fast prec xl) as [|yl yu]; simpl;
          [rewrite F'.valid_lb_nan|];
          (destruct (T.sin_fast prec xu) as [|zl zu]; simpl;
           [rewrite F'.valid_ub_nan|]); rewrite ?F'.nan_correct; [easy|..];
            try (case (F.valid_lb yl);
                 [|now simpl; case Xsin; [|intros rs [H0 H1]; lra]]);
            try (case (F.valid_ub zu);
                 [|now intros _;
                   rewrite Bool.andb_comm; case Xsin; [|intros rs [H0 H1]; lra]]);
            try (case (F.valid_ub yu);
                 [|now simpl; case Xsin; [|intros rs [H0 H1]; lra]]);
            try (case (F.valid_lb zl);
                 [|now intros _;
                   rewrite Bool.andb_comm; case Xsin; [|intros rs [H0 H1]; lra]]);
            now case Xsin. }
      generalize (T.sin_fast_correct prec xl).
      destruct (T.sin_fast prec xl) as [|yl yu].
        simpl.
        now rewrite F'.nan_correct.
      rewrite X.
      simpl.
      xreal_tac yl. easy.
      case (_ && _)%bool; [|intros [H0 H1]; lra].
      intros [Hy _].
      apply Rle_trans with (1 := Hy).
      assert (H' := Rle_trans _ _ _ Hxu Hpu').
      apply sin_incr_1; try easy.
      now apply Rle_trans with x.
      now apply Rle_trans with r. }
    generalize (T.sin_fast_correct prec xu).
    destruct (T.sin_fast prec xu) as [|yl yu].
      simpl.
      now rewrite F'.nan_correct.
    rewrite X0.
    simpl.
    xreal_tac yu. easy.
    case (_ && _)%bool; [|intros [H0 H1]; lra].
    intros [_ Hy].
    apply Rle_trans with (2 := Hy).
    assert (H' := Rle_trans _ _ _ Hpl' Hxl).
    apply sin_incr_1 ; try easy.
    now apply Rle_trans with r0.
    now apply Rle_trans with x.
  intros _.
  unfold Xsin.
  rewrite <- cos_shift.
  change (Xreal (Rtrigo_def.cos (PI / 2 - x))) with (Xcos (Xsub (Xreal (PI / 2)) (Xreal x))).
  apply cos_correct.
  apply sub_correct with (2 := Hx).
  replace (PI / 2)%R with (PI / 4 * 2)%R by field.
  change (Xreal (PI / 4 * 2)) with (Xreal (PI / 4) * Xreal 2)%XR.
  apply mul2_correct.
  apply T.pi4_correct.
intros _.
rewrite <- (Ropp_involutive x).
unfold Xsin.
rewrite sin_neg.
apply (neg_correct _ (Xreal _)).
rewrite <- cos_shift.
replace (PI / 2 - - x)%R with (x + PI / 2)%R by ring.
change (Xreal (Rtrigo_def.cos (x + PI / 2))) with (Xcos (Xadd (Xreal x) (Xreal (PI / 2)))).
apply cos_correct.
apply (add_correct _ _ _ _ _ Hx).
replace (PI / 2)%R with (PI / 4 * 2)%R by field.
change (Xreal (PI / 4 * 2)) with (Xreal (PI / 4) * Xreal 2)%XR.
apply mul2_correct.
apply T.pi4_correct.
Qed.

(* meaningful only for |xi| <= pi/2 *)
Definition tan prec xi :=
  match xi with
  | Ibnd xl xu =>
    if F'.le' xu xl then T.tan_fast prec xl else
    let pi2 := F.mul_DN prec (lower (T.pi4 prec)) c2 in
    match F'.lt' (F.neg pi2) xl, F'.lt' xu pi2 with
    | true, true =>
      bnd (lower (T.tan_fast prec xl)) (upper (T.tan_fast prec xu))
    | _, _ => Inan
    end
  | Inan => Inan
  end.

Lemma tan_correct :
  forall prec, extension Xtan (tan prec).
Proof.
intros prec [|xl xu]; [easy|].
intros [|x].
{ now simpl; case (_ && _)%bool. }
intro Hx; generalize Hx.
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; lra].
intros Vxu Vxl [Hxl Hxu].
unfold tan, c2.
case_eq (F'.le' xu xl).
  intros Hl.
  apply F'.le'_correct in Hl.
  assert (Htxl := T.tan_fast_correct prec xl).
  unfold convert in Hx; rewrite Vxl, Vxu in Hx; simpl in Hx.
  destruct (F.toX xu) as [|xur] ; try easy.
  destruct (F.toX xl) as [|xlr] ; try easy.
  replace x with xlr.
  exact Htxl.
  apply Rle_antisym with (1 := proj1 Hx).
  apply Rle_trans with (2 := Hl).
  apply Hx.
intros _.
case_eq (F'.lt' (F.neg (F.mul_DN prec (lower (T.pi4 prec)) (F.fromZ 2))) xl) ; try easy.
intros Hlt1.
apply F'.lt'_correct in Hlt1.
case_eq (F'.lt' xu (F.mul_DN prec (lower (T.pi4 prec)) (F.fromZ 2))) ; try easy.
intros Hlt2.
apply F'.lt'_correct in Hlt2.
generalize (T.tan_correct prec xl) (T.tan_correct prec xu).
unfold convert in Hx; rewrite Vxl, Vxu in Hx; simpl in Hx.
destruct (F.toX xl) as [|rl].
{ now destruct (F.toX (F.neg (F.mul_DN prec (lower (T.pi4 prec)) (F.fromZ 2)))). }
destruct (F.toX xu) as [|ru] ; try easy.
intros Hl Hu.
rewrite bnd_correct.
2: { generalize (T.tan_fast_correct prec xl).
  unfold T.I.convert.
  case T.tan_fast; [now simpl; unfold valid_lb; rewrite F'.valid_lb_nan|].
  intros l u; simpl; unfold valid_lb; case F.valid_lb; [easy|].
  now case Xtan; [|intros r [H0 H1]; lra]. }
2: { generalize (T.tan_fast_correct prec xu).
  unfold T.I.convert.
  case T.tan_fast; [now simpl; unfold valid_ub; rewrite F'.valid_ub_nan|].
  intros l u; rewrite Bool.andb_comm.
  simpl; unfold valid_ub; case F.valid_ub; [easy|].
  now case Xtan; [|intros r [H0 H1]; lra]. }
rewrite F'.neg_correct in Hlt1.
elim (F.mul_DN_correct prec (lower (T.pi4 prec)) (F.fromZ 2)).
2: {
  rewrite F.fromZ_correct by easy.
  rewrite (F'.valid_ub_real (F.fromZ 2)) by now rewrite F.real_correct, F.fromZ_correct.
  generalize (T.pi4_correct prec).
  unfold T.I.convert.
  case T.pi4.
  { intros _; do 3 right; simpl.
    rewrite F'.valid_lb_nan, F'.nan_correct; repeat split; lra. }
  intros pl pu; simpl.
  case (F.valid_lb pl); [|intros [H0 H1]; lra]; intros _.
  case F.toX; [do 3 right; repeat split; lra|].
  intro r'.
  case (Rle_or_lt 0 r'); intro Hr'; [left; split; lra|].
  do 3 right; repeat split; lra. }
intro Vmpi2.
unfold le_lower, le_upper.
rewrite F.fromZ_correct by easy.
revert Hlt1 Hlt2.
case F.toX; [easy|]; intro rpi2.
simpl.
intros Hlt1 Hlt2.
generalize (T.pi4_correct prec).
destruct (T.pi4 prec) as [|pi4l pi4u].
{ now simpl; rewrite F'.nan_correct. }
unfold T.I.convert.
case (_ && _)%bool; [|intros [H0 H1]; lra].
intros [Hpil _].
simpl.
destruct (F.toX pi4l) as [|pi4r] ; [easy|].
simpl.
intro Hmpi2.
apply (Rmult_le_compat_r 2) in Hpil; [|now apply IZR_le].
unfold Rdiv in Hpil.
replace (PI * /4 * 2)%R with (PI / 2)%R in Hpil by field.
assert (H1: (- PI / 2 < rl)%R) by lra.
assert (H2: (ru < PI / 2)%R) by lra.
unfold Xtan'.
simpl.
case is_zero_spec.
simpl in Hx.
apply Rgt_not_eq, cos_gt_0.
apply Rlt_le_trans with (2 := proj1 Hx).
unfold Rdiv.
now rewrite <- Ropp_mult_distr_l_reverse.
now apply Rle_lt_trans with ru.
unfold Xtan' in Hl, Hu.
intros _.
split.
- destruct (T.tan_fast prec xl) as [|tl tu].
  simpl.
  now rewrite F'.nan_correct.
  revert Hl.
  simpl.
  case (_ && _)%bool; [|now case is_zero; [|intros [H0' H1']; lra]].
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
  now rewrite F'.nan_correct.
  revert Hu.
  simpl.
  case (_ && _)%bool; [|now case is_zero; [|intros [H0' H1']; lra]].
  simpl.
  case is_zero_spec ; [easy|].
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
     (if F.real xl then lower (T.atan_fast prec xl)
      else F.neg (F.mul_UP prec (upper (T.pi4 prec)) c2))
     (if F.real xu then upper (T.atan_fast prec xu)
      else F.mul_UP prec (upper (T.pi4 prec)) c2)
  | Inan => Inan
  end.

Lemma atan_correct :
  forall prec, extension Xatan (atan prec).
Proof.
intros prec [|xl xu]; [easy|].
intros [|x].
{ now simpl; case (_ && _)%bool. }
intro Hx; generalize Hx.
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; lra].
intros Vxu Vxl [Hxl Hxu].
assert (Hpi := T.pi4_correct prec).
simpl.
unfold c2.
unfold convert in Hx; rewrite Vxl, Vxu in Hx; simpl in Hx.
elim (F.mul_UP_correct prec (upper (T.pi4 prec)) (F.fromZ 2)).
2: {
  rewrite F.fromZ_correct by easy.
  rewrite (F'.valid_ub_real (F.fromZ 2)) by now rewrite F.real_correct, F.fromZ_correct.
  generalize (T.pi4_correct prec).
  unfold T.I.convert.
  case T.pi4.
  { intros _; left; simpl.
    rewrite F'.valid_ub_nan, F'.nan_correct; repeat split; lra. }
  intros pl pu; simpl.
  rewrite Bool.andb_comm.
  case (F.valid_ub pu); [|intros [H0 H1]; lra]; intros _.
  case F.toX; [left; repeat split; lra|].
  intro r'.
  case (Rle_or_lt 0 r'); intro Hr'; [left; repeat split; lra|].
  do 2 right; left; repeat split; lra. }
intros Vmpi2 Hmpi2.
set (l := if F.real xl then _ else _).
set (u := if F.real xu then _ else _).
assert (Vl : F.valid_lb l = true).
{ unfold l; rewrite F.real_correct.
  generalize (T.atan_fast_correct prec xl).
  case F.toX.
  { now intros _; rewrite F'.valid_lb_neg. }
  intro r.
  unfold T.I.convert.
  case T.atan_fast; [now simpl; rewrite F'.valid_lb_nan|].
  intros l' u'.
  simpl.
  now case F.valid_lb; [|intros [H0 H1]; lra]. }
assert (Vu : F.valid_ub u = true).
{ unfold u; rewrite F.real_correct.
  generalize (T.atan_fast_correct prec xu).
  case F.toX; [easy|].
  intro r.
  unfold T.I.convert.
  case T.atan_fast; [now simpl; rewrite F'.valid_ub_nan|].
  intros l' u'.
  simpl.
  now rewrite Bool.andb_comm; case F.valid_ub; [|intros [H0 H1]; lra]. }
rewrite Vl, Vu; simpl.
unfold l, u.
rewrite 2!F.real_correct.
split.
- generalize (proj1 Hx). clear Hx.
  case_eq (F.toX xl).
  intros _ _.
  rewrite F'.neg_correct.
  revert Hmpi2; unfold le_upper.
  case F.toX; [easy|]; intro rmpi2.
  rewrite F.fromZ_correct by easy.
  destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl.
  now rewrite F'.nan_correct.
  revert Hpi; simpl.
  case (_ && _)%bool; [|intros [H0 H1]; lra]; simpl; intro Hpi.
  destruct (F.toX pi4u) as [|rpi4] ; try easy.
  simpl.
  intro H.
  apply (Rle_trans _ _ _ (Ropp_le_contravar _ _ H)).
  apply Rlt_le.
  apply Rle_lt_trans with (2 := proj1 (atan_bound x)).
  lra.
  intros rl Hl Hx.
  generalize (T.atan_correct prec xl).
  destruct (T.atan_fast prec xl) as [|al au].
  intros _.
  simpl.
  now rewrite F'.nan_correct.
  simpl.
  rewrite Hl.
  case (_ && _)%bool; [|intros [H0 H1]; lra].
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
  revert Hmpi2.
  unfold le_upper.
  case F.toX; [easy|]; intro rmpi2.
  rewrite F.fromZ_correct by easy.
  destruct (T.pi4 prec) as [|pi4l pi4u] ; simpl.
  now rewrite F'.nan_correct.
  revert Hpi; simpl.
  case (_ && _)%bool; [|intros [H0 H1]; lra]; simpl; intro Hpi.
  destruct (F.toX pi4u) as [|rpi4] ; [easy|].
  simpl.
  apply Rle_trans.
  apply Rlt_le.
  apply Rlt_le_trans with (1 := proj2 (atan_bound x)).
  lra.
  intros rl Hl Hx.
  generalize (T.atan_correct prec xu).
  destruct (T.atan_fast prec xu) as [|al au].
  intros _.
  simpl.
  now rewrite F'.nan_correct.
  simpl.
  rewrite Hl.
  case (_ && _)%bool; [|intros [H0 H1]; lra].
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
     (if F.real xl then lower (T.exp_fast prec xl) else F.zero)
     (if F.real xu then upper (T.exp_fast prec xu) else F.nan)
  | Inan => Inan
  end.

Theorem exp_correct :
  forall prec, extension Xexp (exp prec).
Proof.
intros prec [|xl xu].
easy.
intros [|x].
now simpl; case (_ && _)%bool.
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; lra].
intros Vxu Vxl [Hxl Hxu].
simpl.
set (l := if F.real xl then _ else _).
set (u := if F.real xu then _ else _).
assert (Vl : F.valid_lb l = true).
{ unfold l.
  rewrite F.real_correct.
  generalize (T.exp_fast_correct prec xl).
  case F.toX.
  { now simpl; rewrite F'.valid_lb_zero. }
  intro rxl.
  unfold T.I.convert.
  simpl.
  case T.exp_fast.
  { now simpl; rewrite F'.valid_lb_nan. }
  intros rl ru.
  simpl.
  now case F.valid_lb; [|intros [H0 H1]; lra]. }
assert (Vu : F.valid_ub u = true).
{ unfold u.
  rewrite F.real_correct.
  generalize (T.exp_fast_correct prec xu).
  case F.toX.
  { now rewrite F'.valid_ub_nan. }
  intro rxu.
  unfold T.I.convert.
  simpl.
  case T.exp_fast.
  { now simpl; rewrite F'.valid_ub_nan. }
  intros rl ru.
  simpl; rewrite Bool.andb_comm.
  now case F.valid_ub; [|intros [H0 H1]; lra]. }
rewrite Vl, Vu; unfold l, u.
split.
(* lower *)
clear Hxu.
rewrite F.real_correct.
xreal_tac xl.
rewrite F.zero_correct.
simpl.
apply Rlt_le.
apply exp_pos.
generalize (T.exp_fast_correct prec xl).
destruct (T.exp_fast prec xl) as [|yl yu].
unfold lower.
now rewrite F'.nan_correct.
rewrite X.
unfold T.I.convert.
case (_ && _)%bool; [|intros [H0 H1]; lra].
intros (H, _).
simpl.
xreal_tac2.
apply Rle_trans with (1 := H).
now apply Raux.exp_le.
(* upper *)
clear Hxl.
rewrite F.real_correct.
xreal_tac xu.
now rewrite F'.nan_correct.
generalize (T.exp_fast_correct prec xu).
destruct (T.exp_fast prec xu) as [|yl yu].
unfold upper.
now rewrite F'.nan_correct.
rewrite X.
unfold T.I.convert.
case (_ && _)%bool; [|intros [H0 H1]; lra].
intros (_, H).
simpl.
xreal_tac2.
apply Rle_trans with (2 := H).
now apply Raux.exp_le.
Qed.

Definition ln prec xi :=
  match xi with
  | Ibnd xl xu =>
    if F'.lt' F.zero xl then
      Ibnd
        (lower (T.ln_fast prec xl))
        (if F.real xu then upper (T.ln_fast prec xu) else F.nan)
    else Inan
  | Inan => Inan
  end.

Theorem ln_correct :
  forall prec, extension Xln (ln prec).
Proof.
intros prec [|xl xu].
easy.
unfold Xln'.
intros [|x]; [now unfold convert; case (_ && _)%bool|].
simpl.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; lra].
intros Vxu Vxl [Hl Hu].
case_eq (F'.lt' F.zero xl) ; intros Hlt ; [|easy].
apply F'.lt'_correct in Hlt.
rewrite F.zero_correct in Hlt.
simpl.
set (l := lower _).
set (u := if F.real xu then _ else _).
assert (Vl : F.valid_lb l = true).
{ generalize (T.ln_fast_correct prec xl).
  unfold l, T.I.convert.
  case T.ln_fast; [now simpl; rewrite F'.valid_lb_nan|].
  intros rl ru.
  simpl.
  now case F.valid_lb; [|case Xln; [|intros r [H0 H1]; lra]]. }
assert (Vu : F.valid_ub u = true).
{ generalize (T.ln_fast_correct prec xu).
  unfold u, T.I.convert; simpl.
  rewrite F.real_correct.
  case F.toX; [now rewrite F'.valid_ub_nan|].
  intro r.
  case T.ln_fast; [now simpl; rewrite F'.valid_ub_nan|].
  intros rl ru.
  rewrite Bool.andb_comm; simpl.
  now case F.valid_ub; [|case Xln'; [|intros r' [H0 H1]; lra]]. }
rewrite Vl, Vu; unfold l, u; clear Vl l Vu u; simpl.
case is_positive_spec.
intros Hx.
simpl.
split.
generalize (T.ln_fast_correct prec xl).
case T.ln_fast.
intros _.
simpl.
now rewrite F'.nan_correct.
intros l u.
simpl.
case_eq (Xln (F.toX xl)); [now intros _; case (_ && _)%bool|].
intros lnx Hlnx.
case (_ && _)%bool; [|intros [H0 H1]; lra].
intros [H _].
destruct (F.toX l) as [|lr].
easy.
apply Rle_trans with (1 := H).
destruct (F.toX xl) as [|xlr].
easy.
revert Hlnx.
unfold Xln'.
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
rewrite F.real_correct.
case_eq (F.toX xu).
now rewrite F'.nan_correct.
intros xur Hxu.
rewrite Hxu in Hu.
generalize (T.ln_fast_correct prec xu).
case T.ln_fast.
intros _.
simpl.
now rewrite F'.nan_correct.
intros l u.
simpl.
rewrite Hxu.
unfold Xln'.
simpl.
case (_ && _)%bool; [|now case is_positive; [intros [H0 H1]; lra|]].
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

End FloatIntervalFull.
