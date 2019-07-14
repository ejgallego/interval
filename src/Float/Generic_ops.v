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

From Coq Require Import ZArith Reals Psatz.
From Flocq Require Import Raux.

Require Import Xreal.
Require Import Basic.
Require Import Generic.
Require Import Generic_proof.
Require Import Sig.
Require Import Interval.Interval.  (* for le_upper/lower, TODO PR: move them? *)

Module Type Radix.
  Parameter val : radix.
End Radix.

Module Radix2 <: Radix.
  Definition val := radix2.
End Radix2.

Module Radix10 <: Radix.
  Definition val := Build_radix 10 (refl_equal _).
End Radix10.

Module GenericFloat (Rad : Radix) <: FloatOps.

  Definition radix := Rad.val.
  Definition sensible_format := match radix_val radix with Zpos (xO _) => true | _ => false end.
  Definition type := float radix.
  Definition toF (x : type) := x.
  Definition toX (x : type) := FtoX x.
  Definition toR x := proj_val (toX x).
  Definition fromF (x : type) := x.
  Definition precision := positive.
  Definition sfactor := Z.
  Definition prec := fun x : positive => x.
  Definition ZtoS := fun x : Z => x.
  Definition StoZ := fun x : Z => x.
  Definition PtoP := fun x : positive => x.
  Definition incr_prec := Pplus.
  Definition zero := @Fzero radix.
  Definition nan := @Fnan radix.
  Definition mag := @Fmag radix.
  Definition cmp (x y : type) := match Fcmp x y with Xlt => Lt | Xgt => Gt | _ => Eq end.
  Definition min := @Fmin radix.
  Definition max := @Fmax radix.
  Definition neg := @Fneg radix.
  Definition abs := @Fabs radix.
  Definition scale := @Fscale radix.
  Definition div2 := @Fdiv2 radix.
  Definition add_UP := @Fadd radix rnd_UP.
  Definition add_DN := @Fadd radix rnd_DN.
  Definition sub_UP := @Fsub radix rnd_UP.
  Definition sub_DN := @Fsub radix rnd_DN.
  Definition mul_UP := @Fmul radix rnd_UP.
  Definition mul_DN := @Fmul radix rnd_DN.
  Definition div_UP := @Fdiv radix rnd_UP.
  Definition div_DN := @Fdiv radix rnd_DN.
  Definition sqrt_UP := @Fsqrt radix rnd_UP.
  Definition sqrt_DN := @Fsqrt radix rnd_DN.
  Definition nearbyint := @Fnearbyint_exact radix.
  Definition zero_correct := refl_equal (Xreal R0).
  Definition nan_correct := refl_equal Xnan.
  Definition min_correct := @Fmin_correct radix.
  Definition max_correct := @Fmax_correct radix.
  Definition neg_correct := @Fneg_correct radix.
  Definition abs_correct := @Fabs_correct radix.
  Definition nearbyint_correct := @Fnearbyint_exact_correct radix.

  Lemma rnd_binop_UP_correct op Rop :
    (forall mode p x y,
       toX (op mode p x y)
       = Xround radix mode (prec p) (Xlift2 Rop (toX x) (toX y)))
    -> forall p x y,
      le_upper (Xlift2 Rop (toX x) (toX y)) (toX (op rnd_UP p x y)).
  Proof.
  intros H p x y; rewrite H; clear H.
  set (z := Xlift2 _ _ _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'; simpl].
  now apply Generic_fmt.round_UP_pt, FLX.FLX_exp_valid.
  Qed.

  Lemma rnd_binop_DN_correct op Rop :
    (forall mode p x y,
       toX (op mode p x y)
       = Xround radix mode (prec p) (Xlift2 Rop (toX x) (toX y)))
    -> forall p x y,
      le_lower (toX (op rnd_DN p x y)) (Xlift2 Rop (toX x) (toX y)).
  Proof.
  intros H p x y; rewrite H; clear H.
  set (z := Xlift2 _ _ _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'].
  unfold le_lower, Xneg; simpl; apply Ropp_le_contravar.
  now apply Generic_fmt.round_DN_pt, FLX.FLX_exp_valid.
  Qed.

  Definition fromZ n : float radix := match n with Zpos p => Float false p Z0 | Zneg p => Float true p Z0 | Z0 => Fzero end.

  Lemma fromZ_correct' : forall n, toX (fromZ n) = Xreal (IZR n).
  Proof.
    intros. case n ; split.
  Qed.

  Lemma fromZ_correct :
    forall n,
    (Z.abs n <= 256)%Z ->
    toX (fromZ n) = Xreal (IZR n).
  Proof.
  intros n _.
  apply fromZ_correct'.
  Qed.

  Definition fromZ_DN (p : precision) := fromZ.

  Lemma fromZ_DN_correct :
    forall p n,
    le_lower (toX (fromZ_DN p n)) (Xreal (IZR n)).
  Proof.
  intros p n.
  rewrite fromZ_correct'.
  apply Rle_refl.
  Qed.

  Definition fromZ_UP (p : precision) := fromZ.

  Lemma fromZ_UP_correct :
    forall p n,
    le_upper (Xreal (IZR n)) (toX (fromZ_UP p n)).
  Proof.
  intros p n.
  rewrite fromZ_correct'.
  apply Rle_refl.
  Qed.

  Definition real (f : float radix) := match f with Fnan => false | _ => true end.

  Lemma real_correct :
    forall f, real f = match toX f with Xnan => false | _ => true end.
  Proof.
  intros f.
  now case f.
  Qed.

  Definition add_UP_correct :=
    rnd_binop_UP_correct Fadd Rplus (@Fadd_correct radix).
  Definition add_DN_correct :=
    rnd_binop_DN_correct Fadd Rplus (@Fadd_correct radix).
  Definition sub_UP_correct :=
    rnd_binop_UP_correct Fsub Rminus (@Fsub_correct radix).
  Definition sub_DN_correct :=
    rnd_binop_DN_correct Fsub Rminus (@Fsub_correct radix).
  Definition mul_UP_correct :=
    rnd_binop_UP_correct Fmul Rmult (@Fmul_correct radix).
  Definition mul_DN_correct :=
    rnd_binop_DN_correct Fmul Rmult (@Fmul_correct radix).

  Lemma div_UP_correct :
    forall p x y,
      le_upper (Xdiv (toX x) (toX y)) (toX (Fdiv rnd_UP p x y)).
  Proof.
  intros p x y; rewrite (@Fdiv_correct radix).
  set (z := Xdiv _ _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'; simpl].
  now apply Generic_fmt.round_UP_pt, FLX.FLX_exp_valid.
  Qed.

  Lemma div_DN_correct :
    forall p x y,
      le_lower (toX (Fdiv rnd_DN p x y)) (Xdiv (toX x) (toX y)).
  Proof.
  intros p x y; rewrite (@Fdiv_correct radix).
  set (z := Xdiv _ _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'].
  unfold le_lower, Xneg; simpl; apply Ropp_le_contravar.
  now apply Generic_fmt.round_DN_pt, FLX.FLX_exp_valid.
  Qed.

  Lemma sqrt_UP_correct :
    forall p x,
      le_upper (Xsqrt (toX x)) (toX (Fsqrt rnd_UP p x)).
  Proof.
  intros p x; rewrite (@Fsqrt_correct radix).
  set (z := Xsqrt _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'; simpl].
  now apply Generic_fmt.round_UP_pt, FLX.FLX_exp_valid.
  Qed.

  Lemma sqrt_DN_correct :
    forall p x,
      le_lower (toX (Fsqrt rnd_DN p x)) (Xsqrt (toX x)).
  Proof.
  intros p x; rewrite (@Fsqrt_correct radix).
  set (z := Xsqrt _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'].
  unfold le_lower, Xneg; simpl; apply Ropp_le_contravar.
  now apply Generic_fmt.round_DN_pt, FLX.FLX_exp_valid.
  Qed.

  Lemma cmp_correct :
    forall x y,
    toX x = Xreal (toR x) ->
    toX y = Xreal (toR y) ->
    cmp x y = Rcompare (toR x) (toR y).
  Proof.
  intros x y Rx Ry.
  unfold cmp.
  rewrite Fcmp_correct.
  unfold toX in Rx, Ry.
  rewrite Rx, Ry.
  simpl.
  now case Rcompare.
  Qed.

  Lemma div2_correct :
    forall x, sensible_format = true ->
    (1 / 256 <= Rabs (toR x))%R ->
    toX (div2 x) = Xdiv (toX x) (Xreal 2).
  Proof.
  intros x Hf _.
  unfold div2, Fdiv2, toX.
  rewrite Fscale2_correct; [|easy].
  simpl; unfold Z.pow_pos; simpl.
  rewrite Xdiv_split.
  unfold Xinv, Xinv'.
  now rewrite is_zero_false.
  Qed.

  Definition midpoint (x y : type) := Fscale2 (Fadd_exact x y) (ZtoS (-1)).

  Lemma midpoint_correct :
    forall x y,
    sensible_format = true ->
    real x = true -> real y = true -> (toR x <= toR y)%R
    -> real (midpoint x y) = true /\ (toR x <= toR (midpoint x y) <= toR y)%R.
  Proof.
  intros x y He.
  unfold toR, FtoX, midpoint.
  rewrite !real_correct.
  rewrite (Fscale2_correct _ _ _ He).
  rewrite Fadd_exact_correct.
  unfold toX.
  do 2 (case FtoX; [easy|]).
  change (bpow radix2 (ZtoS (-1))) with (/2)%R.
  clear x y; simpl; intros x y _ _ Hxy.
  now split; [|lra].
  Qed.

End GenericFloat.
