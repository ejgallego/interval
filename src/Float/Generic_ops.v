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
  Definition one := @Float radix false 1 0.
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
  Definition one_correct := refl_equal (Xreal R1).
  Definition nan_correct := refl_equal Xnan.
  Definition nearbyint_correct := @Fnearbyint_exact_correct radix.

  Definition real (f : float radix) := match f with Fnan => false | _ => true end.

  Lemma real_correct :
    forall f, real f = match toX f with Xnan => false | _ => true end.
  Proof.
  intros f.
  now case f.
  Qed.

  Definition valid_ub (_ : type) := true.
  Definition valid_lb (_ : type) := true.

  Lemma valid_lb_correct :
    forall f, real f = true -> valid_lb f = true.
  Proof. easy. Qed.

  Lemma valid_ub_correct :
    forall f, real f = true -> valid_ub f = true.
  Proof. easy. Qed.

  Lemma valid_lb_nan : valid_lb nan = true.
  Proof. easy. Qed.

  Lemma valid_ub_nan : valid_ub nan = true.
  Proof. easy. Qed.

  Lemma min_correct :
    forall x y,
    ((valid_lb x = true \/ valid_lb y = true)
     -> (valid_lb (min x y) = true /\ toX (min x y) = Xmin (toX x) (toX y)))
    /\ (valid_ub x = true -> valid_ub y = true
       -> (valid_ub (min x y) = true /\ toX (min x y) = Xmin (toX x) (toX y)))
    /\ (valid_lb y = false -> min x y = x)
    /\ (valid_lb x = false -> min x y = y).
  Proof. now intros x y; rewrite (Fmin_correct radix). Qed.

  Lemma max_correct :
    forall x y,
    ((valid_ub x = true \/ valid_ub y = true)
     -> (valid_ub (max x y) = true /\ toX (max x y) = Xmax (toX x) (toX y)))
    /\ (valid_lb x = true -> valid_lb y = true
       -> (valid_lb (max x y) = true /\ toX (max x y) = Xmax (toX x) (toX y)))
    /\ (valid_ub y = false -> max x y = x)
    /\ (valid_ub x = false -> max x y = y).
  Proof. now intros x y; rewrite (Fmax_correct radix). Qed.

  Lemma neg_correct :
    forall x, toX (neg x) = Xneg (toX x)
    /\ (valid_lb (neg x) = valid_ub x)
    /\ (valid_ub (neg x) = valid_lb x).
  Proof. now intro x; rewrite (Fneg_correct radix). Qed.

  Lemma abs_correct :
    forall x, toX (abs x) = Xabs (toX x) /\ (valid_ub (abs x) = true).
  Proof. now intro x; rewrite (Fabs_correct radix). Qed.

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
    valid_lb (fromZ_DN p n) = true /\ le_lower (toX (fromZ_DN p n)) (Xreal (IZR n)).
  Proof.
  intros p n.
  split.
  easy.
  rewrite fromZ_correct'.
  apply Rle_refl.
  Qed.

  Definition fromZ_UP (p : precision) := fromZ.

  Lemma fromZ_UP_correct :
    forall p n,
    valid_ub (fromZ_UP p n) = true /\ le_upper (Xreal (IZR n)) (toX (fromZ_UP p n)).
  Proof.
  intros p n.
  split.
  easy.
  rewrite fromZ_correct'.
  apply Rle_refl.
  Qed.

  Lemma add_UP_correct :
    forall p x y, valid_ub x = true -> valid_ub y = true
    -> (valid_ub (add_UP p x y) = true
       /\ le_upper (Xadd (toX x) (toX y)) (toX (add_UP p x y))).
  Proof.
  intros p x y _ _; split; [easy|].
  now apply (rnd_binop_UP_correct _ _ (@Fadd_correct _)).
  Qed.

  Lemma add_DN_correct :
    forall p x y, valid_lb x = true -> valid_lb y = true
    -> (valid_lb (add_DN p x y) = true
       /\ le_lower (toX (add_DN p x y)) (Xadd (toX x) (toX y))).
  Proof.
  intros p x y _ _; split; [easy|].
  now apply (rnd_binop_DN_correct _ _ (@Fadd_correct _)).
  Qed.

  Lemma sub_UP_correct :
    forall p x y, valid_ub x = true -> valid_lb y = true
    -> (valid_ub (sub_UP p x y) = true
        /\ le_upper (Xsub (toX x) (toX y)) (toX (sub_UP p x y))).
  Proof.
  intros p x y _ _; split; [easy|].
  now apply (rnd_binop_UP_correct _ _ (@Fsub_correct _)).
  Qed.

  Lemma sub_DN_correct :
    forall p x y, valid_lb x = true -> valid_ub y = true
    -> (valid_lb (sub_DN p x y) = true
       /\ le_lower (toX (sub_DN p x y)) (Xsub (toX x) (toX y))).
  Proof.
  intros p x y _ _; split; [easy|].
  now apply (rnd_binop_DN_correct _ _ (@Fsub_correct _)).
  Qed.

  Lemma mul_UP_correct :
    forall p x y,
    ((valid_ub x = true /\ valid_ub y = true
      /\ (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
      /\ (match toX y with Xnan => True | Xreal r => (0 <= r)%R end))
     \/ (valid_lb x = true /\ valid_lb y = true
         /\ (match toX x with Xnan => True | Xreal r => (r <= 0)%R end)
         /\ (match toX y with Xnan => True | Xreal r => (r <= 0)%R end))
     \/ (match toX x with Xnan => False | Xreal r => (r <= 0)%R end
        /\ match toX y with Xnan => False | Xreal r => (0 <= r)%R end)
     \/ (match toX x with Xnan => False | Xreal r => (0 <= r)%R end
        /\ match toX y with Xnan => False | Xreal r => (r <= 0)%R end))
    -> (valid_ub (mul_UP p x y) = true
        /\ le_upper (Xmul (toX x) (toX y)) (toX (mul_UP p x y))).
  Proof.
  intros p x y _; split; [easy|].
  now apply (rnd_binop_UP_correct _ _ (@Fmul_correct _)).
  Qed.

  Lemma mul_DN_correct :
    forall p x y,
    ((match toX x with Xnan => False | Xreal r => (0 <= r)%R end
      /\ match toX y with Xnan => False | Xreal r => (0 <= r)%R end)
     \/ (match toX x with Xnan => False | Xreal r => (r <= 0)%R end
        /\ match toX y with Xnan => False | Xreal r => (r <= 0)%R end)
     \/ (valid_ub x = true /\ valid_lb y = true
         /\ (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
         /\ (match toX y with Xnan => True | Xreal r => (r <= 0)%R end))
     \/ (valid_lb x = true /\ valid_ub y = true
         /\ (match toX x with Xnan => True | Xreal r => (r <= 0)%R end)
         /\ (match toX y with Xnan => True | Xreal r => (0 <= r)%R end)))
    -> (valid_lb (mul_DN p x y) = true
        /\ le_lower (toX (mul_DN p x y)) (Xmul (toX x) (toX y))).
  Proof.
  intros p x y _; split; [easy|].
  now apply (rnd_binop_DN_correct _ _ (@Fmul_correct _)).
  Qed.

  Lemma div_UP_correct :
    forall p x y,
    ((valid_ub x = true
      /\ (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
      /\ (match toX y with Xnan => False | Xreal r => (0 < r)%R end))
     \/ (valid_lb x = true
         /\ (match toX x with Xnan => True | Xreal r => (r <= 0)%R end)
         /\ (match toX y with Xnan => False | Xreal r => (r < 0)%R end))
     \/ (match toX x with Xnan => False | Xreal r => (0 <= r)%R end
        /\ match toX y with Xnan => False | Xreal r => (r < 0)%R end)
     \/ (match toX x with Xnan => False | Xreal r => (r <= 0)%R end
        /\ match toX y with Xnan => False | Xreal r => (0 < r)%R end))
    -> (valid_ub (div_UP p x y) = true
        /\ le_upper (Xdiv (toX x) (toX y)) (toX (div_UP p x y))).
  Proof.
  intros p x y _; split; [easy|].
  unfold div_UP.
  rewrite (@Fdiv_correct radix).
  set (z := Xdiv _ _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'; simpl].
  now apply Generic_fmt.round_UP_pt, FLX.FLX_exp_valid.
  Qed.

  Lemma div_DN_correct :
    forall p x y,
    ((valid_ub x = true
      /\ (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
      /\ (match toX y with Xnan => False | Xreal r => (r < 0)%R end))
     \/ (valid_lb x = true
         /\ (match toX x with Xnan => True | Xreal r => (r <= 0)%R end)
         /\ (match toX y with Xnan => False | Xreal r => (0 < r)%R end))
     \/ (match toX x with Xnan => False | Xreal r => (0 <= r)%R end
        /\ match toX y with Xnan => False | Xreal r => (0 < r)%R end)
     \/ (match toX x with Xnan => False | Xreal r => (r <= 0)%R end
        /\ match toX y with Xnan => False | Xreal r => (r < 0)%R end))
    -> (valid_lb (div_DN p x y) = true
        /\ le_lower (toX (div_DN p x y)) (Xdiv (toX x) (toX y))).
  Proof.
  intros p x y _; split; [easy|].
  unfold div_DN.
  rewrite (@Fdiv_correct radix).
  set (z := Xdiv _ _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'].
  unfold le_lower, Xneg; simpl; apply Ropp_le_contravar.
  now apply Generic_fmt.round_DN_pt, FLX.FLX_exp_valid.
  Qed.

  Lemma sqrt_UP_correct :
    forall p x,
    valid_ub x = true
    -> (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
    -> (valid_ub (sqrt_UP p x) = true
        /\ le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x))).
  Proof.
  intros p x _ _; split; [easy|].
  unfold sqrt_UP.
  rewrite (@Fsqrt_correct radix).
  set (z := Xsqrt _).
  unfold Xround, Xlift.
  case z; [exact I|intro z'; simpl].
  now apply Generic_fmt.round_UP_pt, FLX.FLX_exp_valid.
  Qed.

  Lemma sqrt_DN_correct :
    forall p x,
    valid_lb x = true
    -> (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
    -> (valid_lb (sqrt_DN p x) = true
        /\ le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x))).
  Proof.
  intros p x _ _; split; [easy|].
  unfold sqrt_DN.
  rewrite (@Fsqrt_correct radix).
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
