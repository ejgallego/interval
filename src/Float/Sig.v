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

From Coq Require Import ZArith Reals.
From Flocq Require Import Raux.

Require Import Xreal.
Require Import Basic.
Require Import Interval.Interval.  (* for le_upper/lower, TODO PR: move them? *)

Variant fclass := Freal | Fnan | Fminfty | Fpinfty.  (* TODO PR: move? *)

Module Type FloatOps.

Parameter sensible_format : bool.

Parameter radix : radix.
Parameter type : Type.
Parameter toF : type -> float radix.

Definition toX x := FtoX (toF x).
Definition toR x := proj_val (toX x).

Parameter precision : Type.
Parameter sfactor : Type.
Parameter prec : precision -> positive.
Parameter PtoP : positive -> precision.
Parameter ZtoS : Z -> sfactor.
Parameter StoZ : sfactor -> Z.

Parameter incr_prec : precision -> positive -> precision.

Parameter zero : type.
Parameter one : type.
Parameter nan : type.

Parameter fromZ : Z -> type.
Parameter fromZ_DN : precision -> Z -> type.
Parameter fromZ_UP : precision -> Z -> type.

Parameter fromF : float radix -> type.
Parameter classify : type -> fclass.
Parameter real : type -> bool.
Parameter is_nan : type -> bool.
Parameter mag : type -> sfactor.
Parameter valid_ub : type -> bool.  (* valid upper bound (typically, not -oo) *)
Parameter valid_lb : type -> bool.  (* valid lower bound (typically, not +oo) *)

Parameter cmp : type -> type -> Xcomparison.
Parameter min : type -> type -> type.
Parameter max : type -> type -> type.
Parameter neg : type -> type.
Parameter abs : type -> type.
Parameter scale : type -> sfactor -> type.
Parameter div2 : type -> type.
Parameter add_UP : precision -> type -> type -> type.
Parameter add_DN : precision -> type -> type -> type.
Parameter sub_UP : precision -> type -> type -> type.
Parameter sub_DN : precision -> type -> type -> type.
Parameter mul_UP : precision -> type -> type -> type.
Parameter mul_DN : precision -> type -> type -> type.
Parameter div_UP : precision -> type -> type -> type.
Parameter div_DN : precision -> type -> type -> type.
Parameter sqrt_UP : precision -> type -> type.
Parameter sqrt_DN : precision -> type -> type.
Parameter nearbyint_UP : rounding_mode -> type -> type.
Parameter nearbyint_DN : rounding_mode -> type -> type.
Parameter midpoint : type -> type -> type.

Parameter zero_correct : toX zero = Xreal 0.
Parameter one_correct : toX one = Xreal 1.
Parameter nan_correct : classify nan = Fnan.

Parameter fromZ_correct :
  forall n,
  (Z.abs n <= 256)%Z ->
  toX (fromZ n) = Xreal (IZR n).

Parameter fromZ_DN_correct :
  forall p n,
  valid_lb (fromZ_DN p n) = true /\ le_lower (toX (fromZ_DN p n)) (Xreal (IZR n)).

Parameter fromZ_UP_correct :
  forall p n,
  valid_ub (fromZ_UP p n) = true /\ le_upper (Xreal (IZR n)) (toX (fromZ_UP p n)).

Parameter classify_correct :
  forall f, real f = match classify f with Freal => true | _ => false end.

Parameter real_correct :
  forall f, real f = match toX f with Xnan => false | _ => true end.

Parameter is_nan_correct :
  forall f, is_nan f = match classify f with Fnan => true | _ => false end.

Parameter valid_lb_correct :
  forall f, valid_lb f = match classify f with Fpinfty => false | _ => true end.

Parameter valid_ub_correct :
  forall f, valid_ub f = match classify f with Fminfty => false | _ => true end.

Parameter cmp_correct :
  forall x y,
  cmp x y =
  match classify x, classify y with
  | Fnan, _ | _, Fnan => Xund
  | Fminfty, Fminfty => Xeq
  | Fminfty, _ => Xlt
  | _, Fminfty => Xgt
  | Fpinfty, Fpinfty => Xeq
  | _, Fpinfty => Xlt
  | Fpinfty, _ => Xgt
  | Freal, Freal => Xcmp (toX x) (toX y)
  end.

Parameter min_correct :
  forall x y,
  match classify x, classify y with
  | Fnan, _ | _, Fnan => classify (min x y) = Fnan
  | Fminfty, _ | _, Fminfty => classify (min x y) = Fminfty
  | Fpinfty, _ => min x y = y
  | _, Fpinfty => min x y = x
  | Freal, Freal => toX (min x y) = Xmin (toX x) (toX y)
  end.

Parameter max_correct :
  forall x y,
  match classify x, classify y with
  | Fnan, _ | _, Fnan => classify (max x y) = Fnan
  | Fpinfty, _ | _, Fpinfty => classify (max x y) = Fpinfty
  | Fminfty, _ => max x y = y
  | _, Fminfty => max x y = x
  | Freal, Freal => toX (max x y) = Xmax (toX x) (toX y)
  end.

Parameter neg_correct :
  forall x,
  match classify x with
  | Freal => toX (neg x) = Xneg (toX x)
  | Fnan => classify (neg x) = Fnan
  | Fminfty => classify (neg x) = Fpinfty
  | Fpinfty => classify (neg x) = Fminfty
  end.

Parameter abs_correct :
  forall x, toX (abs x) = Xabs (toX x) /\ (valid_ub (abs x) = true).

Parameter div2_correct :
  forall x, sensible_format = true ->
  (1 / 256 <= Rabs (toR x))%R ->
  toX (div2 x) = Xdiv (toX x) (Xreal 2).

Parameter add_UP_correct :
  forall p x y, valid_ub x = true -> valid_ub y = true
    -> (valid_ub (add_UP p x y) = true
       /\ le_upper (Xadd (toX x) (toX y)) (toX (add_UP p x y))).

Parameter add_DN_correct :
  forall p x y, valid_lb x = true -> valid_lb y = true
    -> (valid_lb (add_DN p x y) = true
       /\ le_lower (toX (add_DN p x y)) (Xadd (toX x) (toX y))).

Parameter sub_UP_correct :
  forall p x y, valid_ub x = true -> valid_lb y = true
    -> (valid_ub (sub_UP p x y) = true
       /\ le_upper (Xsub (toX x) (toX y)) (toX (sub_UP p x y))).

Parameter sub_DN_correct :
  forall p x y, valid_lb x = true -> valid_ub y = true
    -> (valid_lb (sub_DN p x y) = true
       /\ le_lower (toX (sub_DN p x y)) (Xsub (toX x) (toX y))).

Parameter mul_UP_correct :
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

Parameter mul_DN_correct :
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

Parameter div_UP_correct :
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

Parameter div_DN_correct :
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

Parameter sqrt_UP_correct :
  forall p x,
    valid_ub x = true
    -> (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
    -> (valid_ub (sqrt_UP p x) = true
        /\ le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x))).

Parameter sqrt_DN_correct :
  forall p x,
    valid_lb x = true
    -> (match toX x with Xnan => True | Xreal r => (0 <= r)%R end)
    -> (valid_lb (sqrt_DN p x) = true
        /\ le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x))).

Parameter nearbyint_UP_correct :
  forall mode x,
  valid_ub (nearbyint_UP mode x) = true
  /\ le_upper (Xnearbyint mode (toX x)) (toX (nearbyint_UP mode x)).

Parameter nearbyint_DN_correct :
  forall mode x,
  valid_lb (nearbyint_DN mode x) = true
  /\ le_lower (toX (nearbyint_DN mode x)) (Xnearbyint mode (toX x)).

Parameter midpoint_correct :
  forall x y,
  sensible_format = true ->
  real x = true -> real y = true -> (toR x <= toR y)%R
  -> real (midpoint x y) = true /\ (toR x <= toR (midpoint x y) <= toR y)%R.

End FloatOps.

Module FloatExt (F : FloatOps).

Lemma valid_lb_real f : F.real f = true -> F.valid_lb f = true.
Proof.
generalize (F.valid_lb_correct f).
generalize (F.classify_correct f).
now case F.classify; try easy; intro H; rewrite H.
Qed.

Lemma valid_ub_real f : F.real f = true -> F.valid_ub f = true.
Proof.
generalize (F.valid_ub_correct f).
generalize (F.classify_correct f).
now case F.classify; try easy; intro H; rewrite H.
Qed.

Lemma valid_lb_nan : F.valid_lb F.nan = true.
Proof.
generalize F.nan_correct.
generalize (F.valid_lb_correct F.nan).
now case F.classify.
Qed.

Lemma valid_ub_nan : F.valid_ub F.nan = true.
Proof.
generalize F.nan_correct.
generalize (F.valid_ub_correct F.nan).
now case F.classify.
Qed.

Lemma valid_lb_zero : F.valid_lb F.zero = true.
Proof.
generalize (F.valid_lb_correct F.zero).
generalize (F.classify_correct F.zero).
rewrite F.real_correct, F.zero_correct.
now case F.classify.
Qed.

Lemma valid_ub_zero : F.valid_ub F.zero = true.
Proof.
generalize (F.valid_ub_correct F.zero).
generalize (F.classify_correct F.zero).
rewrite F.real_correct, F.zero_correct.
now case F.classify.
Qed.

Lemma nan_correct : F.toX F.nan = Xnan.
Proof.
generalize (F.classify_correct F.nan).
generalize F.nan_correct.
case F.classify; [easy|intros _|easy..].
generalize (F.real_correct F.nan).
now case F.toX; [|intros r H; rewrite H].
Qed.

Lemma is_nan_nan : F.is_nan F.nan = true.
Proof. now rewrite F.is_nan_correct, F.nan_correct. Qed.

Lemma neg_correct x : F.toX (F.neg x) = Xneg (F.toX x).
Proof.
generalize (F.real_correct x).
generalize (F.real_correct (F.neg x)).
generalize (F.neg_correct x).
rewrite !F.classify_correct.
case F.classify; intro Hx; rewrite Hx; [|now case F.toX, F.toX..].
now case F.toX; [easy|]; intros rx; simpl; case F.classify.
Qed.

Lemma valid_lb_neg x : F.valid_lb (F.neg x) = F.valid_ub x.
Proof.
generalize (F.real_correct x).
generalize (F.real_correct (F.neg x)).
generalize (F.neg_correct x).
rewrite !F.classify_correct, !F.valid_lb_correct, !F.valid_ub_correct.
case F.classify; intro Hx; rewrite Hx; [|now case F.toX, F.toX..].
now case F.toX; [easy|]; intros rx; simpl; case F.classify.
Qed.

Lemma valid_ub_neg x : F.valid_ub (F.neg x) = F.valid_lb x.
Proof.
generalize (F.real_correct x).
generalize (F.real_correct (F.neg x)).
generalize (F.neg_correct x).
rewrite !F.classify_correct, !F.valid_lb_correct, !F.valid_ub_correct.
case F.classify; intro Hx; rewrite Hx; [|now case F.toX, F.toX..].
now case F.toX; [easy|]; intros rx; simpl; case F.classify.
Qed.

Lemma real_neg x : F.real (F.neg x) = F.real x.
Proof. now rewrite !F.real_correct, neg_correct; case F.toX. Qed.

Lemma is_nan_neg x : F.is_nan (F.neg x) = F.is_nan x.
Proof.
rewrite !F.is_nan_correct.
generalize (F.neg_correct x).
case_eq (F.classify x); [|now intros _ H; rewrite H..].
intro Hx.
generalize (F.classify_correct x); rewrite Hx, F.real_correct.
case F.toX; [easy|]; intros rx _.
generalize (F.classify_correct (F.neg x)).
rewrite F.real_correct.
case F.toX; [easy|]; intros rnx.
now case F.classify.
Qed.

Definition cmp x y:=
  if F.real x then
    if F.real y then
      F.cmp x y
    else Xund
  else Xund.

Lemma cmp_correct :
  forall x y,
  cmp x y = Xcmp (F.toX x) (F.toX y).
Proof.
intros x y.
unfold cmp.
rewrite !F.classify_correct, F.cmp_correct.
generalize (F.classify_correct x).
generalize (F.classify_correct y).
rewrite !F.real_correct.
now case (F.classify x), (F.classify y), (F.toX x), (F.toX y).
Qed.

Definition le' x y :=
  match cmp x y with
  | Xlt | Xeq => true
  | Xgt | Xund => false
  end.

Lemma le'_correct :
  forall x y,
  le' x y = true ->
  match F.toX x, F.toX y with
  | Xreal xr, Xreal yr => (xr <= yr)%R
  | _, _ => False
  end.
Proof.
intros x y.
unfold le'.
rewrite cmp_correct.
destruct F.toX as [|xr]. easy.
destruct F.toX as [|yr]. easy.
simpl.
now case Raux.Rcompare_spec ; auto with real.
Qed.

Definition lt' x y :=
  match cmp x y with
  | Xlt  => true
  | _ => false
  end.

Lemma lt'_correct :
  forall x y,
  lt' x y = true ->
  match F.toX x, F.toX y with
  | Xreal xr, Xreal yr => (xr < yr)%R
  | _, _ => False
  end.
Proof.
intros x y.
unfold lt'.
rewrite cmp_correct.
destruct F.toX as [|xr]. easy.
destruct F.toX as [|yr]. easy.
simpl.
now case Raux.Rcompare_spec.
Qed.

Definition le x y :=
  match F.cmp x y with
  | Xgt => false
  | _ => true
  end.

Lemma le_correct :
  forall x y,
  F.toX x = Xreal (F.toR x) ->
  F.toX y = Xreal (F.toR y) ->
  le x y = Rle_bool (F.toR x) (F.toR y).
Proof.
intros x y Rx Ry.
unfold le.
rewrite F.cmp_correct.
generalize (F.classify_correct x).
generalize (F.classify_correct y).
rewrite !F.real_correct, Rx, Ry.
do 2 (case F.classify; [|easy..]; intros _).
simpl.
unfold Rle_bool.
now case Rcompare.
Qed.

Definition lt x y :=
  match F.cmp x y with
  | Xlt  => true
  | _ => false
  end.

Lemma lt_correct :
  forall x y,
  F.toX x = Xreal (F.toR x) ->
  F.toX y = Xreal (F.toR y) ->
  lt x y = Rlt_bool (F.toR x) (F.toR y).
Proof.
intros x y Rx Ry.
unfold lt.
rewrite F.cmp_correct.
generalize (F.classify_correct x).
generalize (F.classify_correct y).
rewrite !F.real_correct, Rx, Ry.
do 2 (case F.classify; [|easy..]; intros _).
simpl.
unfold Rlt_bool.
now case Rcompare.
Qed.

Lemma real_correct :
  forall x,
  F.real x = true ->
  F.toX x = Xreal (F.toR x).
Proof.
intros x Rx.
rewrite F.real_correct in Rx.
unfold F.toR.
now destruct F.toX as [|rx].
Qed.

Inductive toX_prop (x : F.type) : ExtendedR -> Prop :=
  | toX_Xnan : toX_prop x Xnan
  | toX_Xreal : F.toX x = Xreal (F.toR x) -> toX_prop x (Xreal (F.toR x)).

Lemma toX_spec :
  forall x, toX_prop x (F.toX x).
Proof.
intros x.
case_eq (F.toX x).
intros _.
apply toX_Xnan.
intros r H.
change r with (proj_val (Xreal r)).
rewrite <- H.
apply toX_Xreal.
unfold F.toR.
now rewrite H at 2.
Qed.

Lemma classify_zero : F.classify F.zero = Freal.
Proof.
generalize (F.classify_correct F.zero).
rewrite F.real_correct, F.zero_correct.
now case F.classify.
Qed.

Lemma min_valid_lb x y :
  F.valid_lb x = true -> F.valid_lb y = true ->
  (F.valid_lb (F.min x y) = true
   /\ F.toX (F.min x y) = Xmin (F.toX x) (F.toX y)).
Proof.
rewrite !F.valid_lb_correct.
generalize (F.min_correct x y).
generalize (F.classify_correct x) ; rewrite F.real_correct ;
case_eq (F.classify x); intro Cx ; [..|easy] ;
  [case_eq (F.toX x); [easy|] ; intros rx Hx _
  |case_eq (F.toX x); [|easy] ; intros Hx _..] ;
  ( generalize (F.classify_correct y) ; rewrite F.real_correct ;
    case_eq (F.classify y); intro Cy ; [..|easy] ;
      [case_eq (F.toX y); [easy|] ; intros ry Hy _
      |case_eq (F.toX y); [|easy] ; intros Hy _..] ) ;
  intros Hmin _ _ ;
  generalize (F.classify_correct (F.min x y)) ; rewrite F.real_correct ;
  rewrite Hmin ;
  simpl ;
  rewrite ?Cx, ?Cy ;
  rewrite ?Hx, ?Hy ;
  [case F.classify ; easy|..] ;
  now case F.toX.
Qed.

Lemma max_valid_ub x y :
  F.valid_ub x = true -> F.valid_ub y = true ->
  (F.valid_ub (F.max x y) = true
   /\ F.toX (F.max x y) = Xmax (F.toX x) (F.toX y)).
Proof.
rewrite !F.valid_ub_correct.
generalize (F.max_correct x y).
generalize (F.classify_correct x) ; rewrite F.real_correct ;
case_eq (F.classify x); intro Cx ; [..|easy|] ;
  [case_eq (F.toX x); [easy|] ; intros rx Hx _
  |case_eq (F.toX x); [|easy] ; intros Hx _..] ;
  ( generalize (F.classify_correct y) ; rewrite F.real_correct ;
    case_eq (F.classify y); intro Cy ; [..|easy|] ;
      [case_eq (F.toX y); [easy|] ; intros ry Hy _
      |case_eq (F.toX y); [|easy] ; intros Hy _..] ) ;
  intros Hmax _ _ ;
  generalize (F.classify_correct (F.max x y)) ; rewrite F.real_correct ;
  rewrite Hmax ;
  simpl ;
  rewrite ?Cx, ?Cy ;
  rewrite ?Hx, ?Hy ;
  [case F.classify ; easy|..] ;
  now case F.toX.
Qed.

End FloatExt.
