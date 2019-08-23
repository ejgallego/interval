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
Parameter real : type -> bool.
Parameter mag : type -> sfactor.
Parameter valid_ub : type -> bool.  (* valid upper bound (typically, not -oo) *)
Parameter valid_lb : type -> bool.  (* valid lower bound (typically, not +oo) *)

Parameter cmp : type -> type -> comparison.
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
Parameter nearbyint : rounding_mode -> type -> type.
Parameter midpoint : type -> type -> type.

Parameter zero_correct : toX zero = Xreal 0.
Parameter one_correct : toX one = Xreal 1.
Parameter nan_correct : toX nan = Xnan.

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

Parameter real_correct :
  forall f,
  real f = match toX f with Xnan => false | _ => true end.

Parameter valid_lb_correct :
  forall f, real f = true -> valid_lb f = true.

Parameter valid_ub_correct :
  forall f, real f = true -> valid_ub f = true.

Parameter valid_lb_nan : valid_lb nan = true.

Parameter valid_ub_nan : valid_ub nan = true.

Parameter cmp_correct :
  forall x y,
  toX x = Xreal (toR x) ->
  toX y = Xreal (toR y) ->
  cmp x y = Rcompare (toR x) (toR y).

Parameter min_correct :
  forall x y,
    ((valid_lb x = true \/ valid_lb y = true)
     -> (valid_lb (min x y) = true /\ toX (min x y) = Xmin (toX x) (toX y)))
    /\ (valid_ub x = true -> valid_ub y = true
       -> (valid_ub (min x y) = true /\ toX (min x y) = Xmin (toX x) (toX y)))
    /\ (valid_lb y = false -> min x y = x)
    /\ (valid_lb x = false -> min x y = y).

Parameter max_correct :
  forall x y,
    ((valid_ub x = true \/ valid_ub y = true)
     -> (valid_ub (max x y) = true /\ toX (max x y) = Xmax (toX x) (toX y)))
    /\ (valid_lb x = true -> valid_lb y = true
       -> (valid_lb (max x y) = true /\ toX (max x y) = Xmax (toX x) (toX y)))
    /\ (valid_ub y = false -> max x y = x)
    /\ (valid_ub x = false -> max x y = y).

Parameter neg_correct :
  forall x, toX (neg x) = Xneg (toX x)
    /\ (valid_lb (neg x) = valid_ub x)
    /\ (valid_ub (neg x) = valid_lb x).

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

Parameter nearbyint_correct :
  forall mode x,
  toX (nearbyint mode x) = Xnearbyint mode (toX x).

Parameter midpoint_correct :
  forall x y,
  sensible_format = true ->
  real x = true -> real y = true -> (toR x <= toR y)%R
  -> real (midpoint x y) = true /\ (toR x <= toR (midpoint x y) <= toR y)%R.

End FloatOps.

Module FloatExt (F : FloatOps).

Definition cmp x y:=
  if F.real x then
    if F.real y then
      match F.cmp x y with Lt => Xlt | Gt => Xgt | Eq => Xeq end
    else Xund
  else Xund.

Lemma cmp_correct :
  forall x y,
  cmp x y = Xcmp (F.toX x) (F.toX y).
Proof.
intros x y.
unfold cmp.
rewrite 2!F.real_correct.
generalize (F.cmp_correct x y).
unfold F.toR.
destruct (F.toX x) as [|rx] ;
  destruct (F.toX y) as [|ry] ; try easy.
simpl.
now intros ->.
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
  | Gt => false
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
now rewrite F.cmp_correct.
Qed.

Definition lt x y :=
  match F.cmp x y with
  | Lt  => true
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
now rewrite F.cmp_correct.
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

End FloatExt.
