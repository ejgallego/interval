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

Require Import Bool Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_float_sig.
Require Import Interval_generic.
Require Import Interval_generic_proof.

Inductive interval : Set :=
  | Inan : interval
  | Ibnd (l u : ExtendedR) : interval.

Definition Xlower (xi : interval) : ExtendedR :=
  match xi with
  | Ibnd xl _ => xl
  | _ => Xnan
  end.

Definition Xupper (xi : interval) : ExtendedR :=
  match xi with
  | Ibnd _ xu => xu
  | _ => Xnan
  end.

Definition contains i v :=
  match i, v with
  | Ibnd l u, Xreal x =>
    match l with
    | Xreal r => Rle r x
    | Xnan => True
    end /\
    match u with
    | Xreal r => Rle x r
    | Xnan => True
    end
  | Inan, _ => True
  | _, Xnan => False
  end.

Lemma contains_connected :
  forall xi, connected (fun x => contains xi (Xreal x)).
intros [|l u] a b Ha Hb x Hx.
exact I.
split.
destruct l as [|l].
exact I.
exact (Rle_trans _ _ _ (proj1 Ha) (proj1 Hx)).
destruct u as [|u].
exact I.
exact (Rle_trans _ _ _ (proj2 Hx) (proj2 Hb)).
Qed.

Definition le_upper x y :=
  match y with
  | Xnan => True
  | Xreal yr =>
    match x with
    | Xnan => False
    | Xreal xr => Rle xr yr
    end
  end.

Definition le_lower x y :=
  le_upper (Xneg y) (Xneg x).

(* There are probably more instances missing. *)

Lemma le_lower_refl (r : R) : le_lower (Xreal r) (Xreal r).
Proof. by rewrite /=; apply: Rle_refl. Qed.

Lemma le_upper_refl (r : R) : le_upper (Xreal r) (Xreal r).
Proof. by rewrite /=; apply: Rle_refl. Qed.

Lemma le_upper_trans :
  forall x y z,
  le_upper x y -> le_upper y z -> le_upper x z.
intros x y z.
case z.
split.
intro zr.
case y.
intros _ H.
elim H.
intros yr.
case x.
intros H _.
elim H.
intros xr.
simpl.
apply Rle_trans.
Qed.

Lemma le_lower_trans :
  forall x y z,
  le_lower x y -> le_lower y z -> le_lower x z.
unfold le_lower.
intros.
eapply le_upper_trans ; eassumption.
Qed.

Lemma contains_le :
  forall xl xu v,
  contains (Ibnd xl xu) v ->
  le_lower xl v /\ le_upper v xu.
intros xl xu v.
case v.
intro.
elim H.
intros r.
case xl.
intro.
exact H.
intros l (Hl, Hu).
split.
exact (Ropp_le_contravar _ _ Hl).
exact Hu.
Qed.

Lemma le_contains :
  forall xl xu v,
  le_lower xl (Xreal v) -> le_upper (Xreal v) xu ->
  contains (Ibnd xl xu) (Xreal v).
intros xl xu v.
case xl.
intros _ Hu.
exact (conj I Hu).
intros l Hl Hu.
split.
exact (Ropp_le_cancel _ _ Hl).
exact Hu.
Qed.

Definition subset xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    le_lower yl xl /\ le_upper xu yu
  | _, Inan => True
  | _, _ => False
  end.

Theorem subset_contains :
  forall xi yi,
  subset xi yi ->
  forall v,
  contains xi v ->
  contains yi v.
intros xi yi.
case yi.
intros _ v _.
exact I.
intros yl yu.
case xi.
intros H v _.
elim H.
intros xl xu Hx v.
case v.
intro H.
elim H.
intros r H.
apply le_contains.
apply le_lower_trans with xl.
exact (proj1 Hx).
exact (proj1 (contains_le _ _ _ H)).
apply le_upper_trans with xu.
exact (proj2 (contains_le _ _ _ H)).
exact (proj2 Hx).
Qed.

Definition domain P b :=
  forall x, contains b x -> P x.

Theorem subset_domain :
  forall P yi,
  domain P yi ->
  forall xi,
  subset xi yi ->
  domain P xi.
intros P yi Hp xi Hx x H.
apply Hp.
apply subset_contains with (1 := Hx).
exact H.
Qed.

Theorem subset_subset :
  forall xi yi zi,
  subset xi yi ->
  subset yi zi ->
  subset xi zi.
intros xi yi zi.
case zi.
case xi ; intros ; exact I.
intros zl zu.
case xi.
case yi ; simpl ; trivial.
intros xl xu.
case yi.
intros _ H.
elim H.
intros yl yu Hx Hy.
split.
apply le_lower_trans with yl.
exact (proj1 Hy).
exact (proj1 Hx).
apply le_upper_trans with yu.
exact (proj2 Hx).
exact (proj2 Hy).
Qed.

Theorem bisect :
  forall P xl xm xu,
  domain P (Ibnd xl xm) ->
  domain P (Ibnd xm xu) ->
  domain P (Ibnd xl xu).
intros P xl xm xu Hl Hu [|x] H.
elim H.
case_eq xm ; intros.
apply Hu.
rewrite H0.
exact (conj I (proj2 H)).
case (Rle_dec x r) ; intros Hr.
apply Hl.
apply le_contains.
exact (proj1 (contains_le _ _ _ H)).
rewrite H0.
exact Hr.
apply Hu.
apply le_contains.
rewrite H0.
unfold le_lower.
simpl.
apply Ropp_le_contravar.
auto with real.
exact (proj2 (contains_le _ _ _ H)).
Qed.

Definition le_mixed x y :=
  match y with
  | Xnan => True
  | Xreal yr =>
    match x with
    | Xnan => True
    | Xreal xr => Rle xr yr
    end
  end.

Lemma le_mixed_lower :
  forall xl yr,
  le_mixed xl (Xreal yr) -> le_lower xl (Xreal yr).
intros [|xr] yr H.
exact H.
exact (Ropp_le_contravar _ _ H).
Qed.

Lemma le_mixed_upper :
  forall xr yu,
  le_mixed (Xreal xr) yu -> le_upper (Xreal xr) yu.
intros xr [|yr] H ; exact H.
Qed.

Definition not_empty xi :=
  exists v, contains xi (Xreal v).

Lemma le_mixed_not_empty :
  forall x y, le_mixed x y ->
  not_empty (Ibnd x y).
intros [|xr] [|yr] Hl.
exists R0. now split.
exists yr. repeat split.
apply Rle_refl.
exists xr. repeat split.
apply Rle_refl.
exists xr. split.
apply Rle_refl.
exact Hl.
Qed.

Lemma contains_minf_not_empty :
  forall xu, not_empty (Ibnd Xnan xu).
intros [|xr].
exists R0. now split.
exists xr. repeat split.
apply Rle_refl.
Qed.

Lemma contains_pinf_not_empty :
  forall xl, not_empty (Ibnd xl Xnan).
intros [|xr].
exists R0. now split.
exists xr. repeat split.
apply Rle_refl.
Qed.

Lemma contains_not_empty :
  forall x xi, contains xi x -> not_empty xi.
intros x [|[u _|l [_|u]]].
intros _.
exists R0.
exact I.
apply contains_minf_not_empty.
apply contains_pinf_not_empty.
case x.
intro H.
elim H.
intros xr H.
exists xr.
exact H.
Qed.

Lemma contains_lower :
  forall l u x,
  contains (Ibnd (Xreal l) u) x ->
  contains (Ibnd (Xreal l) u) (Xreal l).
intros.
split.
apply Rle_refl.
destruct x as [|x].
elim H.
destruct u as [|u].
exact I.
apply Rle_trans with (1 := proj1 H) (2 := proj2 H).
Qed.

Lemma contains_upper :
  forall l u x,
  contains (Ibnd l (Xreal u)) x ->
  contains (Ibnd l (Xreal u)) (Xreal u).
intros.
split.
destruct x as [|x].
elim H.
destruct l as [|l].
exact I.
apply Rle_trans with (1 := proj1 H) (2 := proj2 H).
apply Rle_refl.
Qed.

(*
Lemma contains_not_empty_2 :
  forall xi x, contains xi x ->
 (exists v, forall y, contains xi y -> y = Xreal v) \/
 (exists u, exists v, (u < v)%R /\ subset (Ibnd (Xreal u) (Xreal v)) xi).
intros [|[u|l [|u]]] x H.
(* NaI *)
right.
exists R0.
exists R1.
exact (conj Rlt_0_1 I).
(* (-inf,?] *)
right.
destruct (contains_minf_not_empty u) as (v, Hv).
exists (v + -1)%R.
exists v.
split.
pattern v at 2 ; replace v with (v + -1 + 1)%R by ring.
apply Rlt_plus_1.
exact Hv.
(* [l,+inf) *)
right.
destruct (contains_pinf_not_empty (Xreal l)) as (v, Hv).
exists v.
exists (v + 1)%R.
split.
apply Rlt_plus_1.
split.
exact (Ropp_le_contravar _ _ (proj1 Hv)).
exact I.
(* [l,u] *)
destruct (contains_not_empty _ _ H) as (w, Hw).
destruct (Rle_lt_or_eq_dec _ _ (Rle_trans _ _ _ (proj1 Hw) (proj2 Hw))) as [Hr|Hr].
clear -Hr.
right.
exists l.
exists u.
split.
exact Hr.
split ; exact (Rle_refl _).
left.
exists l.
intros [|y] Hy.
elim Hy.
apply f_equal.
apply Rle_antisym.
rewrite <- Hr in Hy.
exact (proj2 Hy).
exact (proj1 Hy).
Qed.
*)

Definition overlap xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    (le_lower xl yl /\ le_mixed yl xu /\ le_mixed yl yu) \/
    (le_lower yl xl /\ le_mixed xl yu /\ le_mixed xl xu)
  | Ibnd xl xu, Inan => le_mixed xl xu
  | Inan, Ibnd yl yu => le_mixed yl yu
  | Inan, Inan => True
  end.

Lemma overlap_contains_aux :
  forall xl xu yl yu,
  le_lower xl yl -> le_mixed yl xu -> le_mixed yl yu ->
  exists v, contains (Ibnd xl xu) (Xreal v) /\ contains (Ibnd yl yu) (Xreal v).
intros xl xu yl yu Ho1 Ho2 Ho3.
destruct yl as [|yr].
destruct xl. 2: elim Ho1.
destruct xu as [|xr].
destruct (contains_minf_not_empty yu) as (yr, Hy).
exists yr.
split ; [ now split | exact Hy ].
destruct yu as [|yr].
exists xr. repeat split.
apply Rle_refl.
exists (Rmin xr yr).
repeat split.
apply Rmin_l.
apply Rmin_r.
exists yr.
split.
apply le_contains.
exact Ho1.
exact Ho2.
split.
apply Rle_refl.
exact Ho3.
Qed.

Theorem overlap_contains :
  forall xi yi,
  overlap xi yi ->
  exists v,
  contains xi (Xreal v) /\ contains yi (Xreal v).
intros [|xl xu] [|yl yu] Ho.
exists R0. now split.
destruct (le_mixed_not_empty _ _ Ho) as (v, Hv).
exists v. now split.
destruct (le_mixed_not_empty _ _ Ho) as (v, Hv).
exists v. now split.
destruct Ho as [(Ho1,(Ho2,Ho3))|(Ho1,(Ho2,Ho3))].
exact (overlap_contains_aux _ _ _ _ Ho1 Ho2 Ho3).
destruct (overlap_contains_aux _ _ _ _ Ho1 Ho2 Ho3) as (v, (H1, H2)).
exists v. split ; assumption.
Qed.

Definition interval_extension
  (f : ExtendedR -> ExtendedR)
  (fi : interval -> interval) :=
  forall b : interval, forall x : ExtendedR,
  contains b x -> contains (fi b) (f x).

Definition interval_extension_2
  (f : ExtendedR -> ExtendedR -> ExtendedR)
  (fi : interval -> interval -> interval) :=
  forall ix iy : interval, forall x y : ExtendedR,
  contains ix x -> contains iy y ->
  contains (fi ix iy) (f x y).

Module Type IntervalOps.

Parameter bound_type : Type.
Parameter convert_bound : bound_type -> ExtendedR.
Parameter type : Type.
Parameter convert : type -> interval.
Parameter zero : type.
Parameter nai : type.
Parameter bnd : bound_type -> bound_type -> type.

Parameter bnd_correct :
  forall l u,
  convert (bnd l u) = Ibnd (convert_bound l) (convert_bound u).

Parameter zero_correct :
  convert zero = Ibnd (Xreal 0) (Xreal 0).

Parameter nai_correct :
  convert nai = Inan.

Notation subset_ := subset.

Parameter subset : type -> type -> bool.
Parameter overlap : type -> type -> bool.

Parameter subset_correct :
  forall xi yi : type,
  subset xi yi = true -> subset_ (convert xi) (convert yi).

Parameter join : type -> type -> type.
Parameter meet : type -> type -> type.
Parameter sign_large : type -> Xcomparison.
Parameter sign_strict : type -> Xcomparison.

Parameter sign_large_correct :
  forall xi,
  match sign_large xi with
  | Xeq => forall x, contains (convert xi) x -> x = Xreal 0
  | Xlt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rle (proj_val x) 0
  | Xgt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rle 0 (proj_val x)
  | Xund => True
  end.

Parameter sign_strict_correct :
  forall xi,
  match sign_strict xi with
  | Xeq => forall x, contains (convert xi) x -> x = Xreal 0
  | Xlt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rlt (proj_val x) 0
  | Xgt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rlt 0 (proj_val x)
  | Xund => True
  end.

Parameter join_correct :
  forall xi yi v,
  contains (convert xi) v \/ contains (convert yi) v ->
  contains (convert (join xi yi)) v.

Parameter meet_correct :
  forall xi yi v,
  contains (convert xi) v -> contains (convert yi) v ->
  contains (convert (meet xi yi)) v.

Parameter midpoint : type -> bound_type.

Parameter midpoint_correct :
  forall xi,
  (exists x, contains (convert xi) x) ->
  convert_bound (midpoint xi) = Xreal (proj_val (convert_bound (midpoint xi))) /\
  contains (convert xi) (convert_bound (midpoint xi)).

Definition extension f fi := forall b x,
  contains (convert b) x -> contains (convert (fi b)) (f x).

Definition extension_2 f fi := forall ix iy x y,
  contains (convert ix) x ->
  contains (convert iy) y ->
  contains (convert (fi ix iy)) (f x y).

Parameter mask : type -> type -> type.

Parameter mask_correct : extension_2 Xmask mask.

Parameter precision : Type.

Parameter neg : type -> type.
Parameter abs : type -> type.
Parameter pi : precision -> type.
Parameter inv : precision -> type -> type.
Parameter sqr : precision -> type -> type.
Parameter sqrt : precision -> type -> type.
Parameter cos : precision -> type -> type.
Parameter sin : precision -> type -> type.
Parameter tan : precision -> type -> type.
Parameter atan : precision -> type -> type.
Parameter exp : precision -> type -> type.
Parameter ln : precision -> type -> type.
Parameter add : precision -> type -> type -> type.
Parameter sub : precision -> type -> type -> type.
Parameter mul : precision -> type -> type -> type.
Parameter div : precision -> type -> type -> type.
Parameter power_int : precision -> type -> Z -> type.

Parameter neg_correct : extension Xneg neg.
Parameter pi_correct : forall prec, contains (convert (pi prec)) (Xreal PI).
Parameter inv_correct : forall prec, extension Xinv (inv prec).
Parameter sqr_correct : forall prec, extension Xsqr (sqr prec).
Parameter abs_correct : extension Xabs abs.
Parameter sqrt_correct : forall prec, extension Xsqrt (sqrt prec).
Parameter cos_correct : forall prec, extension Xcos (cos prec).
Parameter sin_correct : forall prec, extension Xsin (sin prec).
Parameter tan_correct : forall prec, extension Xtan (tan prec).
Parameter atan_correct : forall prec, extension Xatan (atan prec).
Parameter exp_correct : forall prec, extension Xexp (exp prec).
Parameter ln_correct : forall prec, extension Xln (ln prec).
Parameter add_correct : forall prec, extension_2 Xadd (add prec).
Parameter sub_correct : forall prec, extension_2 Xsub (sub prec).
Parameter mul_correct : forall prec, extension_2 Xmul (mul prec).
Parameter div_correct : forall prec, extension_2 Xdiv (div prec).
Parameter power_int_correct : forall prec n, extension (fun x => Xpower_int x n) (fun x => power_int prec x n).

Parameter bounded : type -> bool.
Parameter lower_bounded : type -> bool.
Parameter upper_bounded : type -> bool.

Parameter lower_extent : type -> type.
Parameter upper_extent : type -> type.
Parameter whole : type.

Parameter lower_extent_correct :
  forall xi x y,
  contains (convert xi) (Xreal y) ->
  (x <= y)%R ->
  contains (convert (lower_extent xi)) (Xreal x).

Parameter upper_extent_correct :
  forall xi x y,
  contains (convert xi) (Xreal y) ->
  (y <= x)%R ->
  contains (convert (upper_extent xi)) (Xreal x).

Parameter whole_correct :
  forall x,
  contains (convert whole) (Xreal x).

Parameter lower : type -> bound_type.
Parameter upper : type -> bound_type.

Parameter lower_correct :
  forall xi : type, convert_bound (lower xi) = Xlower (convert xi).

Parameter upper_correct :
  forall xi : type, convert_bound (upper xi) = Xupper (convert xi).

Definition bounded_prop xi :=
  convert xi = Ibnd (convert_bound (lower xi)) (convert_bound (upper xi)).

Parameter lower_bounded_correct :
  forall xi,
  lower_bounded xi = true ->
  convert_bound (lower xi) = Xreal (proj_val (convert_bound (lower xi))) /\
  bounded_prop xi.

Parameter upper_bounded_correct :
  forall xi,
  upper_bounded xi = true ->
  convert_bound (upper xi) = Xreal (proj_val (convert_bound (upper xi))) /\
  bounded_prop xi.

Parameter bounded_correct :
  forall xi,
  bounded xi = true ->
  lower_bounded xi = true /\ upper_bounded xi = true.

Parameter fromZ : Z -> type.

Parameter fromZ_correct :
  forall v, contains (convert (fromZ v)) (Xreal (Z2R v)).

(* v1
Definition propagate fi :=
  forall x, contains (convert x) Xnan -> contains (convert (fi x)) Xnan.
*)
(* v2
Definition propagate fi := forall x, fi x = mask (fi x) x.
*)

(* v3
Definition propagate fi := fi nai = nai.
Definition propagate_l fi := forall xi : type, fi nai xi = nai.
Definition propagate_r fi := forall xi : type, fi xi nai = nai.
*)

Definition propagate fi :=
  forall xi, convert xi = Inan -> convert (fi xi) = Inan.
Definition propagate_l fi :=
  forall xi yi : type, convert xi = Inan -> convert (fi xi yi) = Inan.
Definition propagate_r fi :=
  forall xi yi : type, convert yi = Inan -> convert (fi xi yi) = Inan.

Parameter mask_propagate_l : propagate_l mask.
Parameter mask_propagate_r : propagate_r mask.
Parameter neg_propagate : propagate neg.
Parameter inv_propagate : forall prec, propagate (inv prec).
Parameter sqr_propagate : forall prec, propagate (sqr prec).
Parameter sqrt_propagate : forall prec, propagate (sqrt prec).
Parameter cos_propagate : forall prec, propagate (cos prec).
Parameter sin_propagate : forall prec, propagate (sin prec).
Parameter tan_propagate : forall prec, propagate (tan prec).
Parameter atan_propagate : forall prec, propagate (atan prec).
Parameter exp_propagate : forall prec, propagate (exp prec).
Parameter ln_propagate : forall prec, propagate (ln prec).
Parameter power_int_propagate : forall prec n, propagate (fun x => power_int prec x n).
Parameter add_propagate_l : forall prec, propagate_l (add prec).
Parameter sub_propagate_l : forall prec, propagate_l (sub prec).
Parameter mul_propagate_l : forall prec, propagate_l (mul prec).
Parameter div_propagate_l : forall prec, propagate_l (div prec).
Parameter add_propagate_r : forall prec, propagate_r (add prec).
Parameter sub_propagate_r : forall prec, propagate_r (sub prec).
Parameter mul_propagate_r : forall prec, propagate_r (mul prec).
Parameter div_propagate_r : forall prec, propagate_r (div prec).

End IntervalOps.
