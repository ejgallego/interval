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

From Coq Require Import Bool Reals Psatz.
From Coquelicot Require Import Coquelicot.
From mathcomp.ssreflect Require Import ssreflect.

Require Import Stdlib.
Require Import Xreal.
Require Import Basic.

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
Proof.
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

Lemma contains_Xnan :
  forall xi, contains xi Xnan <-> xi = Inan.
Proof.
intros xi.
now case xi ; split.
Qed.

Lemma contains_Inan :
  forall xi x, xi = Inan -> contains xi x.
Proof.
now intros xi x ->.
Qed.

Lemma contains_le :
  forall xl xu v,
  contains (Ibnd xl xu) v ->
  le_lower xl v /\ le_upper v xu.
Proof.
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
Proof.
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

Definition subset' xi yi :=
  forall x, contains xi x -> contains yi x.

Theorem subset_contains :
  forall xi yi,
  subset xi yi ->
  subset' xi yi.
Proof.
intros xi yi.
destruct yi as [|yl yu].
easy.
destruct xi as [|xl xu].
easy.
intros [H1 H2] [|v] Hv.
easy.
apply contains_le in Hv.
apply le_contains.
now apply le_lower_trans with (1 := H1).
now apply le_upper_trans with (2 := H2).
Qed.

Definition domain P b :=
  forall x, contains b x -> P x.

Theorem bisect :
  forall P xl xm xu,
  domain P (Ibnd xl xm) ->
  domain P (Ibnd xm xu) ->
  domain P (Ibnd xl xu).
Proof.
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

Definition domain' P b :=
  forall x, contains b (Xreal x) -> P x.

Theorem bisect' :
  forall P xl xm xu,
  domain' P (Ibnd xl xm) ->
  domain' P (Ibnd xm xu) ->
  domain' P (Ibnd xl xu).
Proof.
intros P xl xm xu Hl Hu x H.
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

Definition not_empty xi :=
  exists v, contains xi (Xreal v).

Lemma contains_lower :
  forall l u x,
  contains (Ibnd (Xreal l) u) x ->
  contains (Ibnd (Xreal l) u) (Xreal l).
Proof.
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
Proof.
intros.
split.
destruct x as [|x].
elim H.
destruct l as [|l].
exact I.
apply Rle_trans with (1 := proj1 H) (2 := proj2 H).
apply Rle_refl.
Qed.

Module Type IntervalBasicOps.

Parameter bound_type : Type.
Parameter convert_bound : bound_type -> ExtendedR.
Parameter type : Type.
Parameter convert : type -> interval.
Parameter zero : type.
Parameter nai : type.
Parameter empty : type.
Parameter bnd : bound_type -> bound_type -> type.
Parameter real : type -> bool.

Parameter bnd_correct :
  forall l u,
  convert (bnd l u) = Ibnd (convert_bound l) (convert_bound u).

Parameter zero_correct :
  convert zero = Ibnd (Xreal 0) (Xreal 0).

Parameter nai_correct :
  convert nai = Inan.

Parameter empty_correct :
  forall x, contains (convert empty) x -> False.

Parameter real_correct :
  forall xi, real xi = match convert xi with Inan => false | _ => true end.

Local Notation subset_ := subset.

Parameter subset : type -> type -> bool.

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

Parameter meet_correct' :
  forall xi yi v,
  contains (convert (meet xi yi)) v ->
  contains (convert xi) v /\ contains (convert yi) v.

Parameter midpoint : type -> bound_type.

Parameter midpoint_correct :
  forall xi,
  (exists x, contains (convert xi) x) ->
  convert_bound (midpoint xi) = Xreal (proj_val (convert_bound (midpoint xi))) /\
  contains (convert xi) (convert_bound (midpoint xi)).

Parameter midpoint' : type -> type.

Parameter midpoint'_correct :
  forall xi,
  (forall x, contains (convert (midpoint' xi)) x -> contains (convert xi) x) /\
  (not_empty (convert xi) -> not_empty (convert (midpoint' xi))).

Definition extension f fi := forall b x,
  contains (convert b) x -> contains (convert (fi b)) (f x).

Definition extension_2 f fi := forall ix iy x y,
  contains (convert ix) x ->
  contains (convert iy) y ->
  contains (convert (fi ix iy)) (f x y).

Parameter mask : type -> type -> type.

Parameter mask_correct : extension_2 Xmask mask.
Parameter mask_correct' :
  forall xi yi x,
  contains (convert xi) x ->
  contains (convert (mask xi yi)) x.

Parameter precision : Type.

Parameter wider : precision -> type -> type -> bool.

Parameter neg : type -> type.
Parameter abs : type -> type.
Parameter inv : precision -> type -> type.
Parameter sqr : precision -> type -> type.
Parameter sqrt : precision -> type -> type.
Parameter add : precision -> type -> type -> type.
Parameter sub : precision -> type -> type -> type.
Parameter mul : precision -> type -> type -> type.
Parameter div : precision -> type -> type -> type.
Parameter power_int : precision -> type -> Z -> type.
Parameter nearbyint : rounding_mode -> type -> type.

Parameter neg_correct : extension Xneg neg.
Parameter abs_correct : extension Xabs abs.
Parameter inv_correct : forall prec, extension Xinv (inv prec).
Parameter sqr_correct : forall prec, extension Xsqr (sqr prec).
Parameter sqrt_correct : forall prec, extension Xsqrt (sqrt prec).
Parameter add_correct : forall prec, extension_2 Xadd (add prec).
Parameter sub_correct : forall prec, extension_2 Xsub (sub prec).
Parameter mul_correct : forall prec, extension_2 Xmul (mul prec).
Parameter div_correct : forall prec, extension_2 Xdiv (div prec).
Parameter power_int_correct : forall prec n, extension (fun x => Xpower_int x n) (fun x => power_int prec x n).
Parameter nearbyint_correct : forall mode, extension (Xnearbyint mode) (nearbyint mode).

Parameter neg_correct' :
  forall xi x,
  contains (convert (neg xi)) (Xneg x) ->
  contains (convert xi) x.

Parameter cancel_add : precision -> type -> type -> type.
Parameter cancel_sub : precision -> type -> type -> type.

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

Parameter lower_complement : type -> type.
Parameter upper_complement : type -> type.

Parameter lower_complement_correct :
  forall xi x y,
  contains (convert xi) (Xreal x) ->
  contains (convert (lower_complement xi)) (Xreal y) ->
  (y <= x)%R.

Parameter upper_complement_correct :
  forall xi x y,
  contains (convert xi) (Xreal x) ->
  contains (convert (upper_complement xi)) (Xreal y) ->
  (x <= y)%R.

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

Parameter fromZ_small : Z -> type.

Parameter fromZ_small_correct :
  forall v,
  (Z.abs v <= 256)%Z ->
  contains (convert (fromZ_small v)) (Xreal (IZR v)).

Parameter fromZ : precision -> Z -> type.

Parameter fromZ_correct :
  forall prec v, contains (convert (fromZ prec v)) (Xreal (IZR v)).

Definition propagate_l fi :=
  forall xi yi : type, convert xi = Inan -> convert (fi xi yi) = Inan.
Definition propagate_r fi :=
  forall xi yi : type, convert yi = Inan -> convert (fi xi yi) = Inan.

Parameter mask_propagate_l : propagate_l mask.
Parameter mask_propagate_r : propagate_r mask.
Parameter add_propagate_l : forall prec, propagate_l (add prec).
Parameter sub_propagate_l : forall prec, propagate_l (sub prec).
Parameter mul_propagate_l : forall prec, propagate_l (mul prec).
Parameter div_propagate_l : forall prec, propagate_l (div prec).
Parameter add_propagate_r : forall prec, propagate_r (add prec).
Parameter sub_propagate_r : forall prec, propagate_r (sub prec).
Parameter mul_propagate_r : forall prec, propagate_r (mul prec).
Parameter div_propagate_r : forall prec, propagate_r (div prec).

End IntervalBasicOps.

Module Type IntervalOps.

Include IntervalBasicOps.

Parameter pi : precision -> type.
Parameter cos : precision -> type -> type.
Parameter sin : precision -> type -> type.
Parameter tan : precision -> type -> type.
Parameter atan : precision -> type -> type.
Parameter exp : precision -> type -> type.
Parameter ln : precision -> type -> type.

Parameter pi_correct : forall prec, contains (convert (pi prec)) (Xreal PI).
Parameter cos_correct : forall prec, extension Xcos (cos prec).
Parameter sin_correct : forall prec, extension Xsin (sin prec).
Parameter tan_correct : forall prec, extension Xtan (tan prec).
Parameter atan_correct : forall prec, extension Xatan (atan prec).
Parameter exp_correct : forall prec, extension Xexp (exp prec).
Parameter ln_correct : forall prec, extension Xln (ln prec).

End IntervalOps.

Module IntervalBasicExt (I : IntervalBasicOps).

Definition propagate fi :=
  forall xi, I.convert xi = Inan -> I.convert (fi xi) = Inan.

Lemma propagate_extension :
  forall fi f, I.extension (Xbind f) fi -> propagate fi.
Proof.
intros fi f Hf xi H.
specialize (Hf xi Xnan).
rewrite H in Hf.
specialize (Hf I).
clear -Hf.
now destruct I.convert.
Qed.

Lemma neg_propagate : propagate I.neg.
Proof.
apply propagate_extension with (1 := I.neg_correct).
Qed.

Lemma inv_propagate : forall prec, propagate (I.inv prec).
Proof.
intros prec.
apply propagate_extension with (1 := I.inv_correct prec).
Qed.

Lemma sqrt_propagate : forall prec, propagate (I.sqrt prec).
Proof.
intros prec.
apply propagate_extension with (1 := I.sqrt_correct prec).
Qed.

Lemma power_int_propagate : forall prec n, propagate (fun x => I.power_int prec x n).
Proof.
intros prec n.
apply propagate_extension with (1 := I.power_int_correct prec n).
Qed.

Definition extension f fi :=
  forall (xi : I.type) (x : R),
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert (fi xi)) (Xreal (f x)).

Definition extension_2 f fi :=
  forall (xi yi : I.type) (x y : R),
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert yi) (Xreal y) ->
  contains (I.convert (fi xi yi)) (Xreal (f x y)).

Lemma neg_correct : extension Ropp I.neg.
Proof.
intros xi x.
now apply I.neg_correct.
Qed.

Lemma abs_correct : extension Rabs I.abs.
Proof.
intros xi x.
now apply I.abs_correct.
Qed.

Lemma inv_correct : forall prec, extension Rinv (I.inv prec).
Proof.
intros prec xi x Hx.
generalize (I.inv_correct prec xi _ Hx).
unfold Xinv', Xbind.
case is_zero ; try easy.
now case I.convert.
Qed.

Lemma sqr_correct : forall prec, extension Rsqr (I.sqr prec).
Proof.
intros prec xi x.
now apply I.sqr_correct.
Qed.

Lemma sqrt_correct : forall prec, extension sqrt (I.sqrt prec).
Proof.
intros prec xi x Hx.
generalize (I.sqrt_correct prec xi _ Hx).
unfold Xsqrt', Xbind.
case is_negative ; try easy.
now case I.convert.
Qed.

Lemma add_correct : forall prec, extension_2 Rplus (I.add prec).
Proof.
intros prec xi yi x y.
now apply I.add_correct.
Qed.

Lemma sub_correct : forall prec, extension_2 Rminus (I.sub prec).
Proof.
intros prec xi yi x y.
now apply I.sub_correct.
Qed.

Lemma mul_correct : forall prec, extension_2 Rmult (I.mul prec).
Proof.
intros prec xi yi x y.
now apply I.mul_correct.
Qed.

Lemma div_correct : forall prec, extension_2 Rdiv (I.div prec).
Proof.
intros prec xi yi x y Hx Hy.
generalize (I.div_correct prec _ _ _ _ Hx Hy).
simpl. unfold Xdiv'.
case is_zero ; try easy.
now case I.convert.
Qed.

Lemma nearbyint_correct :
  forall mode, extension (Rnearbyint mode) (I.nearbyint mode).
Proof.
intros mode xi x.
now apply I.nearbyint_correct.
Qed.

Lemma power_int_correct :
  forall prec n, extension (fun x => powerRZ x n) (fun xi => I.power_int prec xi n).
Proof.
intros prec n xi x Hx.
generalize (I.power_int_correct prec n xi _ Hx).
unfold Xpower_int, Xpower_int', Xbind.
destruct n as [|n|n] ; try easy.
case is_zero ; try easy.
now case I.convert.
Qed.

Lemma zero_correct : contains (I.convert I.zero) (Xreal 0).
Proof.
rewrite I.zero_correct.
split ; apply Rle_refl.
Qed.

Lemma contains_only_0 r :
  contains (I.convert I.zero) (Xreal r) -> r = 0%R.
Proof.
rewrite I.zero_correct.
intros [H1 H2].
now apply Rle_antisym.
Qed.

Lemma join_correct :
  forall ui vi u v x,
  contains (I.convert ui) (Xreal u) ->
  contains (I.convert vi) (Xreal v) ->
  (u <= x <= v)%R ->
  contains (I.convert (I.join ui vi)) (Xreal x).
Proof.
intros ui vi u v x Iu Iv [H1 H2].
assert (Hu := I.join_correct ui vi (Xreal u)).
assert (Hv := I.join_correct ui vi (Xreal v)).
destruct (I.convert (I.join ui vi)) as [|p q].
easy.
split.
destruct p as [|p].
easy.
apply Rle_trans with (2 := H1).
apply Hu.
now left.
destruct q as [|q].
easy.
apply Rle_trans with (1 := H2).
apply Hv.
now right.
Qed.

Lemma contains_RInt prec (f3 : R -> R) x1 x2 Y X1 X2 :
  ex_RInt f3 x1 x2->
  contains (I.convert X1) (Xreal x1) ->
  contains (I.convert X2) (Xreal x2) ->
  (forall x, (Rmin x1 x2 <= x <= Rmax x1 x2)%R -> contains (I.convert Y) (Xreal (f3 x))) ->
  contains (I.convert (I.mul prec (I.sub prec X2 X1) Y)) (Xreal (RInt f3 x1 x2)).
Proof.
move => Hf3_int HZx1 HZx2 Hext.
destruct (Req_dec x2 x1) as [H|H].
  rewrite H RInt_point /zero /= -(Rmult_0_l (f3 x1)) -(Rminus_diag_eq x2 x1) //.
  apply: mul_correct.
  exact: sub_correct.
  apply: Hext.
  exact: Rmin_Rmax_l.
have -> : (RInt f3 x1 x2 = (x2 - x1) * ((RInt f3 x1 x2) / (x2 - x1)))%R.
  rewrite /Rdiv (Rmult_comm _ (Rinv _)) -Rmult_assoc Rinv_r ?Rmult_1_l //.
  exact: Rminus_eq_contra.
apply: mul_correct.
exact: sub_correct.
wlog H': x1 x2 {H HZx1 HZx2} Hext Hf3_int / (x1 < x2)%R.
  intros H'.
  destruct (Rdichotomy _ _ H) as [H21|H12].
  rewrite -opp_RInt_swap.
  replace (-_/_)%R with (RInt f3 x2 x1 / (x1 - x2))%R by (field; lra).
  apply: H' H21.
  by rewrite Rmin_comm Rmax_comm.
  exact: ex_RInt_swap.
  exact: ex_RInt_swap.
  exact: H'.
case: (I.convert Y) Hext => // l u Hext.
apply: le_contains.
- rewrite /le_lower /le_upper /=.
  case: l Hext => //= rl Hext.
  apply: Ropp_le_contravar.
  apply: RInt_le_l => // x Hx.
  apply Hext.
  now rewrite -> Rmin_left, Rmax_right ; try apply Rlt_le.
- rewrite /le_upper /=.
  case: u Hext => //= ru Hext.
  apply: RInt_le_r => // x Hx.
  apply Hext.
  now rewrite -> Rmin_left, Rmax_right ; try apply Rlt_le.
Qed.

End IntervalBasicExt.

Module IntervalExt (I : IntervalOps).

Include (IntervalBasicExt I).

Lemma cos_correct : forall prec, extension cos (I.cos prec).
Proof.
intros prec xi x.
now apply I.cos_correct.
Qed.

Lemma sin_correct : forall prec, extension sin (I.sin prec).
Proof.
intros prec xi x.
now apply I.sin_correct.
Qed.

Lemma tan_correct : forall prec, extension tan (I.tan prec).
Proof.
intros prec xi x Hx.
generalize (I.tan_correct prec xi _ Hx).
unfold Xtan', Xbind.
case is_zero ; try easy.
now case I.convert.
Qed.

Lemma atan_correct : forall prec, extension atan (I.atan prec).
Proof.
intros prec xi x.
now apply I.atan_correct.
Qed.

Lemma exp_correct : forall prec, extension exp (I.exp prec).
Proof.
intros prec xi x.
now apply I.exp_correct.
Qed.

Lemma ln_correct : forall prec, extension ln (I.ln prec).
Proof.
intros prec xi x Hx.
generalize (I.ln_correct prec xi _ Hx).
unfold Xln', Xbind.
case is_positive ; try easy.
now case I.convert.
Qed.

End IntervalExt.
