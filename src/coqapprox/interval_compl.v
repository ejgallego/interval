(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2014, ENS de Lyon and Inria.

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

Require Import ZArith Reals Psatz.
Require Import Interval_xreal.
Require Import Interval_interval.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import xreal_ssr_compat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ltn_leq_pred m n : m < n -> m <= n.-1.
Proof. by move=> H; rewrite -ltnS (ltn_predK H). Qed.

Lemma Xneg_as_Xmul (x : ExtendedR) : Xneg x = Xmul x (Xreal (-1)).
Proof. destruct x as [|x]; trivial; simpl; f_equal; ring. Qed.

Lemma contains_trans (X : interval) (a b c : ExtendedR) :
  contains X a -> contains X b -> contains (Interval_interval.Ibnd a b) c ->
  contains X c.
Proof.
intros Ha Hb Hc.
destruct a as [|a]; destruct b as [|b]; destruct c as [|c];
  destruct X as [|l u]; trivial.
- now destruct Ha.
- now destruct Ha.
- now destruct Hb.
- destruct l as [|l]; destruct u as [|u]; trivial; simpl in *.
  + now repeat split; apply Rle_trans with (1 := proj2 Hc) (2 := proj2 Hb).
  + now repeat split; apply Rle_trans with (1 := proj1 Ha) (2 := proj1 Hc).
  + split.
    * now apply Rle_trans with (1 := proj1 Ha) (2 := proj1 Hc).
    * now apply Rle_trans with (1 := proj2 Hc) (2 := proj2 Hb).
Qed.

Notation IIbnd := Interval_interval.Ibnd (only parsing).
Notation IInan := Interval_interval.Inan (only parsing).

Local Notation subset_ := Interval_interval.subset (only parsing).

Lemma subset_refl : forall x, subset_ x x.
Proof.
case => [|l u] =>//=; rewrite /le_lower /le_upper; split.
  by case (-l)%XR => //; apply Rle_refl.
by case u => //; apply Rle_refl.
Qed.

Lemma contains_subset (X Y : interval) :
  (exists t, contains X t) ->
  (forall v : ExtendedR, contains X v -> contains Y v) ->
  subset_ X Y.
Proof.
case: X =>[|l u]; case: Y =>[|L U] //; first by move=>_ /(_ Xnan); apply.
move=>[t Ht] Hmain.
have {t Ht} [r Hr] : exists r : R, contains (IIbnd l u) (Xreal r).
  exact: contains_not_empty Ht.
have H'r := Hmain _ Hr; split; move: Hmain Hr H'r.
  case: L=>[//|L]; case: l=>[|l] Hmain Hr H'r; first exfalso.
    move/(_ (Xreal (L - 1))): Hmain.
    by move: Hr H'r; rewrite /contains; case: u; intuition psatzl R.
  case/(_ (Xreal l)): Hmain.
    by move: Hr H'r; rewrite /contains; case: u; intuition psatzl R.
  by rewrite /le_lower => top _ /=; psatzl R.
case: U=>[//|U]; case: u=>[|u] Hmain Hr H'r; first exfalso.
  move/(_ (Xreal (U + 1))): Hmain.
  by move: Hr H'r; rewrite /contains; case: l; intuition psatzl R.
case/(_ (Xreal u)): Hmain =>//.
by move: Hr H'r; rewrite /contains; case: l; intuition psatzl R.
Qed.

Module IntervalAux (I : IntervalOps).

Section PrecArgument.

Variable prec : I.precision.

Lemma mul_0_contains_0_l y Y X :
  contains (I.convert Y) y ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.mul prec X Y)) (Xreal 0).
Proof.
move=> Hy H0.
have H0y ry : (Xreal 0) = (Xreal 0 * Xreal ry)%XR by rewrite /= Rmult_0_l.
case: y Hy => [|ry] Hy; [rewrite (H0y 0%R)|rewrite (H0y ry)];
  apply: I.mul_correct =>//.
by case ->: (I.convert Y) Hy.
Qed.

Lemma mul_0_contains_0_r y Y X :
  contains (I.convert Y) y ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.mul prec Y X)) (Xreal 0).
Proof.
move=> Hy H0.
have Hy0 ry : (Xreal 0) = (Xreal ry * Xreal 0)%XR by rewrite /= Rmult_0_r.
case: y Hy => [|ry] Hy; [rewrite (Hy0 0%R)|rewrite (Hy0 ry)];
  apply: I.mul_correct=>//.
by case: (I.convert Y) Hy.
Qed.

Lemma pow_contains_0 (X : I.type) (n : Z) :
  (n > 0)%Z ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.power_int prec X n)) (Xreal 0).
Proof.
move=> Hn HX.
rewrite (_: (Xreal 0) = (Xpower_int (Xreal 0) n)); first exact: I.power_int_correct.
case: n Hn =>//= p Hp; rewrite pow_ne_zero //.
by zify; auto with zarith.
Qed.

Lemma subset_sub_contains_0 x0 (X0 X : I.type) :
  contains (I.convert X0) x0 ->
  I.subset_ (I.convert X0) (I.convert X) ->
  contains (I.convert (I.sub prec X X0)) (Xreal 0).
Proof.
move=> Hx0 Hsub.
  have H1 : contains (I.convert X) x0.
    exact: (subset_contains (I.convert X0)).
have Hs := I.sub_correct prec X X0 x0 x0 H1 Hx0.
case cx0 : x0 Hs Hx0 => [|rx0].
  by case: (I.convert (I.sub prec X X0)).
rewrite (_: Xreal 0 = Xreal rx0 - Xreal rx0)%XR;
  last by rewrite /= Rminus_diag_eq.
by move=>*; apply: I.sub_correct=>//; apply: (subset_contains (I.convert X0)).
Qed.

Lemma subset_real_contains X rx ry c :
  contains (I.convert X) (Xreal rx) ->
  contains (I.convert X) (Xreal ry) -> (rx <= c <= ry)%Re ->
  contains (I.convert X) (Xreal c).
Proof.
case CX : (I.convert X) => [|l u] // => Hrx Hry Hc.
case Cl: l Hc Hrx Hry =>[|rl];
  case Cu : u =>[|ru] // [Hcx Hcy][Hxu0 Hxu][Hyu0 Hyu]; split => //.
  + by apply: (Rle_trans _ ry).
  + by apply: (Rle_trans _ rx).
  by apply: (Rle_trans _ rx).
by apply: (Rle_trans _ ry).
Qed.

Lemma Isub_Inan_propagate_l y Y X :
  contains (I.convert Y) y ->
  I.convert X = Interval_interval.Inan ->
  I.convert (I.sub prec X Y) = Interval_interval.Inan.
Proof.
move=> Hy Hnan; move/(I.sub_correct prec X Y Xnan y _): Hy; rewrite Hnan.
by case Cs : (I.convert (I.sub prec X Y))=> [//|l u] /(_ I).
Qed.

Lemma Isub_Inan_propagate_r y Y X :
  contains (I.convert Y) y ->
  I.convert X = Interval_interval.Inan ->
  I.convert (I.sub prec Y X) = Interval_interval.Inan.
Proof.
move=> Hy Hnan; move/(I.sub_correct prec Y X y Xnan): Hy.
rewrite Hnan (_ : y - Xnan = Xnan)%XR; last by case: y.
by case Cs : (I.convert (I.sub prec Y X)) => [//|l u] /(_ I).
Qed.

Lemma Imul_Inan_propagate_l y Y X :
  contains (I.convert Y) y ->
  I.convert X = Interval_interval.Inan ->
  I.convert (I.mul prec X Y) = Interval_interval.Inan.
Proof.
move=> Hy Hnan; move/(I.mul_correct prec X Y Xnan y _): Hy; rewrite Hnan.
by case Cs : (I.convert (I.mul prec X Y)) => [//|l u] /(_ I).
Qed.

Lemma Imul_Inan_propagate_r y Y X :
  contains (I.convert Y) y ->
  I.convert X = Interval_interval.Inan ->
  I.convert (I.mul prec Y X) = Interval_interval.Inan.
Proof.
move=> Hy Hnan; move/(I.mul_correct prec Y X y Xnan): Hy.
rewrite Hnan(_ : y*Xnan = Xnan)%XR; last by case: y.
by case Cs : (I.convert (I.mul prec Y X)) => [//|l u]/(_ I).
Qed.

Lemma Idiv_Inan_propagate_r y Y X :
  contains (I.convert Y) y ->
  I.convert X = Interval_interval.Inan ->
  I.convert (I.div prec Y X) = Interval_interval.Inan.
Proof.
move=> Hy Hnan; move/(I.div_correct prec Y X y Xnan): Hy.
rewrite Hnan (_ : y / Xnan = Xnan)%XR; last by case: y.
by case Cs : (I.convert (I.div prec Y X)) => [//|l u]/(_ I).
Qed.

Lemma Ipow_Inan_propagate (X : I.type) (n : Z) :
  I.convert X = Interval_interval.Inan ->
  I.convert (I.power_int prec X n) = Interval_interval.Inan.
Proof.
move=> Hnan.
move: (I.power_int_correct prec n X Xnan); rewrite Hnan.
by case Cs : (I.convert (I.power_int prec X n)) => [//|l u]/(_ I).
Qed.

Lemma Iadd_Inan_propagate_l y Y X :
  contains (I.convert Y) y ->
  I.convert X = Interval_interval.Inan ->
  I.convert (I.add prec X Y) = Interval_interval.Inan.
Proof.
move=> Hy Hnan; move/(I.add_correct prec X Y Xnan y _): Hy; rewrite Hnan.
by case Cs: (I.convert (I.add prec X Y)) => [//|l u] /(_ I).
Qed.

Lemma Iadd_Inan_propagate_r y Y X :
  contains (I.convert Y) y ->
  I.convert X = Interval_interval.Inan ->
  I.convert (I.add prec Y X) = Interval_interval.Inan.
Proof.
move=> Hy Hnan.
move: (I.add_correct prec Y X y Xnan Hy).
rewrite Hnan (_ : y+Xnan = Xnan)%XR; last by case: y Hy.
by case: (I.convert (I.add prec Y X)) => [//|l u] /(_ I).
Qed.

Lemma Iadd_zero_subset_l (a b : I.type) :
  (exists t, contains (I.convert a) t) ->
  contains (I.convert b) (Xreal 0) ->
  I.subset_ (I.convert a) (I.convert (I.add prec b a)).
Proof.
move=> Ht Hb0.
apply: contains_subset =>// v Hav.
move: {Hav} (I.add_correct prec b a (Xreal 0) v Hb0 Hav).
by case: v =>// r; rewrite /= Rplus_0_l.
Qed.

Lemma Iadd_zero_subset_r a b :
  (exists t, contains (I.convert a) t) ->
  contains (I.convert b) (Xreal 0) ->
  I.subset_ (I.convert a) (I.convert (I.add prec a b)).
Proof.
move=> Ht Hb0; apply: contains_subset =>// v Hav.
move: {Hav} (I.add_correct prec a b v (Xreal 0) Hav Hb0).
by case:v =>// r; rewrite /= Rplus_0_r.
Qed.

Lemma Iadd_Isub_aux b a B D :
  contains (I.convert B) b ->
  contains (I.convert D) (a - b)%XR ->
  contains (I.convert (I.add prec B D)) a.
Proof.
move=> Hb Hd.
case cb : b Hb=> [|rb].
  move=> Hb; rewrite (Iadd_Inan_propagate_l _ (y := (a-b)%XR)) => //=.
  by case: (I.convert B) Hb.
rewrite -cb => Hb; rewrite (_ : a = b + (a - b))%XR.
  by apply: I.add_correct.
rewrite cb; case: a Hd => //= r _.
by f_equal; ring.
Qed.

End PrecArgument.
End IntervalAux.
