(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

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

Require Import Reals Psatz.
Require Import Interval_xreal.
Require Import Interval_interval.
Require Import ssreflect.
Require Import xreal_ssr_compat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
