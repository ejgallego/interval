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

Require Import Reals.
Require Import Psatz.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_xreal_derive.
Require Import Interval_interval.
Require Import Interval_generic_proof.
Require Import Rstruct.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq.
Require Import mathcomp.ssreflect.div mathcomp.ssreflect.fintype mathcomp.ssreflect.finfun mathcomp.ssreflect.path mathcomp.ssreflect.bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.
Delimit Scope XR_scope with XR.

Local Open Scope XR_scope.

Notation "x + y" := (Xadd x y) : XR_scope.
Notation "x - y" := (Xsub x y) : XR_scope.
Notation " - y" := (Xneg y) : XR_scope.
Notation "x * y" := (Xmul x y) : XR_scope.
Notation "x / y" := (Xdiv x y) : XR_scope.

Definition Xpow x n := Xpower_int x (Z_of_nat n).

Notation "x ^ n" := (Xpow x n) : XR_scope.

Arguments Xpow x n : simpl nomatch.

(* Erik: Xpow_iter, Xpow_idem, Xpow_Xreal may be removed
  in favor of fun x n => Xpower_int x (Z_of_nat n), cf. FullXR.tpow *)

Implicit Types n k : nat.
Implicit Type r : R.
Implicit Type X : interval.

Definition Xpow_iter x n := iter_nat (Xmul x) n (Xmask (Xreal 1) x).

(* "Transitional result" (may be removed in a later version) *)
Lemma Xpow_idem x n : Xpow x n = Xpow_iter x n.
Proof.
elim: n =>[//|n IHn].
rewrite /Xpow_iter iter_nat_S /= -/(Xpow_iter x n) -IHn.
case: {IHn} x =>//= r.
(* and similarly to the proof of FullXR.tpow_S *)
case: n =>// n.
by congr Xreal; rewrite tech_pow_Rmult; congr pow; rewrite Pos2Nat.inj_succ.
Qed.

Lemma Xpow_Xreal r n : Xpow_iter (Xreal r) n = Xreal (pow r n).
Proof.
by elim: n=>// n; rewrite /Xpow_iter iter_nat_S => /= ->.
Qed.

Lemma Xmul_Xreal a b : Xreal a * Xreal b = Xreal (a * b).
Proof. by []. Qed.

Lemma zeroF r : (r <> 0)%Re -> is_zero r = false.
Proof.
rewrite /is_zero /Req_bool; case E: (Rcompare r 0) =>//.
by rewrite (Rcompare_Eq_inv _ _ E).
Qed.

Lemma zeroT r : (r = 0)%Re -> is_zero r = true.
Proof. by move ->; rewrite is_zero_correct_zero. Qed.

Lemma positiveT x : (0 < x)%Re -> is_positive x = true.
Proof. by case: is_positive_spec =>//; move/Rle_not_lt. Qed.

Lemma negativeF x : (0 <= x)%Re -> is_negative x = false.
Proof. by case: is_negative_spec =>//; move/Rle_not_lt. Qed.

Lemma positiveF x : (x <= 0)%Re -> is_positive x = false.
Proof. by case: is_positive_spec =>//; move/Rle_not_lt. Qed.

Lemma negativeT x : (x < 0)%Re -> is_negative x = true.
Proof. by case: is_negative_spec =>//; move/Rle_not_lt. Qed.

Lemma XReq_EM_T : forall r1 r2:ExtendedR, {r1 = r2} + {r1 <> r2}.
Proof.
case=>[|r1] []; [left|move=> ?; right|right|move=> r2] =>//.
case: (Req_EM_T r1 r2); first by move ->; left.
by move=> Hr; right=> HX; apply: Hr; case: HX.
Qed.

Definition eqX x1 x2 : bool :=
  match XReq_EM_T x1 x2 with
    | left _ => true
    | right _ => false
  end.

Lemma eqXP : Equality.axiom eqX.
Proof.
move=> x1 x2; apply: (iffP idP) => [|<-].
  by rewrite /eqX; case: XReq_EM_T.
by rewrite /eqX; case: XReq_EM_T.
Qed.

Canonical Structure Xreal_eqMixin := EqMixin eqXP.
Canonical Structure Xreal_eqType := Eval hnf in
  EqType ExtendedR Xreal_eqMixin.

Lemma Xadd0 : left_id (Xreal 0%Re) Xadd.
Proof. by case=> // r; rewrite /= Rplus_0_l. Qed.

Lemma Xmul0 : left_id (Xreal 1%Re) Xmul.
Proof. by case=> // r; rewrite /= Rmult_1_l. Qed.

Local Open Scope XR_scope.

Lemma sum_f_to_big n (f : nat -> R) :
  sum_f_R0 f n = \big[Rplus/0%R]_(0 <= i < n.+1) f i.
Proof.
elim: n =>[|n IHn]; first by rewrite big_nat_recl // big_mkord big_ord0 Rplus_0_r.
by rewrite big_nat_recr //= IHn.
Qed.

Lemma contains_Xnan (X : interval) :
  contains X Xnan <-> X = Interval_interval.Inan.
Proof. by case: X. Qed.
