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

Require Import ZArith.
Require Import Reals.
Require Import Interval_interval.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_specific_ops.
Require Import Interval_float_sig.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.bigop.
Require Import interval_compl.
Require Import xreal_ssr_compat.
Require Import poly_datatypes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "--> e"
  (at level 10, e at level 8, no associativity, format "-->  e").

Module BaseZ <: BaseOps.
Definition U := unit. (* exact arithmetic, no need for prec arg *)
Local Notation "--> e" := (fun _ : U => e).
Definition T := Z.
Definition tzero := Z0.
Definition tone := 1%Z.
Definition tadd := --> Zplus.
Definition tmul := --> Zmult.
Definition topp := Zopp.
Definition tsub := --> Zminus.
End BaseZ.

Module FullR <: ExactFullOps.
Definition U := unit.
Local Notation "--> e" := (fun _ : U => e).
Definition T := R.
Definition tzero := R0.
Definition tone := R1.
Definition topp := Ropp.
Definition tadd := --> Rplus.
Definition tsub := --> Rminus.
Definition tmul := --> Rmult.
Definition tdiv := --> Rdiv.
Definition tpower_int := --> powerRZ.
Definition texp := --> exp.
Definition tln := --> ln.
Definition tnat := INR.
Definition tfromZ := IZR.
Definition tinv := --> Rinv.
Definition tcos := --> cos.
Definition tsin := --> sin.
Definition tsqr := --> fun x => Rmult x x.
Definition tsqrt := --> sqrt.
Definition tinvsqrt := --> fun x => (Rinv (sqrt x)).
Definition tcst : T -> T -> T := fun c _ => c.
Definition ttan := --> tan.
Definition tatan := --> atan.
(*
Axiom tasin : U -> T -> T.
Axiom tacos : U -> T -> T.
*)
Lemma tadd_zerol : left_id tzero (tadd tt). Proof Rplus_0_l.
Lemma tadd_zeror : right_id tzero (tadd tt). Proof Rplus_0_r.
Lemma tadd_comm : commutative (tadd tt). Proof Rplus_comm.
Lemma tadd_assoc : associative (tadd tt).
Proof. move=> *; symmetry; exact: Rplus_assoc. Qed.
Lemma tmul_onel : left_id tone (tmul tt). Proof Rmult_1_l.
Lemma tmul_oner : right_id tone (tmul tt). Proof Rmult_1_r.
Lemma tmul_comm : commutative (tmul tt). Proof Rmult_comm.
Lemma tmul_assoc : associative (tmul tt).
Proof. move=> *; symmetry; exact: Rmult_assoc. Qed.
Lemma tmul_distrl : left_distributive (tmul tt) (tadd tt).
Proof Rmult_plus_distr_r.
Lemma tmul_distrr : right_distributive (tmul tt) (tadd tt).
Proof.
by move=> x y z; rewrite tmul_comm tmul_distrl; rewrite 2![_ _ _ x]tmul_comm.
Qed.


Definition tpow prec x n := (tpower_int prec x (Z_of_nat n)).

Lemma cstE : forall c x, tcst c x = c. Proof. done. Qed.
Lemma tpow_0 : forall x, tpow tt x 0 = R1. Proof. done. Qed.

Lemma tpow_S : forall x n, tpow tt x n.+1 = tmul tt x (tpow tt x n).
Proof.
by move=> x n; rewrite /tpow /tpower_int -!Interval_missing.pow_powerRZ.
Qed.

Lemma tpow_opp x n :
  x <> tzero -> tpower_int tt x (-n) = tinv tt (tpower_int tt x n).
Proof.
case: n =>//=; auto with real => p H.
rewrite /tinv ?Rinv_involutive //.
exact: pow_nonzero.
Qed.

Lemma tmul_zerol : left_zero tzero (tmul tt). Proof Rmult_0_l.
Lemma tmul_zeror : right_zero tzero (tmul tt). Proof Rmult_0_r.
End FullR.

(* Require Import NaryFunctions.
Implicit Arguments nuncurry [A B n].
Implicit Arguments ncurry [A B n]. *)
Definition nuncurry2 {A1 A2 B : Type} : (A1 -> A2 -> B) -> A1 * A2 -> B :=
  fun (f : A1 -> A2 -> B) (p : A1 * A2) => let (a, b) := p in f a b.

Module MaskBaseF (F:FloatOps with Definition even_radix := true) <: MaskBaseOps.
(* Minimal definitions for floats: only type T will be eventually used. *)
Definition U := (rounding_mode * F.precision)%type.
(* Erik: the parameter [PolyOps.U] will get the same definition. *)
Definition T := F.type.
Definition tzero := F.zero.
Definition tone := F.fromZ 1%Z.
Definition tadd : U -> T -> T -> T := nuncurry2 F.add.
Definition tmul : U -> T -> T -> T := nuncurry2 F.mul.
Definition topp : T -> T := F.neg.
Definition tsub : U -> T -> T -> T := nuncurry2 F.sub.
Definition tcst (c x : T) : T :=
  if F.real x then c else F.nan.
Definition tnat (n : nat) : T := F.fromZ (Z.of_nat n).
Definition tfromZ : Z -> T := F.fromZ.
End MaskBaseF.

Module MaskBaseF_NE (F : FloatOps with Definition even_radix := true)
  <: MaskBaseOps.
(* Minimal definitions for floats: only type T will be eventually used. *)
Definition U := F.precision.
Definition T := F.type.
Definition tzero := F.zero.
Definition tone := F.fromZ 1%Z.
Definition tadd : U -> T -> T -> T := F.add rnd_NE.
Definition tmul : U -> T -> T -> T := F.mul rnd_NE.
Definition topp : T -> T := F.neg.
Definition tsub : U -> T -> T -> T := F.sub rnd_NE.
Definition tcst (c x : T) : T :=
  if F.real x then c else F.nan.
Definition tnat (n : nat) : T := F.fromZ (Z.of_nat n).
Definition tfromZ : Z -> T := F.fromZ.
End MaskBaseF_NE.

Module FullInt (I : IntervalOps) <: FullOps.
Definition U := I.precision.
Definition T := I.type.
Definition tzero := I.zero.
Definition tone := I.fromZ 1.
Definition topp := I.neg.
Definition tadd := I.add.
Definition tsub := I.sub.
Definition tmul := I.mul.
Definition tdiv := I.div.
Definition tpower_int := I.power_int.
Definition texp := I.exp.
Definition tln := I.ln.
Definition tnat := fun n => I.fromZ (Z_of_nat n).
Definition tfromZ := I.fromZ.
Definition tinv := I.inv.
Definition tcos := I.cos.
Definition tsin := I.sin.
Definition tsqr := I.sqr.
Definition tsqrt := I.sqrt.
Definition tinvsqrt := fun prec x => I.inv prec (I.sqrt prec x).
Definition tcst : T -> T -> T := I.mask.
Definition ttan := I.tan.
Definition tatan := I.atan.
(*
Parameter tasin : U -> T -> T.
Parameter tacos : U -> T -> T.
*)
End FullInt.
