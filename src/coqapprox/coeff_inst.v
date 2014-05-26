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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
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

Module FullReal <: FullOps.
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
Definition tnat := INR.
Definition tfromZ := IZR.
Definition tinv := --> Rinv.
Definition tcos := --> cos.
Definition tsin := --> sin.
Definition tsqr := --> fun x => Rmult x x.
Definition tsqrt := --> sqrt.
Definition tinvsqrt := --> fun x => (Rinv (sqrt x)).
Definition tcst : T -> T -> T := fun c _ => c.
(*
Parameter tln : U -> T -> T.
Parameter tatan : U -> T -> T.
Parameter tasin : U -> T -> T.
Parameter tacos : U -> T -> T.
*)
End FullReal.

Module FullXR <: ExactFullOps.
Definition U := unit.
Local Notation "--> e" := (fun _ : U => e).
Definition T := ExtendedR.
Definition tcst := Xmask.
Definition tzero := Xreal R0.
Definition tone := Xreal R1.
Definition topp := Xneg.
Definition tadd := --> Xadd.
Definition tsub := --> Xsub.
Definition tmul := --> Xmul.
Definition tdiv := --> Xdiv.
Definition tpower_int := --> Xpower_int.
Definition tpow := --> fun x n => Xpower_int x (Z_of_nat n).
Arguments tpow _ x n : simpl nomatch.
Definition texp := --> Xexp.
Definition tnat := fun n => Xreal (INR n).
Definition tfromZ := fun n => Xreal (IZR n).
Definition tinv := --> Xinv.
Definition tcos := --> Xcos.
Definition tsin := --> Xsin.
Definition tsqr := --> fun x => Xmul x x.
Definition tsqrt := --> Xsqrt.
Definition tinvsqrt := --> fun x => Xinv (Xsqrt x).
(*
Parameter tln : U -> T -> T.
Definition tatan := --> Xatan.
Parameter tasin : U -> T -> T.
Parameter tacos : U -> T -> T.
*)
Lemma tadd_zerol : left_id tzero (tadd tt). Proof Xadd_0_l.
Lemma tadd_zeror : right_id tzero (tadd tt). Proof Xadd_0_r.
Lemma tadd_comm : commutative (tadd tt). Proof Xadd_comm.
Lemma tadd_assoc : associative (tadd tt).
Proof. move=> *; symmetry; exact: Xadd_assoc. Qed.
Lemma tmul_onel : left_id tone (tmul tt). Proof Xmul_1_l.
Lemma tmul_oner : right_id tone (tmul tt). Proof Xmul_1_r.
Lemma tmul_comm : commutative (tmul tt). Proof Xmul_comm.
Lemma tmul_assoc : associative (tmul tt).
Proof. move=> *; symmetry; exact: Xmul_assoc. Qed.
Lemma tmul_distrl : left_distributive (tmul tt) (tadd tt).
Proof Xmul_Xadd_distr_r.
Lemma tmul_distrr : right_distributive (tmul tt) (tadd tt).
Proof.
by move=> x y z; rewrite tmul_comm tmul_distrl; rewrite 2![_ _ _ x]tmul_comm.
Qed.

Lemma mask_add_l : forall a b x, tcst (tadd tt a b) x = tadd tt (tcst a x) b.
Proof. by move=> a b x; case x. Qed.
Lemma mask_add_r : forall a b x, tcst (tadd tt a b) x = tadd tt a (tcst b x).
Proof. by move=> a b x; case x; rewrite /= ?[tadd _ _ Xnan]tadd_comm. Qed.
Lemma mask_mul_l : forall a b x, tcst (tmul tt a b) x = tmul tt (tcst a x) b.
Proof. by move=> a b x; case x. Qed.
Lemma mask_mul_r : forall a b x, tcst (tmul tt a b) x = tmul tt a (tcst b x).
Proof. by move=> a b x; case x; rewrite /= ?[tmul _ _ Xnan]tmul_comm. Qed.

Lemma tpow_0 : forall x, tpow tt x 0 = tcst tone x.
Proof. done. Qed.

Lemma tpow_S (x : ExtendedR) (n : nat) :
  tpow tt x n.+1 = tmul tt x (tpow tt x n).
Proof.
case: x =>//= r; case: n =>//= n.
congr Xreal; rewrite tech_pow_Rmult; congr pow.
by rewrite Pos2Nat.inj_succ.
Qed.

Lemma tpow_opp (x : ExtendedR) (n : Z) : x <> Xreal 0 ->
  tpower_int tt x (-n) = tinv tt (tpower_int tt x n).
Proof. (* this result might be replaced by a more high-level one *)
case: x =>//= r; case: n =>//=.
- by rewrite zeroF; auto with real.
- move=> p; case: (is_zero_spec r).
  + move->; rewrite pow_ne_zero ?zeroT //.
    zify; romega.
  + move=> Hr; rewrite zeroF //.
    exact: pow_nonzero.
- move=> p; case: (is_zero_spec r) =>[->//|Hr _].
  rewrite /tinv /Xinv zeroF; last by auto with real.
  by rewrite Rinv_involutive; auto with real.
Qed.

Lemma big_distrr_spec :
  forall n F a, n <> 0 -> tmul tt a (\big[tadd tt/tzero]_(i < n) F i) =
  \big[tadd tt/tzero]_(i < n) tmul tt a (F i).
Proof.
case=>[//|n] F; case=> [|a] _.
  rewrite [tmul _ Xnan _]/=.
  by rewrite (bigXadd_Xnan_i (n := n.+1) (i := ord0)).
rewrite /tadd /tzero /tmul.
rewrite Xmul_comm.
rewrite big_Xmul_Xadd_distr.
apply: eq_big=>//.
by move=> i _; rewrite Xmul_comm.
Qed.

Lemma mask_idemp : forall a x, tcst (tcst a x) x = tcst a x.
Proof. by move=>?; case. Qed.

Lemma mask_comm :
  (* useless, but just in case *)
  forall a x y, tcst (tcst a x) y = tcst (tcst a y) x.
Proof. by move=> ? [|r] [|s]. Qed.

Lemma mask0mul_l : forall x, tmul tt tzero x = tcst tzero x.
Proof.
case=>[|x]; rewrite /= ?[tmul _ _ Xnan]tmul_comm //.
rewrite /tzero; f_equal; ring.
Qed.

Lemma mask0mul_r : forall x, tmul tt x tzero = tcst tzero x.
Proof.
case=>[|x]; rewrite /= ?[tmul _ _ Xnan]tmul_comm //.
rewrite /tzero; f_equal; ring.
Qed.
End FullXR.

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
Definition tzero := I.fromZ Z0.
Lemma zero_correct : contains (I.convert tzero) (Xreal 0).
Proof I.fromZ_correct Z0.
Definition tone := I.fromZ 1.
Definition topp := I.neg.
Definition tadd := I.add.
Definition tsub := I.sub.
Definition tmul := I.mul.
Definition tdiv := I.div.
Definition tpower_int := I.power_int.
Definition texp := I.exp.
Definition tnat := fun n => I.fromZ (Z_of_nat n).
Definition tfromZ := I.fromZ.
Definition tinv := I.inv.
Definition tcos := I.cos.
Definition tsin := I.sin.
Definition tsqr := I.sqr.
Definition tsqrt := I.sqrt.
Definition tinvsqrt := fun prec x => I.inv prec (I.sqrt prec x).
Definition tcst : T -> T -> T := I.mask.
(*
Parameter tln : U -> T -> T.
Definition tatan := I.atan.
Parameter tasin : U -> T -> T.
Parameter tacos : U -> T -> T.
*)
End FullInt.
