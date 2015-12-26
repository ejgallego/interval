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

Require Import ZArith Psatz.
Require Import Flocq.Core.Fcore_Raux.
Require Import Interval_xreal.
Require Import Interval_generic Interval_interval.
Require Import Interval_definitions.
Require Import Interval_specific_ops.
Require Import Interval_float_sig.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Interval_xreal_derive.
Require Import Interval_missing.
Require Import Interval_generic_proof.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.bigop.
Require Import Rstruct xreal_ssr_compat.
Require Import seq_compl.
Require Import interval_compl.
Require Import poly_datatypes.
Require Import taylor_poly.
Require Import derive_compl.
Require Import basic_rec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The interface *)

Module Type PolyBound (I : IntervalOps) (Pol : PolyIntOps I).
Import Pol Pol.Notations.
Local Open Scope ipoly_scope.

Module Import Aux := IntervalAux I.

Parameter ComputeBound : Pol.U -> Pol.T -> I.type -> I.type.

Parameter ComputeBound_correct :
  forall u pi p,
  pi >:: p ->
  R_extension (PolR.eval tt p) (ComputeBound u pi).

Parameter ComputeBound_propagate :
  forall u pi p,
  pi >:: p ->
  I.propagate (ComputeBound u pi).

(*
Lemma ComputeBound_correct' :
  forall u p px,
  Link.contains_pointwise p px ->
  I.extension (toXreal_fun (PolR.teval tt px)) (ComputeBound u p).
Proof.
move=> u p px H.
apply: R_extension_correct.
by apply: ComputeBound_correct.
by apply: ComputeBound_propagate.
Qed.
*)

End PolyBound.

Module PolyBoundThm
  (I : IntervalOps)
  (Pol : PolyIntOps I)
  (Bnd : PolyBound I Pol).

Import Pol.Notations Bnd.
Local Open Scope ipoly_scope.

Module Import Aux := IntervalAux I.

Theorem ComputeBound_nth0 prec pi p X :
  pi >:: p ->
  X >: 0 ->
  forall r : R, (Pol.nth pi 0) >: r ->
                ComputeBound prec pi X >: r.
Proof.
move=> Hpi HX0 r Hr.
case E: (Pol.size pi) =>[|n].
  have->: r = PolR.eval tt p 0%R.
  rewrite Pol.nth_default ?E // I.zero_correct /= in Hr.
  have [A B] := Hr.
  have H := Rle_antisym _ _ B A.
  rewrite PolR.hornerE big1 //.
  by move=> i _; rewrite (Pol.nth_default_alt Hpi) ?E // Rmult_0_l.
  exact: ComputeBound_correct.
have->: r = PolR.eval tt (PolR.set_nth p 0 r) 0%R.
  rewrite PolR.hornerE PolR.size_set_nth max1n big_nat_recl //.
  rewrite PolR.nth_set_nth /= FullR.pow_0 Rmult_1_r big1 ?Rplus_0_r //.
  by move=> i _; rewrite FullR.pow_S [FullR.mul tt _ _]Rmult_0_l Rmult_0_r.
apply: ComputeBound_correct =>//.
have->: pi = Pol.set_nth pi 0 (Pol.nth pi 0).
  by rewrite Pol.set_nth_nth // E.
exact: Pol.set_nth_correct.
Qed.

Arguments ComputeBound_nth0 [prec pi] p [X] _ _ r _.

End PolyBoundThm.

(** Naive implementation: Horner evaluation *)

Module PolyBoundHorner (I : IntervalOps) (Pol : PolyIntOps I)
  <: PolyBound I Pol.

Import Pol.Notations.
Local Open Scope ipoly_scope.
Module Import Aux := IntervalAux I.

Definition ComputeBound : Pol.U -> Pol.T -> I.type -> I.type :=
  Pol.eval.

Theorem ComputeBound_correct :
  forall prec pi p,
  pi >:: p ->
  R_extension (PolR.eval tt p) (ComputeBound prec pi).
Proof.
move=> Hfifx X x Hx; rewrite /ComputeBound.
by move=> *; apply Pol.eval_correct.
Qed.

Arguments ComputeBound_correct [prec pi p] _ b x _.

(*
elim/PolR.tpoly_ind: fx fi Hfifx => [|a b IH]; elim/tpoly_ind.
- rewrite PolR.teval_polyNil teval_polyNil.
  change (Xreal 0) with (Xmask (Xreal 0) (Xreal x)).
  move=> *; apply: I.mask_correct =>//.
  by rewrite I.zero_correct; split; auto with real.
- clear; move=> c p _ [K1 K2].
  by rewrite tsize_polyCons PolR.tsize_polyNil in K1.
- clear; move=> [K1 K2].
  by rewrite PolR.tsize_polyCons tsize_polyNil in K1.
move=> d p _ [K1 K2].
rewrite PolR.teval_polyCons teval_polyCons.
rewrite Xreal_add.
apply: I.add_correct =>//.
  rewrite Xreal_mul.
  apply: I.mul_correct =>//.
  apply: IH.
  rewrite tsize_polyCons in K2.
  split.
    rewrite tsize_polyCons PolR.tsize_polyCons in K1.
    by case: K1.
  move=> k Hk.
  move/(_ k.+1 Hk) in K2.
  rewrite PolR.tnth_polyCons ?tnth_polyCons // in K2.
  rewrite tsize_polyCons PolR.tsize_polyCons in K1.
  by case: K1 =><-.
rewrite tsize_polyCons in K2.
move/(_ 0 erefl) in K2.
by rewrite tnth_polyCons ?PolR.tnth_polyCons in K2.
*)

Lemma ComputeBound_propagate :
  forall prec pi p,
  pi >:: p ->
  I.propagate (ComputeBound prec pi).
Proof. by red=> *; rewrite /ComputeBound Pol.eval_propagate. Qed.

Arguments ComputeBound_propagate [prec pi p] _ xi _.

End PolyBoundHorner.
