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
Require Import xreal_ssr_compat.
Require Import seq_compl.
Require Import interval_compl.
Require Import poly_datatypes.
Require Import taylor_poly.
Require Import coeff_inst.
Require Import rpa_inst.
Require Import derive_compl.
Require Import basic_rec.

(** The interface *)

Module Type PolyBound
  (I : IntervalOps)
  (Import Pol : IntMonomPolyOps I)
  (PolR : (*FIXME/Exact*)MonomPolyOps FullR)
  (Link : LinkIntR I Pol PolR).

Module Import Aux := IntervalAux I.

Parameter ComputeBound : Pol.U -> Pol.T -> I.type -> I.type.

Parameter ComputeBound_correct :
  forall u p px,
  Link.contains_pointwise p px ->
  R_extension (PolR.teval tt px) (ComputeBound u p).

Parameter ComputeBound_propagate :
  forall u p, I_propagate (ComputeBound u p).

End PolyBound.

Module PolyBoundThm
  (I : IntervalOps)
  (Import Pol : IntMonomPolyOps I)
  (PolR : ExactMonomPolyOps FullR)
  (Link : LinkIntR I Pol PolR)
  (Import Bnd : PolyBound I Pol PolR Link).

Module Import Aux := IntervalAux I.

Theorem ComputeBound_nth0 prec p px X :
  Link.contains_pointwise p px ->
  contains (I.convert X) (Xreal 0) ->
  I.subset_ (I.convert (tnth p 0)) (I.convert (ComputeBound prec p X)).
Proof.
move=> [Hsiz Hnth] HX.
case Ep: (Pol.tsize p) =>[|n].
  (* tsize p = 0 *)
  rewrite Pol.tnth_out ?Ep// I.zero_correct.
  apply: contains_subset; first by exists (Xreal 0); split; auto with real.
  move=> [//|v] Hv; rewrite /contains in Hv.
  have{v Hv}->: v = R0 by apply: Rle_antisym; case: Hv.
  suff->: R0 = (PolR.teval tt px R0).
  exact: ComputeBound_correct HX.
  have {p Hsiz Hnth Ep} Epx : PolR.tsize px = 0 by rewrite -Hsiz.
  elim/PolR.tpoly_ind: px Epx; first by rewrite PolR.teval_polyNil.
  by move=> ax px; rewrite PolR.tsize_polyCons.
have Hp: tsize p > 0 by rewrite Ep.
apply: contains_subset; first by exists (Xreal (PolR.tnth px 0)); apply: Hnth.
case.
- move/contains_Xnan => Hnan.
  suff->: (I.convert (ComputeBound prec p X)) = IInan by [].
  admit. (* FIXME *)
move=> a0 Ha0.
red in Hnth.
have Hcommon : Link.contains_pointwise p (PolR.tset_nth px 0 a0).
  split.
    rewrite PolR.tsize_set_nth.
    rewrite -(prednK Hp) in Hsiz *.
    by rewrite -Hsiz maxnSS max0n.
  move=> [|k] Hk.
    by rewrite PolR.tnth_set_nth eqxx.
  rewrite PolR.tnth_set_nth /=.
  exact: Hnth.
suff->: a0 = PolR.teval tt (PolR.tset_nth px 0 a0) R0.
  (* exact: ComputeBound_correct. *) admit.
have Hsiz' := prednK Hp.
rewrite PolR.is_horner /=.
rewrite PolR.tsize_set_nth -Hsiz -Hsiz' maxnSS max0n.
rewrite big_ord_recl /=.
rewrite PolR.tnth_set_nth eqxx Rmult_1_r.
rewrite Hsiz.
clear.
admit. (* FIXME *)
(*
rewrite big1 ?Rplus_0_r//.
move=> i _.
rewrite PolR.tnth_set_nth /bump /= SuccNat2Pos.id_succ /= Rmult_0_l.
case Ex: PolR.tnth =>[|x]; last by simpl; f_equal; ring.
exfalso; move: Hreal.
by rewrite (bigD1 i) //= PolR.tnth_set_nth /bump /= Ex XaddC.
*)
Qed.

End PolyBoundThm.

(** Naive implementation: Horner evaluation *)

Module PolyBoundHorner
  (I : IntervalOps)
  (Import Pol : IntMonomPolyOps I)
  (PolR : (*FIXME/Exact*)MonomPolyOps FullR)
  (Link : LinkIntR I Pol PolR)
  <: PolyBound I Pol PolR Link.

Module Import Aux := IntervalAux I.

Definition ComputeBound : Pol.U -> Pol.T -> I.type -> I.type :=
  Pol.teval.

Theorem ComputeBound_correct u fi fx :
  Link.contains_pointwise fi fx ->
  R_extension (PolR.teval tt fx) (ComputeBound u fi).
Proof.
move=> Hfifx X x Hx; rewrite /ComputeBound.
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
Qed.

Lemma ComputeBound_propagate u p : I_propagate (ComputeBound u p).
Proof.
move=> x; rewrite /ComputeBound.
elim/tpoly_ind: p.
  rewrite teval_polyNil.
  apply: (I.mask_correct I.zero x (Xreal 0) Xnan).
  by rewrite I.zero_correct; red; auto with real.
move=> a p H H'.
move/(_ H')/contains_Xnan in H; clear H'.
rewrite teval_polyCons.
admit. (* FIXME: not provable if a is an empty interval coeff *)
Qed.

End PolyBoundHorner.
