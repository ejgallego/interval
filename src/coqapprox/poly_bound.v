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
  (PolX : ExactMonomPolyOps FullXR)
  (Link : LinkIntX I Pol PolX).

Parameter ComputeBound : Pol.U -> Pol.T -> I.type -> I.type.

Parameter ComputeBound_correct : forall u p px,
  Link.contains_pointwise p px ->
  I.extension (PolX.teval tt px) (ComputeBound u p).

End PolyBound.

Module PolyBoundThm
  (I : IntervalOps)
  (Import Pol : IntMonomPolyOps I)
  (PolX : ExactMonomPolyOps FullXR)
  (Link : LinkIntX I Pol PolX)
  (Import Bnd : PolyBound I Pol PolX Link).

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
  suff->: Xreal 0 = PolX.teval tt px (Xreal 0) by exact: ComputeBound_correct.
  have {p Hsiz Hnth Ep} Epx : PolX.tsize px = 0 by rewrite -Hsiz.
  elim/PolX.tpoly_ind: px Epx; first by rewrite PolX.teval_polyNil.
  by move=> ax px; rewrite PolX.tsize_polyCons.
have Hp: tsize p > 0 by rewrite Ep.
apply: contains_subset; first by exists (PolX.tnth px 0); apply: Hnth.
move=> a0 Ha0.
red in Hnth.
have Hcommon : Link.contains_pointwise p (PolX.tset_nth px 0 a0).
  split.
    rewrite PolX.tsize_set_nth.
    rewrite -(prednK Hp) in Hsiz *.
    by rewrite -Hsiz maxnSS max0n.
  move=> [|k] Hk.
    by rewrite PolX.tnth_set_nth eqxx.
  rewrite PolX.tnth_set_nth /=.
  exact: Hnth.
case E: (PolX.teval tt (PolX.tset_nth px 0 a0) (Xreal 0)) =>[|r].
  suff->: (I.convert (ComputeBound prec p X)) = IInan by [].
  apply: contains_Xnan.
  rewrite -E.
  exact: ComputeBound_correct.
suff->: a0 = PolX.teval tt (PolX.tset_nth px 0 a0) (Xreal 0).
  exact: ComputeBound_correct.
clear - E Hp Hsiz.
have Hsiz' := prednK Hp.
move: E; rewrite PolX.is_horner /=.
  rewrite PolX.tsize_set_nth -Hsiz -Hsiz' maxnSS max0n.
rewrite big_ord_recl /=.
rewrite PolX.tnth_set_nth eqxx Xmul_1_r.
rewrite Hsiz.
clear; move=> Hreal.
rewrite big1 ?Xadd_0_r//.
move=> i _.
rewrite PolX.tnth_set_nth /bump /= SuccNat2Pos.id_succ /= Rmult_0_l.
case Ex: PolX.tnth =>[|x]; last by simpl; f_equal; ring.
exfalso; move: Hreal.
by rewrite (bigD1 i) //= PolX.tnth_set_nth /bump /= Ex XaddC.
Qed.

End PolyBoundThm.

(** Naive implementation: Horner evaluation *)

Module PolyBoundHorner
  (I : IntervalOps)
  (Import Pol : IntMonomPolyOps I)
  (PolX : ExactMonomPolyOps FullXR)
  (Link : LinkIntX I Pol PolX)
  <: PolyBound I Pol PolX Link.

Module Import Aux := IntervalAux I.

Definition ComputeBound : Pol.U -> Pol.T -> I.type -> I.type :=
  Pol.teval.

Theorem ComputeBound_correct u fi fx :
  Link.contains_pointwise fi fx ->
  I.extension (PolX.teval tt fx) (ComputeBound u fi).
Proof.
move=> Hfifx X x Hx; rewrite /ComputeBound.
elim/PolX.tpoly_ind: fx fi Hfifx => [|a b IH]; elim/tpoly_ind.
- rewrite PolX.teval_polyNil teval_polyNil.
  by move=> *; apply: I.mask_correct =>//;
    rewrite I.zero_correct; split; auto with real.
- clear; move=> c p _ [K1 K2].
  by rewrite tsize_polyCons PolX.tsize_polyNil in K1.
- clear; move=> [K1 K2].
  by rewrite PolX.tsize_polyCons tsize_polyNil in K1.
move=> d p _ [K1 K2].
rewrite PolX.teval_polyCons teval_polyCons.
apply: I.add_correct =>//.
  apply: I.mul_correct =>//.
  apply: IH.
  rewrite tsize_polyCons in K2.
  split.
    rewrite tsize_polyCons PolX.tsize_polyCons in K1.
    by case: K1.
  move=> k Hk.
  move/(_ k.+1 Hk) in K2.
  rewrite PolX.tnth_polyCons ?tnth_polyCons // in K2.
  rewrite tsize_polyCons PolX.tsize_polyCons in K1.
  by case: K1 =><-.
rewrite tsize_polyCons in K2.
move/(_ 0 erefl) in K2.
by rewrite tnth_polyCons ?PolX.tnth_polyCons in K2.
Qed.

End PolyBoundHorner.
