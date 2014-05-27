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
Require Import Fcore_Raux.
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
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
Require Import xreal_ssr_compat.
Require Import seq_compl.
Require Import interval_compl.
Require Import poly_datatypes.
Require Import taylor_poly.
Require Import coeff_inst.
Require Import rpa_inst.
Require Import derive_compl.
Require Import basic_rec.
Require Import poly_bound.

Module PolyBoundHornerQuad
  (I : IntervalOps)
  (Import Pol : IntMonomPolyOps I)
  (PolX : ExactMonomPolyOps FullXR)
  (Link : LinkIntX I Pol PolX)
  <: PolyBound I Pol PolX Link.

Module Import Bnd := PolyBoundHorner I Pol PolX Link.

(** FIXME: lemma copied from taylor_model_int_sharp.v *)
Lemma copy_Xdiv_0_r x : Xdiv x (Xreal 0) = Xnan.
Proof. by rewrite /Xdiv; case: x=>// r; rewrite zeroT. Qed.

(** FIXME: lemma copied from taylor_model_int_sharp.v *)
Lemma copy_teval_contains u fi fx (X : I.type) x :
  Link.contains_pointwise fi fx ->
  contains (I.convert X) x ->
  contains (I.convert (teval u fi X)) (PolX.teval tt fx x).
Proof.
move=> Hfifx Hx.
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

Definition ComputeBound (prec : Pol.U) (pol : Pol.T) (x : I.type) : I.type :=
  if 3 <= Pol.tsize pol then
    let a := Pol.tnth pol in
    let a2t2 := I.add prec (a 2) (a 2) in
    let a2t4 := I.add prec a2t2 a2t2 in
    let b1 := I.div prec (a 1) a2t2 in
    let b2 := I.div prec (I.sqr prec (a 1)) a2t4 in
    if (* I.bounded b1 && *) I.bounded b2 then
      I.add prec
            (I.add prec (I.sub prec (a 0) b2)
                   (I.mul prec (a 2) (I.sqr prec (I.add prec x b1))))
            (I.mul prec (I.power_int prec x 3)
                   (Pol.teval prec (Pol.ttail 3 pol) x))
    else Pol.teval prec pol x
  else Pol.teval prec pol x.

Theorem ComputeBound_correct u pi px :
  Link.contains_pointwise pi px ->
  I.extension (PolX.teval tt px) (ComputeBound u pi).
Proof.
move=> [Hsiz Hnth] X x Hx; rewrite /ComputeBound.
case E: (2 < tsize pi); last by apply: Bnd.ComputeBound_correct.
case Eb: I.bounded; last by apply: Bnd.ComputeBound_correct.
(* case Eb': I.bounded; last by apply: Bnd.ComputeBound_correct. *)
simpl.
set A0 := tnth pi 0.
set A1 := tnth pi 1.
set A2 := tnth pi 2.
set Q3 := ttail 3 pi.
pose a0 := PolX.tnth px 0.
pose a1 := PolX.tnth px 1.
pose a2 := PolX.tnth px 2.
pose q3 := PolX.ttail 3 px.
have Hi3: tsize pi = 3 + (tsize pi - 3) by rewrite subnKC //.
have Hx3: PolX.tsize px = 3 + (PolX.tsize px - 3) by rewrite -Hsiz -Hi3.
suff->: PolX.teval tt px x =
  (Xadd (Xadd (Xsub a0 (Xdiv (Xsqr a1) (Xadd (Xadd a2 a2) (Xadd a2 a2))))
              (Xmul a2 (Xsqr (Xadd x (Xdiv a1 (Xadd a2 a2))))))
        (Xmul (Xpower_int x 3) (PolX.teval tt q3 x))).
have Hnth3 : Link.contains_pointwise Q3 q3.
  split; first by rewrite PolX.tsize_tail tsize_tail Hsiz.
  move=> k Hk; rewrite tsize_tail in Hk.
  rewrite tnth_tail PolX.tnth_tail; apply: Hnth.
  by rewrite -ltn_subRL.
apply: I.add_correct;
  [apply: I.add_correct;
    [apply: I.sub_correct;
      [apply: Hnth
      |apply: I.div_correct;
        [apply: I.sqr_correct; apply: Hnth
        |apply: I.add_correct; apply: I.add_correct; apply: Hnth]]
    |apply: I.mul_correct;
      [apply: Hnth
      |apply: I.sqr_correct; apply: I.add_correct;
       [done
       |apply: I.div_correct;
         [apply: Hnth|apply: I.add_correct; apply: Hnth ]]]]
  |apply: I.mul_correct;
    [exact: I.power_int_correct|exact:copy_teval_contains]];
  by rewrite Hi3 //.
rewrite 2!PolX.is_horner Hx3.
rewrite 3!big_ord_recl -/a0 -/a1 -/a2 /= PolX.tsize_tail.
case: x Hx => [|x] Hx; first by rewrite XmulC [in RHS]XaddC.
case E0: a0 =>[|r0]; case E1: a1 =>[|r1]; case E2: a2 =>[|r2] //.
set x0 := Xpower_int _ 0.
set x1 := Xpower_int _ 1.
set x2 := Xpower_int _ 2.
set x3 := Xpower_int _ 3.
set s1 := bigop _ _ _.
set s2 := bigop _ _ _.
have H4 : (r2 + (r2 + (r2 + r2)))%Re <> 0%Re.
  intro K.
  rewrite -Rplus_assoc in K.
  move: Eb.
  have Hzero : contains (I.convert
    (I.add u (I.add u (tnth pi 2) (tnth pi 2))
      (I.add u (tnth pi 2) (tnth pi 2)))) (Xreal 0).
    rewrite -K.
    change (Xreal _) with (Xadd (Xadd (Xreal r2) (Xreal r2))
      (Xadd (Xreal r2) (Xreal r2))).
    by apply: I.add_correct; apply: I.add_correct; rewrite -E2; apply: Hnth.
  case/(I.bounded_correct _) => _.
  case/(I.upper_bounded_correct _) => _.
  rewrite /I.bounded_prop.
  set d := I.div u _ _.
  suff->: I.convert d = IInan by [].
  apply: contains_Xnan.
  rewrite -(copy_Xdiv_0_r (Xsqr a1)).
  apply: I.div_correct =>//.
  apply: I.sqr_correct.
  by apply: Hnth; rewrite Hi3.
have H2 : (r2 + r2)%Re <> 0%Re by intro K; rewrite K Rplus_0_r K in H4.
suff->: s1 = Xmul x3 s2.
  have->: Xmul (Xreal r0) x0 = Xreal r0 by simpl; congr Xreal; ring.
  rewrite Xsub_split -!XaddA; congr Xadd.
  simpl.
  case: s2 =>[|s2]; first by rewrite !XaddA [RHS]XaddC.
  by rewrite !zeroF /=; first (congr Xreal; field).
rewrite /s1 /s2 /x3; clear.
rewrite [Xpower_int _ 3]/= XmulC.
rewrite big_Xmul_Xadd_distr.
apply: eq_bigr=> i _.
rewrite PolX.tnth_tail.
(* some bookkeeping about powers *)
rewrite -!XmulA; congr Xmul.
rewrite -!SuccNat2Pos.inj_succ.
rewrite Pos.of_nat_succ.
rewrite -positive_nat_Z.
rewrite Nat2Pos.id //.
(* Check Xpow_idem. *)
have L := FullXR.tpow_S (Xreal x); rewrite /FullXR.tpow in L.
rewrite XmulC !L /FullXR.tmul !XmulA; congr Xmul.
by rewrite /= Rmult_1_r Rmult_assoc.
Qed.

End PolyBoundHornerQuad.
