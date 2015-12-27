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
Require Import poly_bound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module PolyBoundHornerQuad (I : IntervalOps) (Pol : PolyIntOps I)
  <: PolyBound I Pol.

Module Import Bnd := PolyBoundHorner I Pol.

Module Import Aux := IntervalAux I.

(** FIXME: lemma copied from taylor_model_int_sharp.v *)
Lemma copy_Xdiv_0_r x : Xdiv x (Xreal 0) = Xnan.
Proof. by rewrite /Xdiv; case: x=>// r; rewrite zeroT. Qed.

(*
(** FIXME: lemma copied from taylor_model_int_sharp.v *)
Lemma copy_teval_contains u fi fx :
  Link.contains_pointwise fi fx ->
  R_extension (PolR.teval tt fx) (teval u fi).
Proof.
move=> Hfifx X x Hx.
elim/PolR.tpoly_ind: fx fi Hfifx => [|a b IH]; elim/tpoly_ind.
- rewrite PolR.teval_polyNil teval_polyNil.
  change (Xreal 0) with (Xmask (Xreal 0) (Xreal x)).
  by move=> *; apply: I.mask_correct =>//;
    rewrite I.zero_correct; split; auto with real.
- clear; move=> c p _ [K1 K2].
  by rewrite tsize_polyCons PolR.tsize_polyNil in K1.
- clear; move=> [K1 K2].
  by rewrite PolR.tsize_polyCons tsize_polyNil in K1.
move=> d p _ [K1 K2].
rewrite PolR.teval_polyCons teval_polyCons.
apply: R_add_correct =>//.
  apply: R_mul_correct =>//.
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
*)

Definition ComputeBound (prec : Pol.U) (pol : Pol.T) (x : I.type) : I.type :=
  if 3 <= Pol.size pol then
    let a := Pol.nth pol in
    let a2t2 := I.add prec (a 2) (a 2) in
    let a2t4 := I.add prec a2t2 a2t2 in
    let b1 := I.div prec (a 1) a2t2 in
    let b2 := I.div prec (I.sqr prec (a 1)) a2t4 in
    if (* I.bounded b1 && *) I.bounded b2 then
      I.add prec
            (I.add prec (I.sub prec (a 0) b2)
                   (I.mul prec (a 2) (I.sqr prec (I.add prec x b1))))
            (I.mul prec (I.power_int prec x 3)
                   (Pol.horner prec (Pol.tail 3 pol) x))
    else Pol.horner prec pol x
  else Pol.horner prec pol x.

Import Pol.Notations. Local Open Scope ipoly_scope.

Theorem ComputeBound_correct prec pi p :
  pi >:: p ->
  R_extension (PolR.horner tt p) (ComputeBound prec pi).
Proof.
move=> Hnth X x Hx; rewrite /ComputeBound.
case E: (2 < Pol.size pi); last by apply: Bnd.ComputeBound_correct.
case Eb: I.bounded; last by apply: Bnd.ComputeBound_correct.
(* case Eb': I.bounded; last by apply: Bnd.ComputeBound_correct. *)
simpl.
set A0 := Pol.nth pi 0.
set A1 := Pol.nth pi 1.
set A2 := Pol.nth pi 2.
set Q3 := Pol.tail 3 pi.
pose a0 := PolR.nth p 0.
pose a1 := PolR.nth p 1.
pose a2 := PolR.nth p 2.
pose q3 := PolR.tail 3 p.
have Hi3: Pol.size pi = 3 + (Pol.size pi - 3) by rewrite subnKC //.
(* have Hx3: PolR.size p = 3 + (PolR.size p - 3) by rewrite -Hsiz -Hi3. *)
suff->: PolR.horner tt p x =
  (Rplus (Rplus (Rminus a0 (Rdiv (Rsqr a1) (Rplus (Rplus a2 a2) (Rplus a2 a2))))
              (Rmult a2 (Rsqr (Rplus x (Rdiv a1 (Rplus a2 a2))))))
        (Rmult (powerRZ x 3) (PolR.horner tt q3 x))).
have Hnth3 : Q3 >:: q3 by apply(*:*) Pol.tail_correct.
apply: R_add_correct;
  [apply: R_add_correct;
    [apply: R_sub_correct;
      [apply: Hnth
      |apply: R_div_correct;
        [apply: R_sqr_correct; apply: Hnth
        |apply: R_add_correct; apply: R_add_correct; apply: Hnth]]
    |apply: R_mul_correct;
      [apply: Hnth
      |apply: R_sqr_correct; apply: R_add_correct;
       [done
       |apply: R_div_correct;
         [apply: Hnth|apply: R_add_correct; apply: Hnth ]]]]
  |apply: R_mul_correct;
    [exact: R_power_int_correct|exact: Pol.horner_correct]].
rewrite 2!PolR.hornerE.
rewrite (@big_nat_leq_idx _ _ _ (3 + (PolR.size p - 3))).
rewrite big_mkord.
rewrite 3?big_ord_recl -/a0 -/a1 -/a2 ![Radd_monoid _]/= /q3 PolR.size_tail.
(* simpl Z.of_nat. *)
set x0 := powerRZ x 0.
set x1 := powerRZ x 1.
set x2 := powerRZ x 2.
set x3 := powerRZ x 3.
set s1 := bigop _ _ _.
set s2 := bigop _ _ _.
have H4 : (a2 + a2 + (a2 + a2))%Re <> 0%Re.
  intro K.
  move: Eb.
  have Hzero : contains (I.convert
    (I.add prec (I.add prec (Pol.nth pi 2) (Pol.nth pi 2))
      (I.add prec (Pol.nth pi 2) (Pol.nth pi 2)))) (Xreal 0).
    rewrite -K.
    change (Xreal _) with (Xadd (Xadd (Xreal a2) (Xreal a2))
      (Xadd (Xreal a2) (Xreal a2))).
    by apply: R_add_correct; apply: R_add_correct; apply: Hnth.
  case/(I.bounded_correct _) => _.
  case/(I.upper_bounded_correct _) => _.
  rewrite /I.bounded_prop.
  set d := I.div prec _ _.
  suff->: I.convert d = IInan by [].
  apply -> contains_Xnan.
  rewrite -(copy_Xdiv_0_r (Xsqr (Xreal a1))).
  apply: I.div_correct =>//.
  apply: I.sqr_correct.
  by apply: Hnth; rewrite Hi3.
have H2 : (a2 + a2)%Re <> 0%Re by intro K; rewrite K Rplus_0_r in H4.
suff->: s1 = Rmult x3 s2.
  have->: Rmult a0 x0 = a0 by simpl; rewrite /x0 powerRZ_O Rmult_1_r.
  rewrite -!Rplus_assoc /Rminus; congr Rplus.
  rewrite /Rsqr /x1 /x2; change 1%Z with (Z.of_nat 1); change 2%Z with (Z.of_nat 2).
  rewrite /FullR.pow /=; field.
  split =>//.
by rewrite -Rplus_assoc in H4.
rewrite /s1 /s2 /x3; clear.
rewrite Rmult_comm.
rewrite big_mkord big_distrl.
apply: eq_bigr=> i _.
(* rewrite PolR.nth_tail. *) rewrite /PolR.tail /PolR.nth nth_drop.
(* some bookkeeping about powers *)
change 3%Z with (Z.of_nat 3); rewrite -!pow_powerRZ.
rewrite /= !Rmult_assoc; f_equal; ring.
by rewrite addnC leq_subnK.
move=> i /andP [Hi _].
by rewrite PolR.nth_default ?Rmult_0_l.
Qed.

Arguments ComputeBound_correct [prec pi p] _ b x _.

Lemma ComputeBound_propagate :
  forall prec pi p,
  pi >:: p ->
  I.propagate (ComputeBound prec pi).
Proof.
red=> *; rewrite /ComputeBound /=.
by repeat match goal with [|- context [if ?b then _ else _]] => destruct b end;
  rewrite !(I.add_propagate_r,I.mul_propagate_l,I.power_int_propagate,
            Pol.horner_propagate).
Qed.

Arguments ComputeBound_propagate [prec pi p] _ xi _.

End PolyBoundHornerQuad.
