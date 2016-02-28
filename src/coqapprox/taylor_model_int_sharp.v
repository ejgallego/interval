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

Require Import ZArith Psatz reals_tac reals_compl.
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
Require Import Rstruct Coquelicot.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.bigop.
Require Import xreal_ssr_compat.
Require Import seq_compl.
Require Import interval_compl.
Require Import poly_datatypes.
Require Import taylor_poly.
Require Import derive_compl.
Require Import basic_rec.
Require Import poly_bound.
Require Import coquelicot_compl integral_pol.

(********************************************************************)
(** This theory implements Taylor Models, with sharp remainders for
univariate base functions, using the so-called Zumkeller's technique
which is partly based on the standard enclosure of the Taylor/Lagrange
remainder. *)
(********************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.

(** Rigorous Polynomial Approximation structure *)
Record rpa {pol int : Type} : Type := RPA { approx : pol ; error : int }.

Module TaylorModel (I : IntervalOps) (Pol : PolyIntOps I) (Bnd : PolyBound I Pol).
Import Pol.Notations.
Import PolR.Notations.
Local Open Scope ipoly_scope.
Module Export Aux := IntervalAux I.
Module Import TI := TaylorPoly Pol.Int Pol.
Module TR := TaylorPoly FullR PolR.
Module Import BndThm := PolyBoundThm I Pol Bnd.

Local Notation Ibnd2 x := (I.bnd x x) (only parsing).

(* Module Bnd0 := PolyBoundHorner I Pol PolX Link.
Module Bnd0Thm := PolyBoundThm I Pol PolX Link Bnd. *)

(*
Eval compute in contains (Interval_interval.Ibnd (Xreal 0) (Xreal 0)) (Xreal 0).
Eval compute in contains (Interval_interval.Ibnd (Xreal 0) (Xreal 0)) Xnan.
Eval compute in contains (Interval_interval.Ibnd Xnan Xnan) (Xreal 0).
Eval compute in contains (Interval_interval.Ibnd Xnan Xnan) Xnan.
Eval compute in contains Interval_interval.Inan (Xreal 0).
Eval compute in contains Interval_interval.Inan Xnan.
*)

(* POSSIBLE UTF-8 NOTATION
Notation "X ∋ x" := (contains X x) (at level 70).
Notation "X ⊂ Y" := (I.subset_ X Y) (at level 70).
*)

Ltac tac_def1 f := rewrite /defined; case: (f).
Ltac tac_def2 f g := rewrite /defined; case: (f); case: (g).

Ltac step_xr xr :=
  match goal with
  [ |- contains ?i ?g ] => rewrite -(_ : xr = g)
  end.
Ltac step_r r :=
  match goal with
  [ |- contains ?i (Xreal ?g) ] => rewrite -(_ : r = g)
  end.
Ltac step_xi xi :=
  match goal with
  [ |- contains ?g ?xr ] => rewrite -(_ : xi = g)
  end.
Ltac step_i i :=
  match goal with
  [ |- contains (I.convert ?g) ?xr ] => rewrite -(_ : i = g)
  end.

(* Erik: Some lemmas could be generalized from [I.type] to [interval]. *)

Notation rpa := (@rpa Pol.T I.type).

Section TaylorModel.
(** The presence of this section variable does not hinder any
    sophisticated handling of the precision inside the functions
    that are defined or called below. *)
Variable prec : I.precision.
Variable M : rpa.

Variable Tcoeffs : I.type -> nat -> Pol.T.
(** For complexity reasons, [Tcoeffs] must return more than one coefficient. *)

(** The generic functions [TLrem]/[Ztech] are intended to ease the computation
    of the interval remainder for basic functions. *)
Definition TLrem X0 X n :=
  let N := S n in
  let NthCoeff := Pol.nth (Tcoeffs X N) N in
  let NthPower :=
    I.power_int prec (I.sub prec X X0) (Z_of_nat N) (* improvable *) in
  I.mul prec NthCoeff NthPower.

(** The first argument of [Ztech] will be instantiated with [Tcoeffs X0 n]. *)
Definition Ztech (P : Pol.T) F X0 X n :=
  let N := S n in
  let NthCoeff := Pol.nth (Tcoeffs X N) N in
  if isNNegOrNPos NthCoeff && I.bounded X then
    let a := I.lower X in let b := I.upper X in
    let A := I.bnd a a in let B := I.bnd b b in
    (* If need be, we could replace Pol.horner with Bnd.ComputeBound *)
    let Da := I.sub prec (F A) (Pol.horner prec P (I.sub prec A X0)) in
    let Db := I.sub prec (F B) (Pol.horner prec P (I.sub prec B X0)) in
    let Dx0 := I.sub prec (F X0) (Pol.nth P 0) (* :-D *) in
    I.join (I.join Da Db) Dx0
  else
    let NthPower :=
      I.power_int prec (I.sub prec X X0) (Z_of_nat N) in
    I.mul prec NthCoeff NthPower.

Lemma ZtechE1 P F X0 X n :
  isNNegOrNPos (Pol.nth (Tcoeffs X n.+1) n.+1) = false ->
  Ztech P F X0 X n = TLrem X0 X n.
Proof. by rewrite /Ztech =>->. Qed.

Lemma ZtechE2 P F X0 X n :
  I.bounded X = false ->
  Ztech P F X0 X n = TLrem X0 X n.
Proof. by rewrite /Ztech andbC =>->. Qed.

End TaylorModel.

Section PrecArgument.
(** The presence of this section variable does not hinder any
    sophisticated handling of the precision inside the functions
    that are defined or called below. *)
Variable prec : I.precision.

(** Note that Zumkeller's technique is not necessary for [TM_cst] & [TM_var]. *)
Definition TM_cst c : rpa :=
  RPA (Pol.polyC c) (I.mask I.zero c).

Definition TM_var X0 :=
  RPA (Pol.set_nth Pol.polyX 0 X0) I.zero.

Definition TM_power_int (p : Z) X0 X (n : nat) :=
  let P := (T_power_int prec p X0 n) in RPA P
  (Ztech prec (T_power_int prec p) P (fun x => I.power_int prec x p) X0 X n).

Definition TM_inv X0 X (n : nat) :=
  let P := (T_inv prec X0 n) in
  (** Note that this let-in is essential in call-by-value context. *)
  RPA P (Ztech prec (T_inv prec) P (I.inv prec) X0 X n).

Definition TM_exp X0 X (n : nat) : rpa :=
  let P := (T_exp prec X0 n) in
  RPA P (Ztech prec (T_exp prec) P (I.exp prec) X0 X n).

Definition TM_ln X0 X (n : nat) : rpa :=
  let P := (T_ln prec X0 n) in
  RPA P (Ztech prec (T_ln prec) P (I.ln prec) X0 X n).

Definition TM_sqrt X0 X (n : nat) : rpa :=
  let P := (T_sqrt prec X0 n) in
  RPA P (Ztech prec (T_sqrt prec) P (I.sqrt prec) X0 X n).

Definition I_invsqrt prec x := I.inv prec (I.sqrt prec x).

Definition TM_invsqrt X0 X (n : nat) : rpa :=
  let P := (T_invsqrt prec X0 n) in
  RPA P (Ztech prec (T_invsqrt prec) P (I_invsqrt prec) X0 X n).

Definition TM_sin X0 X (n : nat) : rpa :=
  let P := (T_sin prec X0 n) in
  RPA P (Ztech prec (T_sin prec) P (I.sin prec) X0 X n).

Definition TM_cos X0 X (n : nat) : rpa :=
  let P := (T_cos prec X0 n) in
  RPA P (Ztech prec (T_cos prec) P (I.cos prec) X0 X n).

Definition TM_tan X0 X (n : nat) : rpa :=
  let P := (T_tan prec X0 n) in
  RPA P (Ztech prec (T_tan prec) P (I.tan prec) X0 X n).

Definition TM_atan X0 X (n : nat) : rpa :=
  let P := (T_atan prec X0 n) in
  RPA P (Ztech prec (T_atan prec) P (I.atan prec) X0 X n).

Definition TM_add (Mf Mg : rpa) : rpa :=
  RPA (Pol.add prec (approx Mf) (approx Mg))
    (I.add prec (error Mf) (error Mg)).

Definition TM_opp (M : rpa) : rpa :=
  RPA (Pol.opp (approx M)) (I.neg (error M)).

Definition TM_sub (Mf Mg : rpa) : rpa :=
  RPA (Pol.sub prec (approx Mf) (approx Mg))
      (I.sub prec (error Mf) (error Mg)).

Definition i_validTM (X0 X : interval (* not I.type *) )
  (M : rpa) (xf : ExtendedR -> ExtendedR) :=
  [/\ forall x : R, contains X (Xreal x) -> ~~ defined xf x -> eqNai (error M),
    contains (I.convert (error M)) (Xreal 0),
    I.subset_ X0 X &
    forall x0, contains X0 (Xreal x0) ->
    exists2 Q, approx M >:: Q
    & forall x, contains X (Xreal x) ->
      error M >: toR_fun xf x - (PolR.horner tt Q (x - x0))%R].
(** Otherwise, we could replace [toR_fun xf x] with [proj_val (xf (Xreal x))] *)

Definition restriction (dom : R -> bool) (xf : ExtendedR -> ExtendedR) (x : ExtendedR) :=
  match x, xf x with
  | Xnan, _ | _, Xnan => Xnan
  | Xreal x, Xreal y => if dom x then Xreal y else Xnan
  end.

Lemma defined_restrictionW dom xf x :
  defined (restriction dom xf) x -> defined xf x.
Proof. by rewrite /defined /=; case: xf. Qed.

Lemma defined_restriction dom xf x :
  defined (restriction dom xf) x = defined xf x && dom x.
Proof. by rewrite /defined /=; case: xf =>//; case: dom. Qed.

Lemma Xreal_toR_restr (dom : R -> bool) xf x :
  defined xf x -> dom x -> Xreal (toR_fun (restriction dom xf) x) = xf (Xreal x).
Proof.
move=> H H'; rewrite Xreal_toR; last by rewrite defined_restriction; apply/andP.
by rewrite /restriction H'; tac_def1 xf.
Qed.

Lemma toR_restr_toXreal (dom : R -> bool) f x :
  toR_fun (restriction dom (toXreal_fun f)) x =
  if dom x then f x else (* dummy *) some_real.
Proof.
rewrite /toR_fun /restriction /proj_fun /=.
by case Dx : (dom x).
Qed.

Lemma TM_fun_eq f g X0 X TMf :
  (forall x, contains X (Xreal x) -> f (Xreal x) = g (Xreal x)) ->
  i_validTM X0 X TMf f -> i_validTM X0 X TMf g.
Proof.
move=> Hfg [Hdom H0 Hsubs Hmain].
split=>//.
  move=> x Hx Dx.
  apply: (Hdom x) =>//.
  rewrite (@defined_ext g f x _) ?Hfg //.
move=> x0 Hx0.
have Hx0' : contains X (Xreal x0) by exact: subset_contains Hsubs _ _.
move/(_ x0 Hx0) in Hmain.
have [Q HQ Hf] := Hmain.
exists Q =>//.
move=> x Hx.
case K: (eqNai (error TMf)); first by move/eqNaiP: K =>->.
move/negbT in K.
have Df: defined f x by move: (Hdom x Hx) K; tac_def2 f eqNai.
move/(_ x Hx) in Hfg.
move/(_ x Hx) in Hf.
rewrite Xreal_sub Xreal_toR // -?Hfg // -?[f _]Xreal_toR //.
by rewrite (@defined_ext f) ?Hfg.
Qed.

(** This simple result will be useful to prove the correctness of [TM_comp]. *)

Lemma i_validTM_subset_X0 (X0 : I.type) (SX0 : interval) (X : I.type) f Mf :
  I.subset_ SX0 (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  i_validTM (SX0) (I.convert X) Mf f.
Proof.
red.
move=> HSX0 [Hdef Hf0 Hsubs Hmain].
split=>//; first exact: (subset_subset SX0 (I.convert X0)).
move=> x0 Hx0.
move/(_ x0 (subset_contains _ _ HSX0 _ Hx0)): Hmain.
by case: (defined f x0).
Qed.

Definition ComputeBound (M : rpa) (X0 X : I.type) :=
  I.add prec (Bnd.ComputeBound prec (approx M) (I.sub prec X X0)) (error M).

(* FIXME: still used?

Theorem ComputeBound_correct M (X0 X : I.type) f :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  forall x, contains (I.convert X) x ->
  contains (I.convert (ComputeBound M X0 X)) (f x).
Proof.
move/not_empty'E => [x0 Hx0] [/= Hzero Hsubs Hmain] x Hx.
have [q [Hsize Hcont Herr]] := Hmain _ Hx0.
rewrite /ComputeBound.
have := Herr x Hx.
case E : (PolR.horner tt q (Xsub x x0)) =>[|r].
  rewrite Xsub_Xnan_r.
  move/contains_Xnan => Herr'.
  have Haux :
    contains (I.convert (Bnd.ComputeBound prec (approx M) (I.sub prec X X0)))
      (PolR.horner tt q (Xsub x x0)).
  apply: Bnd.ComputeBound_correct =>//.
  exact: I.sub_correct.
  by rewrite (Iadd_Inan_propagate_r _ Haux).
move=> Hr.
have->: f x =
  Xadd (PolR.horner tt q (Xsub x x0))
  (Xsub (f x) (PolR.horner tt q (Xsub x x0))).
  rewrite E /=.
  by case: (f) =>[//|y]; simpl; congr Xreal; auto with real.
apply: I.add_correct.
  apply: Bnd.ComputeBound_correct.
    now split. (* TODO: Improve? *)
  exact: I.sub_correct.
exact: Herr.
Qed.
*)

Section TM_integral.

Local Notation Isub := (I.sub prec).
Local Notation Imul := (I.mul prec).
Local Notation Iadd := (I.add prec).

Variables (X0 X : I.type).
Variable xF : ExtendedR -> ExtendedR. Let f := toR_fun xF.
Let iX0 := I.convert X0.
Let iX := I.convert X.
(* Hypothesis extF : extension f1 f. *) (* to correct *)

Hypothesis f_int : forall x x0 : R,
  contains iX (Xreal x) -> contains iX0 (Xreal x0) ->
  ex_RInt f x0 x.
Hypothesis x_Def : forall x : R, contains iX (Xreal x) -> defined xF x.
Variable Mf : rpa.

(* here we define a function which takes a Taylor Model for f
and returns a Taylor model for the primitive of f which evaluates to
*)

Definition TM_integral_poly :=
  Pol.primitive prec (I.zero) (approx Mf).

Definition TM_integral_error R :=
  Iadd (Imul (Isub X X0) (error Mf)) ((Iadd (Bnd.ComputeBound (*Pol.horner?*) prec R (Isub X0 X0)))
    (Imul (Isub X0 X0) (error Mf))).

Section Extra_RInt.

Local Open Scope R_scope.
Lemma RInt_translation_add g a b x :
  RInt (fun y : R => g (y + x)%R) a b = RInt g (a + x) (b + x).
Proof.
have -> : a + x = (1 * a + x) by ring.
have -> : b + x = (1 * b + x) by ring.
rewrite -RInt_comp_lin.
by apply: RInt_ext => x0 _; rewrite Rmult_1_l; congr (g _); ring.
Qed.

Lemma RInt_translation_sub g x a b :
  RInt (fun y : R => g (y - x)) a b = RInt g (a - x) (b - x).
Proof.
have -> : a - x = a + (-x) by ring.
have -> : b - x = b + (-x) by ring.
rewrite -RInt_translation_add.
apply: RInt_ext => x0 _; by congr (g _).
Qed.

Lemma ex_RInt_translation_add V g x a b :
  @ex_RInt V g a b -> @ex_RInt V (fun t => g (t + x)) (a - x) (b - x).
Proof.
move => Hgab.
apply: (ex_RInt_ext (fun t => scal 1 (g (1 * t + x)))) => [x0 _|].
have -> : 1 * x0 + x = x0 + x; first by ring.
by rewrite scal_one.
apply: ex_RInt_comp_lin.
have -> : (1 * (a - x) + x ) = a. by ring.
have -> : (1 * (b - x) + x ) = b. by ring.
by [].
Qed.

Lemma ex_RInt_translation_sub V g a b x :
  @ex_RInt V g a b -> @ex_RInt V (fun t => g (t - x)) (a + x) (b + x).
Proof.
move => Hgab.
apply: (ex_RInt_ext (fun t => scal 1 (g (1 * t - x)))) => [x0 _|].
have -> : 1 * x0 - x = x0 - x; first by ring.
by rewrite scal_one.
apply: ex_RInt_comp_lin.
have -> : (1 * (a + x) + -x ) = a. by ring.
have -> : (1 * (b + x) + -x ) = b. by ring.
by [].
Qed.

End Extra_RInt.


Section IntegralBounding.
Local Open Scope R_scope.
Lemma contains_RInt (f3 : R -> R) x1 x2 Y Z1 Z2 :
  (x1 < x2)%R ->
  ex_RInt f3 x1 x2->
  contains (I.convert Z1) (Xreal x1) ->
  contains (I.convert Z2) (Xreal x2) ->
  (forall x, (x1 <= x <= x2)%R -> contains (I.convert Y) (Xreal (f3 x))) ->
  contains (I.convert (Imul  (Isub Z2 Z1) Y)) (Xreal (RInt f3 x1 x2)).
Proof.
move => ltx1x2 Hf3_int HZx1 HZx2 Hext.
have -> : RInt f3 x1 x2 = (RInt f3 x1 x2) / (x2 - x1) * (x2 - x1).
by field => //; lra.
have -> : Xreal (RInt f3 x1 x2 / (x2 - x1) * (x2 - x1)) =
          Xmul (Xsub (Xreal x2) (Xreal x1)) (Xreal (RInt f3 x1 x2 / (x2 - x1) )) by rewrite /= Rmult_comm.
apply: I.mul_correct.
apply: I.sub_correct => // .
case: (I.convert Y) Hext => // l u Hext.
apply: le_contains.
rewrite /le_lower /le_upper /=.
case: l Hext => //= rl Hext.
case: u Hext => [Hext|].
apply: Ropp_le_contravar.
apply: RInt_le_l => //.
move => x Hx12.
by elim: (Hext x Hx12).
move => ru Hext.
apply: Ropp_le_contravar.
apply: RInt_le_l => //.
move => x Hx12.
by elim:  (Hext x Hx12).
rewrite /le_upper /=.
case: u Hext => // ru Hext.
apply: RInt_le_r => // x Hx12.
by elim: (Hext x Hx12).
Qed.

Lemma contains_RInt_gt (f3 : R -> R) x1 x2 Y Z1 Z2 :
  (x2 < x1) ->
  ex_RInt f3 x2 x1->
  contains (I.convert Z1) (Xreal x1) ->
  contains (I.convert Z2) (Xreal x2) ->
  (forall x, x2 <= x <= x1 -> contains (I.convert Y) (Xreal (f3 x))) ->
  contains (I.convert (Imul  (Isub Z2 Z1) Y)) (Xreal (RInt f3 x1 x2)).
Proof.
move => ltx1x2 Hf3_int HZx1 HZx2 Hext.
have -> : RInt f3 x1 x2 = (RInt f3 x1 x2) / (x2 - x1) * (x2 - x1).
by field => //; lra.
rewrite -RInt_swap.
have -> : Xreal (- RInt f3 x2 x1 / (x2 - x1) * (x2 - x1)) =
          Xmul (Xsub (Xreal x2) (Xreal x1)) (Xreal (RInt f3 x2 x1 / (x1 - x2) )).
  by rewrite /=; congr (Xreal); field; lra.
apply: I.mul_correct.
apply: I.sub_correct => // .
case: (I.convert Y) Hext => // l u Hext.
apply: le_contains.
rewrite /le_lower /le_upper /=.
case: l Hext => //= rl Hext.
case: u Hext => [Hext|].
apply: Ropp_le_contravar.
apply: RInt_le_l => //.
move => x Hx12.
by elim: (Hext x Hx12).
move => ru Hext.
apply: Ropp_le_contravar.
apply: RInt_le_l => //.
move => x Hx12.
by elim:  (Hext x Hx12).
rewrite /le_upper /=.
case: u Hext => // ru Hext.
apply: RInt_le_r => // x Hx12.
by elim: (Hext x Hx12).
Qed.

End IntegralBounding.


Local Open Scope R_scope.

Lemma contains_RInt_full (f3 : R -> R) x1 x2 Y Z1 Z2 :
  ex_RInt f3 x1 x2->
  contains (I.convert Z1) (Xreal x1) ->
  contains (I.convert Z2) (Xreal x2) ->
  (forall x, Rmin x1 x2 <= x <= Rmax x1 x2 -> contains (I.convert Y) (Xreal (f3 x))) ->
  contains (I.convert (Imul  (Isub Z2 Z1) Y)) (Xreal (RInt f3 x1 x2)).
Proof.
move => Hf3_int HZx1 HZx2 Hext.
case : (total_order_T x1 x2) => [[H12|Heq]|H21].
- apply: contains_RInt => // x H1x2; apply: Hext.
  by rewrite Rmin_lt // Rmax_lt //.
- rewrite Heq. rewrite RInt_point.
  apply: (@mul_0_contains_0_l _ (Xreal (f3 x1))).
  + apply: (Hext x1); split.
    * by rewrite Heq Rmin_refl; lra.
    * by rewrite Heq Rmax_refl; lra.
  + have -> :
    Xreal 0 = Xsub (Xreal x2) (Xreal x1) ; first by rewrite Heq /= Rminus_eq_0.
    by apply: I.sub_correct.
- apply: contains_RInt_gt => // .
    by apply: ex_RInt_swap.
  move => x H1x2; apply: Hext.
  rewrite Rmin_swap Rmin_lt; try lra.
  rewrite Rmax_swap Rmax_lt; try lra.
Qed.

Lemma pol_int_sub pol x1 x2 x3:  ex_RInt (fun y : R => PolR.horner tt pol (y - x3)) x1 x2.
Proof.
have -> : x1 = x1 - x3 + x3 by ring.
have -> : x2 = x2 - x3 + x3 by ring.
apply: ex_RInt_translation_sub.
exact: Rpol_integrable.
Qed.



(*the following section is now concerned with computing just one integral *)
(* from a to b, for the "interval" tactic *)
Section NumericIntegration.

Local Open Scope R_scope.

Variables (x0 a b : R) (ia ib : I.type).

Hypothesis Hx0 : contains iX0 (Xreal x0).
Hypothesis Ha : contains iX (Xreal a).
Hypothesis Hb : contains iX (Xreal b).
Hypothesis Hia : contains (I.convert ia) (Xreal a).
Hypothesis Hib : contains (I.convert ib) (Xreal b).
Hypothesis Hsubset: Interval_interval.subset iX0 iX.
Hypothesis f_int_numeric : ex_RInt f a b.


Hint Resolve Hia.
Hint Resolve Hib.

Definition polIntegral := Isub (Pol.horner prec TM_integral_poly (Isub ib X0)) (Pol.horner prec TM_integral_poly (Isub ia X0)).
Definition integralError := (Imul (Isub ib ia) (error Mf)).
Definition integralEnclosure := Iadd polIntegral integralError.

Lemma integralDifference p :
  ((RInt (fun x => (f x - PolR.horner tt p (x - x0))%R ) a b) =
   (RInt f a b) - (RInt (fun x => PolR.horner tt p (x - x0))%R ) a b)%R.
Proof.
rewrite RInt_minus.
- by [].
- exact: f_int_numeric.
- have -> : (a = a - x0 + x0)%R by ring.
  have -> : (b = b - x0 + x0)%R by ring.
  apply: ex_RInt_translation_sub.
  by apply: Rpol_integrable.
Qed.

Lemma integralDifference2 p :
  ((RInt f a b) =
   (RInt (fun x => PolR.horner tt p (x - x0))%R ) a b +
   (RInt (fun x => (f x - PolR.horner tt p (x - x0))%R ) a b))%R.
Proof.
by rewrite integralDifference; ring.
Qed.

Local Notation XRInt := (fun f a b => Xreal (RInt f a b)).

(*
With the new archi, this result is now given by Pol.primitive_correct:

Lemma primitive_contains P q :
P >:: q ->
Pol.primitive prec I.zero P >:: PolR.primitive tt 0 q.
Proof. by move=> ?; apply: Pol.primitive_correct =>//; apply: cont0. Qed.
*)

Lemma integralEnclosure_correct :
  i_validTM iX0 iX Mf xF ->
  contains (I.convert integralEnclosure) (XRInt f a b).
Proof.
move => [] Hdef Hcontains0 HX0X H.
have := (H x0 Hx0).
move => [] q HMfq Herror.
rewrite (integralDifference2 q).
rewrite Xreal_add; apply:I.add_correct.
- have -> :
    RInt (fun x : R => q.[x - x0]) a b =
    (PolR.primitive tt 0 q).[b - x0] - (PolR.primitive tt 0 q).[a - x0].
  by rewrite RInt_translation_sub Rpol_integral_0.
  rewrite Xreal_sub; apply: I.sub_correct.
  + apply: Pol.horner_correct.
    rewrite /TM_integral_poly.
    apply: Pol.primitive_correct =>//; exact: cont0.
    rewrite Xreal_sub.
    by apply: I.sub_correct => // .
  + apply: Pol.horner_correct.
    apply: Pol.primitive_correct =>//; exact: cont0.
    exact: (I.sub_correct _ _ _ (Xreal a) (Xreal x0)).
    rewrite /integralError.
    apply: contains_RInt_full => // .
- apply: ex_RInt_plus.
  + exact: f_int_numeric.
    apply: ex_RInt_opp.
    have -> : (a = a - x0 + x0)%R by ring.
    have -> : (b = b - x0 + x0)%R by ring.
    apply: ex_RInt_translation_sub => // .
    by apply: Rpol_integrable.
  + move => x Hx.
    apply: Herror.
    have [Hab|Hba] := Rle_dec a b.
      apply: contains_intvl_trans Ha Hb _; red.
      by rewrite Rmin_leq // Rmax_leq in Hx.
    move/Rnot_le_lt in Hba.
    apply: contains_intvl_trans Hb Ha _; red.
    by rewrite Rmin_swap Rmax_swap Rmin_lt // Rmax_lt in Hx.
Qed.

End NumericIntegration.


Lemma IsubXX (x0 : R) :
contains iX0 (Xreal x0) ->
contains (I.convert (Isub X0 X0)) (Xreal 0).
Proof.
move => Hx0.
have -> : 0%R = (x0 - x0)%R by ring.
rewrite Xreal_sub.
by apply: I.sub_correct.
Qed.

Lemma contains_interval_float_integral (p : PolR.T) :
  approx Mf >:: p ->
  TM_integral_poly >:: (PolR.primitive tt 0%R p).
Proof.
move=> Hp; rewrite /TM_integral_poly.
by apply: Pol.primitive_correct; first exact: cont0.
Qed.

Lemma TM_integral_error_0 (x0 : R) :
  contains iX0 (Xreal x0) ->
  i_validTM (I.convert X0) iX Mf xF ->
  contains (I.convert (TM_integral_error TM_integral_poly)) (Xreal 0).
Proof.
move => Hx0X0 [Hnai ErrMf0 HX0X HPol].
case: (HPol (x0) Hx0X0) => [p Hcontains _].
have->: Xreal 0 = Xadd (Xreal 0) (Xadd (Xreal 0) (Xreal 0)).
  by rewrite /= 2!Rplus_0_l.
apply: I.add_correct; last apply: I.add_correct.
- apply: (@Aux.mul_0_contains_0_r _ (Xreal (x0 - x0))) => // .
  have->: Xreal (x0 - x0) = Xsub (Xreal x0) (Xreal x0) by [].
  by apply: I.sub_correct => //; apply: (subset_contains (I.convert X0) _).
- apply (BndThm.ComputeBound_nth0 (PolR.primitive tt 0%R p)).
    apply: Pol.primitive_correct =>//; exact: cont0.
  exact: (IsubXX Hx0X0).
  have->: 0%R = PolR.nth (PolR.primitive tt 0%Re p) 0 by [].
  exact: contains_interval_float_integral.
- apply: (@Aux.mul_0_contains_0_r _ (Xreal (x0 - x0))) => // .
  exact: R_sub_correct.
Qed.

Definition TM_integral :=
let R := TM_integral_poly in RPA R (TM_integral_error TM_integral_poly).

(* Definition Xint (f : ExtendedR -> ExtendedR) x0 x1 :=
  let f := toXreal_fun f in
  *)

Lemma TM_integral_correct (x0 : Rdefinitions.R) :
contains iX0 (Xreal x0) ->
i_validTM (I.convert X0) iX Mf xF ->
i_validTM (I.convert X0) iX TM_integral (toXreal_fun (RInt f x0)).
Proof.
move => Hx0X0 [Hnai ErrMf0 HX0X HPol] /= ; split => //.
  by apply: (@TM_integral_error_0 _ Hx0X0).
move=> /= x1 HX0x1 {ErrMf0}.
case: (HPol (x0) Hx0X0) => [p Hcontains H3].
case: (HPol (x1) HX0x1) => [p1 Hcontains1 H31 {HPol}].
exists (PolR.primitive tt 0 p1).
- by apply: Pol.primitive_correct; first exact: cont0.
- move => x hxX.
  rewrite toR_toXreal.
  have <- : RInt f x0 x1 + RInt f x1 x = RInt f x0 x.
 + apply: RInt_Chasles; first apply: f_int => // .
      by apply: subset_contains HX0x1 => // .
    by apply: f_int => // .
  have -> : PolR.horner tt (PolR.primitive tt 0 p1) (x - x1) =
            RInt (fun t => PolR.horner tt p1 (t - x1)) x1 x.
  + rewrite RInt_translation_sub.
      have -> : PolR.horner tt (PolR.primitive tt 0 p1) (x - x1) =
            PolR.horner tt (PolR.primitive tt 0 p1) (x - x1) -
            PolR.horner tt (PolR.primitive tt 0 p1) (x1 - x1).
      * have -> : x1 - x1 = 0 by ring.
        set t0 := (X in (_ = _ - X)).
        have->: t0 = 0; last by rewrite Rminus_0_r.
        rewrite /t0 PolR.hornerE PolR.size_primitive big1 // => i _.
        rewrite PolR.nth_primitive.
        case: ifP; first by rewrite Rmult_0_l.
        rewrite /PolR.int_coeff; case: i; first by rewrite Rmult_0_l.
        by move=> *; rewrite /= Rmult_0_l Rmult_0_r.
    by rewrite Rpol_integral_0.
rewrite {Hcontains1}.
set rem := (X in X + _ - _).
set i1 := (X in (rem + X - _)).
set i2 := (X in (rem + _ - X)).
have -> : rem + i1 - i2 = rem + (i1 - i2) by ring.
have -> : i1 - i2 = RInt (fun t => f t - PolR.horner tt p1 (t - x1)) x1 x.
    rewrite -RInt_minus; first by [].
    + by apply: f_int.
    + have {2}-> : x1 = (0 + x1) by ring.
        have -> : x = (x - x1) + x1 by ring.
        apply: ex_RInt_translation_sub.
        exact: Rpol_integrable.
rewrite /TM_integral_error {i1 i2}.
rewrite [rem + _]Rplus_comm Xreal_add.
have -> : rem = RInt (fun t => PolR.horner tt p (t - x0)) x0 x1
                      + (RInt f x0 x1 -
          RInt (fun t => PolR.horner tt p (t - x0)) x0 x1) by rewrite /rem; ring.
rewrite Xreal_add {rem}.
apply: I.add_correct; last first;  first apply: I.add_correct.
- rewrite RInt_translation_sub Rpol_integral_0.
  have -> : x0 - x0 = 0 by ring.
  rewrite PolR.toSeq_horner0. rewrite -nth0 -PolR.nth_toSeq PolR.nth_primitive // Rminus_0_r.
  apply: Bnd.ComputeBound_correct; last by rewrite Xreal_sub; exact: I.sub_correct.
  by apply: Pol.primitive_correct; first exact: cont0.
  + (rewrite -RInt_minus; last by apply: pol_int_sub); last first.
      by apply: f_int => //; apply: (subset_contains iX0) => // .
      apply: contains_RInt_full => // .
      apply: ex_RInt_minus.
        by apply: f_int => //; apply: (subset_contains iX0) => // .
        by apply: pol_int_sub.
      move => x2 Hx2.
      have hx2 : contains iX (Xreal x2).
      apply: (@contains_trans iX (Xreal (Rmin x0 x1)) (Xreal (Rmax x0 x1))) => // .
        by rewrite /Rmin; case (Rle_dec x0 x1) => _ //; apply: (subset_contains iX0) => // .
        by rewrite /Rmax; case (Rle_dec x0 x1) => _ //; apply: (subset_contains iX0) => // .
      by move/(_ x2 hx2) in H3.
rewrite  {H3}.
- apply: contains_RInt_full => // .
  + apply: ex_RInt_minus.
        by apply: f_int => //; apply: (subset_contains iX0).
        by apply: pol_int_sub.
      move => x2 Hx2.
      have hx2 : contains iX (Xreal x2).
      apply: (@contains_trans iX (Xreal (Rmin x1 x)) (Xreal (Rmax x1 x))) => // .
      by rewrite /Rmin;case (Rle_dec x1 x) =>_ //;apply: (subset_contains iX0).
      by rewrite /Rmax;case (Rle_dec x1 x) => _ //;apply: (subset_contains iX0).
      by move/(_ x2 hx2) in H31.
Qed.

End TM_integral.

Definition is_const (f : ExtendedR -> ExtendedR) (X c : I.type) : Prop :=
  exists2 y : ExtendedR, contains (I.convert c) y
  & forall x : R, contains (I.convert X) (Xreal x) -> f (Xreal x) = y.

Lemma is_const_ext (f g : ExtendedR -> ExtendedR) X c :
  (forall x : R, contains (I.convert X) (Xreal x) -> f(Xreal x)=g(Xreal x)) ->
  is_const f X c -> is_const g X c.
Proof.
move=> Hmain [a Ha1 Ha2].
exists a =>//.
move=> x Hx.
rewrite -Hmain //.
exact: Ha2.
Qed.

Corollary is_const_ext_weak (f g : ExtendedR -> ExtendedR) X c :
  (forall x : ExtendedR, f x = g x) ->
  is_const f X c -> is_const g X c.
Proof.
move=> Hmain.
apply: is_const_ext.
move=> x _; exact: Hmain.
Qed.

Lemma contains_IIbnd (a b x : ExtendedR) (X : interval) :
  contains X a -> contains X b -> contains (IIbnd a b) x ->
  contains X x.
Proof.
case: X =>[//|l u]; rewrite /contains.
by case: x =>[|x]; case: l =>[|l]; case: u =>[|u]; case: a =>[|a]; case: b =>[|b]//;
  psatzl R.
Qed.

Lemma Rdiv_pos_compat (x y : R) :
  (0 <= x -> 0 < y -> 0 <= x / y)%Re.
Proof.
move=> Hx Hy.
rewrite /Rdiv -(@Rmult_0_l (/ y)).
apply: Rmult_le_compat_r =>//.
by left; apply: Rinv_0_lt_compat.
Qed.

Lemma Rlt_neq (x y : R) :
  (x < y -> x <> y)%Re.
Proof. by move=> Hxy Keq; rewrite Keq in Hxy; apply: (Rlt_irrefl _ Hxy). Qed.

Lemma Rlt_neq_sym (x y : R) :
  (x < y -> y <> x)%Re.
Proof. by move=> Hxy Keq; rewrite Keq in Hxy; apply: (Rlt_irrefl _ Hxy). Qed.

Lemma Rdiv_pos_compat_rev (x y : R) :
  (0 <= x / y -> 0 < y -> 0 <= x)%Re.
Proof.
move=> Hx Hy.
rewrite /Rdiv -(@Rmult_0_l y) -(@Rmult_1_r x).
rewrite -(Rinv_r y); last exact: Rlt_neq_sym.
rewrite (Rmult_comm y) -Rmult_assoc.
by apply: Rmult_le_compat_r =>//; left.
Qed.

Lemma Rdiv_neg_compat (x y : R) :
  (x <= 0 -> 0 < y -> x / y <= 0)%Re.
Proof.
move=> Hx Hy.
rewrite /Rdiv -(@Rmult_0_l (/ y)).
apply: Rmult_le_compat_r =>//.
by left; apply Rinv_0_lt_compat.
Qed.

Lemma Rdiv_neg_compat_rev (x y : R) :
  (x / y <= 0 -> 0 < y -> x <= 0)%Re.
Proof.
move=> Hx Hy.
rewrite -(@Rmult_0_l y) -(@Rmult_1_r x).
rewrite <- (Rinv_r y); last by apply Rlt_neq_sym.
rewrite (Rmult_comm y) -Rmult_assoc.
apply: Rmult_le_compat_r =>//.
by left.
Qed.

Lemma Rdiv_twice (x y z : R) :
  y <> R0 -> z <> R0 -> (x / (y / z) = (x / y) * z)%Re.
Proof. by move=> Zy Zz; field; split. Qed.

Section ProofOfRec.

Section GenericProof.
(** Generic proof for [TLrem]/[Ztech]. *)

Variable xf : ExtendedR -> ExtendedR.
Variable F : I.type -> I.type.
Variable P : R -> nat -> PolR.T.
Variable IP : I.type -> nat -> Pol.T.

Let f0 := toR_fun xf.
Let def := defined xf.
Let Dn n := Derive_n f0 n.

Hypothesis xf_Xnan : xf Xnan = Xnan.
Hypothesis F_contains : I.extension xf F.

Class validPoly : Prop := ValidPoly {
  Poly_size : forall (x0 : R) n, PolR.size (P x0 n) = n.+1;
  Poly_nth :
    forall (x : R) n k,
    ex_derive_n f0 n x ->
    k <= n ->
    PolR.nth (P x n) k = Rdiv (Dn k x) (INR (fact k)) }.

Class validIPoly : Prop := ValidIPoly {
  IPoly_size :
    forall (X0 : I.type) x0 n, eq_size (IP X0 n) (P x0 n);
  IPoly_nth : forall (X0 : I.type) x0 n, X0 >: x0 -> IP X0 n >:: P x0 n;
  IPoly_nai :
    forall X, forall r : R, contains (I.convert X) (Xreal r) -> ~~ def r ->
    forall n k, k <= n -> I.convert (Pol.nth (IP X n) k) = IInan
}.

Context { validPoly_ : validPoly }.
Context { validIPoly_ : validIPoly }.

Variables X : I.type.

(* Hypothesis Hdef : forall x, X >: x -> def x. *)
Hypothesis Hder_n : forall n x, X >: x -> ex_derive_n f0 n x.

Lemma Poly_nth0 x n : X >: x -> PolR.nth (P x n) 0 = f0 x.
Proof.
move=> H; rewrite Poly_nth // ?Rcomplements.Rdiv_1 //.
exact: Hder_n.
Qed.

Lemma Poly_size' Y n : Pol.size (IP Y n) = n.+1.
Proof. by rewrite (IPoly_size Y (*dummy*)0) Poly_size. Qed.

Theorem i_validTM_TLrem (X0 : I.type) n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (IP X0 n) (TLrem prec IP X0 X n)) xf.
Proof.
move=> Hsubs [t Ht].
pose err := TLrem prec IP X0 X n.
split=>//=.

(* Nai *)
move=> x Hx Nx; rewrite /TLrem; apply/eqNaiP.
rewrite I.mul_propagate_l //.
exact: (IPoly_nai Hx Nx).

(* |- 0 \in err *)
set V := (I.power_int prec (I.sub prec X X0) (Z_of_nat n.+1)).
apply (mul_0_contains_0_r _ (y := Xreal (PolR.nth (P t n.+1) n.+1))).
  apply: IPoly_nth =>//.
  exact: subset_contains (I.convert X0) _ _ _ _ =>//.
apply: pow_contains_0 =>//.
exact: subset_sub_contains_0 Ht _.

move=> x0 Hx0.
(* |- Main condition for i_validTM *)
exists (P x0 n); first by apply: IPoly_nth.
move=> x Hx.
rewrite PolR.hornerE Poly_size //.
have H0 : X >: x0 by exact: (subset_contains (I.convert X0)).
have Hbig :
  \big[Rplus/R0]_(0 <= i < n.+1) (PolR.nth (P x0 n) i * (x - x0) ^ i)%R =
  \big[Rplus/R0]_(0 <= i < n.+1) (Dn i x0 / INR (fact i) * (x - x0)^i)%R.
apply: eq_big_nat => i Hi; rewrite Poly_nth //; exact: Hder_n.
rewrite Hbig.
have Hder' : forall n r, X >: r -> ex_derive_n (toR_fun xf) n r.
  move=> m r Hr.
  exact: Hder_n.
have [c [Hcin [Hc Hc']]] := (@ITaylor_Lagrange xf (I.convert X) n Hder' x0 x H0 Hx).
rewrite Hc {Hc t Ht} /TLrem.
apply: R_mul_correct=>//.
  rewrite -(@Poly_nth _ c n.+1 n.+1) //.
    exact: IPoly_nth.
  exact: Hder_n.
rewrite pow_powerRZ.
apply: R_power_int_correct.
exact: R_sub_correct.
Qed.

Definition Rdelta (n : nat) (x0 x : R) :=
  (f0 x - (P x0 n).[x - x0])%R.

(*
Definition delta_big (n : nat) (xi0 x : ExtendedR) :=
  Xsub (XF0 x) (\big[Xadd/Xreal 0]_(i < n.+1) (PolR.tnth (XP xi0 n) i * (x - xi0) ^ i)%XR).

Definition Xdelta_mask (n : nat) (xi0 x : ExtendedR) :=
  Xsub (XF0 x) (Xmask (\big[Xadd/Xreal 0]_(i < n.+1) (PolR.tnth (XP xi0 n) i * (x - xi0) ^ i)%XR
) (x - xi0)%XR).

Lemma Xdelta_idem (n : nat) (xi0 x : ExtendedR) :
  Xdelta n xi0 x = Xdelta_big n xi0 x.
Proof. by rewrite /Xdelta /Xdelta_big is_horner_pos ?XPoly_size. Qed.

Lemma Xdelta_idem' (n : nat) (xi0 x : ExtendedR) :
  Xdelta n xi0 x = Xdelta_mask n xi0 x.
Proof.
by rewrite /Xdelta /Xdelta_big is_horner_mask /Xdelta_mask XPoly_size.
Qed.
*)

(** We now define the derivative of [Rdelta n x0] *)
Definition Rdelta' (n : nat) (x0 x : R) :=
  (Dn 1 x - (PolR.deriv tt (P x0 n)).[x - x0])%R.

Lemma derivable_pt_lim_pow_sub (r s : R) (n : nat) :
  derivable_pt_lim (fun x : R => (x - s) ^ n)%Re r (INR n * (r - s) ^ n.-1)%Re.
Proof.
have->: let expr := (INR n * (r - s) ^ n.-1)%Re in expr = (expr * 1)%Re.
  by rewrite /= Rmult_1_r.
apply: (derivable_pt_lim_comp (fun x => x - s)%Re (pow^~n) r).
  have->: R1 = Rminus R1 R0 by ring.
  apply: derivable_pt_lim_minus.
    exact: derivable_pt_lim_id.
  exact: derivable_pt_lim_const.
exact: derivable_pt_lim_pow.
Qed.

Lemma bigXadd_P (m n : nat) (x0 s : R) :
  ex_derive_n f0 n x0 ->
  m <= n.+1 ->
  \big[Rplus/R0]_(0 <= i < m)
    (PolR.nth (P x0 n) i * s ^ i)%R =
  \big[Rplus/R0]_(0 <= i < m)
    ((Dn i x0) / INR (fact i) * s ^ i)%R.
Proof.
move=> Hxi0 Hmn; rewrite !big_mkord.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 Hx Hy|i _]; first by rewrite Hx // Hy.
rewrite Poly_nth //.
case: i => [i Hi] /=.
rewrite -ltnS.
exact: leq_trans Hi Hmn.
Qed.

Lemma bigXadd'_P (m n : nat) (x0 s : R) :
  ex_derive_n f0 n x0 ->
  m <= n ->
  \big[Rplus/R0]_(0 <= i < m) (PolR.nth (P x0 n) i.+1 * INR i.+1 * s ^ i)%R =
  \big[Rplus/R0]_(0 <= i < m) ((Dn i.+1 x0) / INR (fact i) * s ^ i)%R.
Proof.
move=> Hx0 Hmn; rewrite !big_mkord.
case: m Hmn =>[|m] Hmn; first by rewrite !big_ord0.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 -> ->//|i _].
rewrite Poly_nth //; last by case: i => [i Hi] /=; exact: leq_trans Hi Hmn.
rewrite fact_simpl mult_INR.
field.
split; by [apply: INR_fact_neq_0 | apply: not_0_INR ].
Qed.

Lemma Rderive_delta (Pr : R -> Prop) (n : nat) (x0 : R) :
  (forall r : R, Pr r -> X >: r) ->
  Pr x0 ->
  Rderive_over Pr (Rdelta n x0) (Rdelta' n x0).
Proof.
move=> HPr Hx0 x Hx.
rewrite /Rdelta /Rdelta'.
apply: is_derive_minus.
  apply: Derive_correct.
  apply: (Hder_n 1).
  exact: HPr.
set d := (_ ^`()).[_].
have->: d = scal R1 d by rewrite /scal /= /mult /= Rmult_1_l.
apply: is_derive_comp; last first.
rewrite -[R1]Rminus_0_r; apply: is_derive_minus; by auto_derive.
rewrite /d.
exact: PolR.is_derive_horner.
Qed.

Lemma Rmonot_contains (g : R -> R) (a b : R) :
  Rmonot (intvl a b) g ->
  forall (x y z : R),
  intvl a b x -> intvl a b y -> intvl x y z ->
  intvl (g x) (g y) (g z) \/ intvl (g y) (g x) (g z).
Proof.
move=> Hmonot x y z Hx Hy Hz.
have Habz : intvl a b z by exact: intvl_trans Hx Hy Hz.
case: Hmonot; rewrite /Rincr /Rdecr =>H; [left|right];
  split; apply: H =>//; move: Hz; rewrite /intvl /=; psatzl R.
Qed.

Lemma upper_Rpos_over
  (l := proj_val (I.convert_bound (I.lower X)))
  (u := proj_val (I.convert_bound (I.upper X)))
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  I.bounded X = true ->
  X >: x0 ->
  Rpos_over (intvl l u) (Dn n.+1) ->
  forall x : R, intvl x0 u x -> intvl x x0 c \/ intvl x0 x c ->
  (0 <= (Dn n.+1 c) / INR (fact n) * (x - x0) ^ n)%Re.
Proof.
move=> Hbnd Hx0 Hsign x Hx [Hc|Hc]. (* REMARK: Hbnd may be unnecessary *)
  have ->: x = x0.
    by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: (0 <= (x - x0))%Re.
  by move: Hx Hc; rewrite /intvl; lra.
have Hle_pow := pow_le _ n Hle.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : intvl l u l.
  exact/intvlP/(bounded_contains_lower _ Hx0).
have contains_u : intvl l u u.
  exact/intvlP/(bounded_contains_upper _ Hx0).
have contains_c : intvl l u c.
  move: Hx0 Hx Hc contains_l contains_u.
  move/(intvlP Hbnd); fold l u.
  move=> Hx0 Hx Hc Hl Hu.
  apply: (intvl_trans Hx0 _ Hc).
  apply: (intvl_trans Hx0 Hu Hx).
move/(_ c contains_c) in Hsign.
by apply: Rmult_le_pos_pos=>//; apply: Rdiv_pos_compat.
Qed.

Lemma upper_Rneg_over
  (l := proj_val (I.convert_bound (I.lower X)))
  (u := proj_val (I.convert_bound (I.upper X)))
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  I.bounded X = true ->
  X >: x0 ->
  Rneg_over (intvl l u) (Dn n.+1) ->
  forall x : R, intvl x0 u x -> intvl x x0 c \/ intvl x0 x c ->
  (Dn n.+1 c / INR (fact n) * (x - x0) ^ n <= 0)%Re.
Proof.
move=> Hbnd Hx0 Hsign x Hx [Hc|Hc]. (* REMARK: Hbnd may be unnecessary *)
  have ->: x = x0.
    by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: (0 <= (x - x0))%Re.
  by move: Hx Hc; rewrite /intvl; lra.
have Hle_pow := pow_le _ n Hle.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : intvl l u l.
  exact/intvlP/(bounded_contains_lower _ Hx0).
have contains_u : intvl l u u.
  exact/intvlP/(bounded_contains_upper _ Hx0).
have contains_c : intvl l u c.
  move: Hx0 Hx Hc contains_l contains_u.
  move/(intvlP Hbnd); fold l u.
  move=> Hx0 Hx Hc Hl Hu.
  apply: (intvl_trans Hx0 _ Hc).
  apply: (intvl_trans Hx0 Hu Hx).
move/(_ c contains_c) in Hsign.
by apply: Rmult_le_neg_pos=>//; apply: Rdiv_neg_compat.
Qed.

Lemma pow_Rabs_sign (r : R) (n : nat) :
  (r ^ n = powerRZ
    (if Rle_bool R0 r then 1 else -1) (Z_of_nat n) * (Rabs r) ^ n)%Re.
Proof.
elim: n =>[|n /= ->]; first by rewrite Rmult_1_l.
case: Rle_bool_spec => Hr.
  rewrite powerRZ_R1 Rmult_1_l SuccNat2Pos.id_succ.
  by rewrite pow1 Rabs_pos_eq // Rmult_1_l.
by rewrite {-1 3}Rabs_left // SuccNat2Pos.id_succ -pow_powerRZ /=; ring.
Qed.

Lemma powerRZ_1_even (k : Z) :(0 <= powerRZ (-1) (2 * k))%Re.
Proof.
by case: k =>[|p|p] /=; rewrite ?Pos2Nat.inj_xO ?pow_1_even; auto with real.
Qed.

Lemma ZEven_pow_le (r : R) (n : nat) :
  Z.Even (Z_of_nat n) ->
  (0 <= r ^ n)%Re.
Proof.
move=> [k Hk].
rewrite pow_Rabs_sign; case: Rle_bool_spec =>[_|Hr].
  rewrite powerRZ_R1 Rmult_1_l.
  apply: pow_le.
  exact: Rabs_pos.
rewrite Hk.
apply: Rmult_le_pos_pos; first exact: powerRZ_1_even.
by apply: pow_le; exact: Rabs_pos.
Qed.

Lemma Ropp_le_0 (x : R) :
  (0 <= x -> - x <= 0)%Re.
Proof. by move=> ?; auto with real. Qed.

Lemma ZOdd_pow_le (r : R) (n : nat) :
  Z.Odd (Z_of_nat n) ->
  (r <= 0 -> r ^ n <= 0)%Re.
Proof.
move=> [k Hk] Hneg.
rewrite pow_Rabs_sign; case: Rle_bool_spec =>[Hr|Hr].
  have->: r = R0 by psatzl R.
  rewrite Rabs_R0 pow_ne_zero ?Rmult_0_r; first by auto with real.
  by zify; omega. (* odd => nonzero *)
rewrite Hk.
apply: Rmult_le_neg_pos; last by apply: pow_le; exact: Rabs_pos.
rewrite powerRZ_add; discrR.
apply: Rmult_le_pos_neg; first exact: powerRZ_1_even.
by rewrite /= Rmult_1_r; apply: Ropp_le_0; apply: Rle_0_1.
Qed.

Lemma lower_even_Rpos_over
  (l := proj_val (I.convert_bound (I.lower X)))
  (u := proj_val (I.convert_bound (I.upper X)))
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  Z.Even (Z_of_nat n) ->
  I.bounded X = true ->
  X >: x0 ->
  Rpos_over (intvl l u) (Dn n.+1) ->
  forall x : R, intvl l x0 x ->
                intvl x x0 c \/ intvl x0 x c ->
  (0 <= Dn n.+1 c / INR (fact n) * (x - x0) ^ n)%Re.
Proof.
move=> Hev Hbnd Hx0 Hsign x Hx [Hc|Hc]; last first. (* REMARK: Hbnd may be unnecessary *)
  have ->: x = x0 by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: ((x - x0) <= 0)%Re.
  by move: Hx Hc; rewrite /intvl; lra.
have Hle_pow := @ZEven_pow_le (x - x0)%Re n Hev.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : intvl l u l.
  exact/intvlP/(bounded_contains_lower _ Hx0).
have contains_u : intvl l u u.
  exact/intvlP/(bounded_contains_upper _ Hx0).
have contains_c : intvl l u c.
  move: Hx0 Hx Hc contains_l contains_u.
  move/(intvlP Hbnd); fold l u.
  move=> Hx0 Hx Hc Hl Hu.
  apply: (intvl_trans _ Hx0 Hc).
  apply: (intvl_trans Hl Hx0 Hx).
move/(_ c contains_c) in Hsign.
by apply: Rmult_le_pos_pos=>//; apply: Rdiv_pos_compat.
Qed.

Lemma lower_even_Rneg_over
  (l := proj_val (I.convert_bound (I.lower X)))
  (u := proj_val (I.convert_bound (I.upper X)))
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  Z.Even (Z_of_nat n) ->
  I.bounded X = true ->
  X >: x0 ->
  Rneg_over (intvl l u) (Dn n.+1) ->
  forall x : R, intvl l x0 x -> intvl x x0 c \/ intvl x0 x c ->
  (Dn n.+1 c / INR (fact n) * (x - x0) ^ n <= 0)%Re.
Proof.
move=> Hev Hbnd Hx0 Hsign x Hx [Hc|Hc]; last first. (* REMARK: Hbnd may be unnecessary *)
  have ->: x = x0 by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: ((x - x0) <= 0)%Re.
  by move: Hx Hc; rewrite /intvl; lra.
have Hle_pow := @ZEven_pow_le (x - x0)%Re n Hev.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : intvl l u l.
  exact/intvlP/(bounded_contains_lower _ Hx0).
have contains_u : intvl l u u.
  exact/intvlP/(bounded_contains_upper _ Hx0).
have contains_c : intvl l u c.
  move: Hx0 Hx Hc contains_l contains_u.
  move/(intvlP Hbnd); fold l u.
  move=> Hx0 Hx Hc Hl Hu.
  apply: (intvl_trans _ Hx0 Hc).
  apply: (intvl_trans Hl Hx0 Hx).
move/(_ c contains_c) in Hsign.
by apply: Rmult_le_neg_pos=>//; apply: Rdiv_neg_compat.
Qed.

Lemma lower_odd_Rpos_over
  (l := proj_val (I.convert_bound (I.lower X)))
  (u := proj_val (I.convert_bound (I.upper X)))
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  Z.Odd (Z_of_nat n) ->
  I.bounded X = true ->
  X >: x0 ->
  Rpos_over (intvl l u) (Dn n.+1) ->
  forall x : R, intvl l x0 x -> intvl x x0 c \/ intvl x0 x c ->
  (Dn n.+1 c / INR (fact n) * (x - x0) ^ n <= 0)%Re.
Proof.
move=> Hev Hbnd Hx0 Hsign x Hx [Hc|Hc]; last first. (* REMARK: Hbnd may be unnecessary *)
  have ->: x = x0 by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: ((x - x0) <= 0)%Re.
  by move: Hx Hc; rewrite /intvl; lra.
have Hle_pow := @ZOdd_pow_le (x - x0)%Re n Hev Hle.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : intvl l u l.
  exact/intvlP/(bounded_contains_lower _ Hx0).
have contains_u : intvl l u u.
  exact/intvlP/(bounded_contains_upper _ Hx0).
have contains_c : intvl l u c.
  move: Hx0 Hx Hc contains_l contains_u.
  move/(intvlP Hbnd); fold l u.
  move=> Hx0 Hx Hc Hl Hu.
  apply: (intvl_trans _ Hx0 Hc).
  apply: (intvl_trans Hl Hx0 Hx).
move/(_ c contains_c) in Hsign.
set r := (_ / _)%Re.
rewrite -(@Rmult_0_r r); apply: Rge_le; apply: Rmult_ge_compat_l.
  by apply: Rle_ge; apply: Rdiv_pos_compat.
by auto with real.
Qed.

Lemma lower_odd_Rneg_over
  (l := proj_val (I.convert_bound (I.lower X)))
  (u := proj_val (I.convert_bound (I.upper X)))
  (c x0 : R) (nm1 : nat) (n := nm1.+1) :
  Z.Odd (Z_of_nat n) ->
  I.bounded X = true ->
  X >: x0 ->
  Rneg_over (intvl l u) (Dn n.+1) ->
  forall x : R, intvl l x0 x -> intvl x x0 c \/ intvl x0 x c ->
  (0 <= (Dn n.+1 c) / INR (fact n) * (x - x0) ^ n)%Re.
Proof.
move=> Hev Hbnd Hx0 Hsign x Hx [Hc|Hc]; last first. (* REMARK: Hbnd may be unnecessary *)
  have ->: x = x0 by move: Hx Hc; rewrite /intvl; lra.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: ((x - x0) <= 0)%Re.
  by move: Hx Hc; rewrite /intvl; lra.
have Hle_pow := @ZOdd_pow_le (x - x0)%Re n Hev Hle.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : intvl l u l.
  exact/intvlP/(bounded_contains_lower _ Hx0).
have contains_u : intvl l u u.
  exact/intvlP/(bounded_contains_upper _ Hx0).
have contains_c : intvl l u c.
  move: Hx0 Hx Hc contains_l contains_u.
  move/(intvlP Hbnd); fold l u.
  move=> Hx0 Hx Hc Hl Hu.
  apply: (intvl_trans _ Hx0 Hc).
  apply: (intvl_trans Hl Hx0 Hx).
move/(_ c contains_c) in Hsign.
set r := ((x - x0) ^ n)%Re.
rewrite -(@Rmult_0_l r); apply: Rmult_le_compat_neg_r.
  by auto with real.
exact: Rdiv_neg_compat.
Qed.

Lemma Xsub_0_r (x : ExtendedR) : Xsub x (Xreal 0) = x.
Proof. by case: x =>//= r; rewrite Rminus_0_r. Qed.

Lemma Rdiv_1_r (x : R) : (x / 1 = x)%Re.
Proof. by rewrite /Rdiv Rinv_1 Rmult_1_r. Qed.

Lemma Xdiv_1_r (x : ExtendedR) : (x / Xreal 1 = x)%XR.
Proof.
by case: x; f_equal =>//= r; rewrite zeroF; discrR; rewrite Rdiv_1_r.
Qed.

(** Proposition 2.2.1 in Mioara Joldes' thesis,
    adapted from Lemma 5.12 in Roland Zumkeller's thesis *)
Theorem Zumkeller_monot_rem (x0 : R) (n : nat)
  (l := proj_val (I.convert_bound (I.lower X)))
  (u := proj_val (I.convert_bound (I.upper X))) :
  I.bounded X = true ->
  contains (I.convert X) (Xreal x0) ->
  Rcst_sign (intvl l u) (Dn n.+1) ->
  Rmonot (intvl l x0) (Rdelta n x0) /\
  Rmonot (intvl x0 u) (Rdelta n x0).
Proof.
move=> Hbnd Hx0.
have /(intvlP Hbnd) Hl : contains (I.convert X) (Xreal l).
  exact: bounded_contains_lower Hx0.
have /(intvlP Hbnd) Hu : contains (I.convert X) (Xreal u).
  exact: bounded_contains_upper Hx0.
move/(intvlP Hbnd) in Hx0.
fold l u in Hl, Hu, Hx0.
case: n =>[|nm1] ; last set n := nm1.+1.
  move=> Hsign; split; apply (@Rderive_cst_sign _ _ (Dn 1)) =>//;
    try exact: intvl_connected.
  - move=> x Hx.
    have intvl_x : intvl l u x.
      exact: intvl_trans Hl Hx0 Hx.
    have contains_x : X >: x by apply/intvlP.
    rewrite -[Dn 1 x]Rminus_0_r.
    apply: is_derive_minus.
      apply: Derive_correct.
      exact: (Hder_n 1).
    auto_derive =>//.
      exact: PolR.ex_derive_horner.
    rewrite Rmult_1_l (Derive_ext _ (fun r => PolR.nth (P x0 0) 0)).
      by rewrite Derive_const.
    by move=> r; rewrite PolR.hornerE Poly_size big_nat1 pow_O Rmult_1_r.
  - case: Hsign => Hsign; [left|right]; move: Hsign; rewrite /Rpos_over /Rneg_over.
    + move=> Htop x Hx; apply: Htop.
      exact: intvl_trans Hl Hx0 Hx.
    + move=> Htop x Hx; apply: Htop.
      exact: intvl_trans Hl Hx0 Hx.
  - move=> x Hx.
    have intvl_x : intvl l u x.
      exact: intvl_trans Hx0 Hu Hx.
    have contains_x : X >: x by apply/intvlP.
    rewrite -[Dn 1 x]Rminus_0_r.
    apply: is_derive_minus.
      apply: Derive_correct.
      exact: (Hder_n 1).
    auto_derive =>//.
      exact: PolR.ex_derive_horner.
    rewrite Rmult_1_l (Derive_ext _ (fun r => PolR.nth (P x0 0) 0)).
      by rewrite Derive_const.
    by move=> r; rewrite PolR.hornerE Poly_size big_nat1 pow_O Rmult_1_r.
  case: Hsign => Hsign; [left|right]; move: Hsign; rewrite /Rpos_over /Rneg_over.
  + move=> Htop x Hx; apply: Htop.
    exact: intvl_trans Hx0 Hu Hx.
  + move=> Htop x Hx; apply: Htop.
    exact: intvl_trans Hx0 Hu Hx.
case=>[Hpos|Hneg].
  split.
    apply: (@Rderive_cst_sign _ _ (Rdelta' n x0)) =>//.
    * exact: intvl_connected.
    * apply: Rderive_delta; last exact: intvl_lx Hx0.
      by move=> r Hr; apply/intvlP/(intvl_trans Hl Hx0 Hr).

    { have [Heven|Hodd] := (Z.Even_or_Odd (Z_of_nat nm1.+1)).
      - left.
        move=> x Hx.
        have H'x : X >: x by exact/intvlP/(intvl_trans Hl Hx0 Hx).
        have H'x0 : X >: x0 by exact/intvlP.
        have TL :=
          @ITaylor_Lagrange (toXreal_fun (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
        have [|||c [H1 [H2 H3]]] := TL =>//.
          move=> k t Ht; rewrite toR_toXreal.
          case: k => [//|k]; rewrite -ex_derive_nSS.
          by apply: (Hder_n k.+2) =>//; apply: Hdef.
        rewrite /Rdelta' PolR.horner_derivE Poly_size.
        rewrite bigXadd'_P //; last exact/Hder_n/intvlP.
        set b := \big[Rplus/R0]_(_ <= i < _) _.
        set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
        have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
        rewrite /b /b2 H2 -Derive_nS.
        exact: (@lower_even_Rpos_over c x0 nm1 _ _ _ _ x).

      - right.
        move=> x Hx.
        have H'x : X >: x by exact/intvlP/(intvl_trans Hl Hx0 Hx).
        have H'x0 : X >: x0 by exact/intvlP.
        have TL :=
          @ITaylor_Lagrange (toXreal_fun (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
        have [|||c [H1 [H2 H3]]] := TL =>//.
          move=> k t Ht; rewrite toR_toXreal.
          case: k => [//|k]; rewrite -ex_derive_nSS.
          by apply: (Hder_n k.+2) =>//; apply: Hdef.
        rewrite /Rdelta' PolR.horner_derivE Poly_size.
        rewrite bigXadd'_P //; last exact/Hder_n/intvlP.
        set b := \big[Rplus/R0]_(_ <= i < _) _.
        set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
        have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
        rewrite /b /b2 H2 -Derive_nS.
        exact: (@lower_odd_Rpos_over c x0 nm1 _ _ _ _ x).
    }

  apply: (@Rderive_cst_sign _ _ (Rdelta' n x0)) =>//.
  * exact: intvl_connected.
  * apply: Rderive_delta; last exact/(intvl_xu Hx0).
    by move=> r Hr; apply/intvlP/(intvl_trans Hx0 Hu Hr).

  left.
  move=> x Hx.
  have H'x : X >: x by exact/intvlP/(intvl_trans Hx0 Hu Hx).
  have H'x0 : X >: x0 by exact/intvlP.
  have TL :=
    @ITaylor_Lagrange (toXreal_fun (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
  have [|||c [H1 [H2 H3]]] := TL =>//.
    move=> k t Ht; rewrite toR_toXreal.
    case: k => [//|k]; rewrite -ex_derive_nSS.
    by apply: (Hder_n k.+2) =>//; apply: Hdef.
  rewrite /Rdelta' PolR.horner_derivE Poly_size.
  rewrite bigXadd'_P //; last exact/Hder_n/intvlP.
  set b := \big[Rplus/R0]_(_ <= i < _) _.
  set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
  have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
  rewrite /b /b2 H2 -Derive_nS.
  exact: (@upper_Rpos_over c x0 nm1 _ _ _ x).

split.

  apply: (@Rderive_cst_sign _ _ (Rdelta' n x0)) =>//.
  * exact: intvl_connected.
  * apply: Rderive_delta; last exact/(intvl_lx Hx0).
    by move=> r Hr; apply/intvlP/(intvl_trans Hl Hx0 Hr).

  { have [Heven|Hodd] := (Z.Even_or_Odd (Z_of_nat nm1.+1)).
  - right.
    move=> x Hx.
    have H'x : X >: x by exact/intvlP/(intvl_trans Hl Hx0 Hx).
    have H'x0 : X >: x0 by exact/intvlP.
    have TL :=
      @ITaylor_Lagrange (toXreal_fun (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
    have [|||c [H1 [H2 H3]]] := TL =>//.
      move=> k t Ht; rewrite toR_toXreal.
      case: k => [//|k]; rewrite -ex_derive_nSS.
      by apply: (Hder_n k.+2) =>//; apply: Hdef.
    rewrite /Rdelta' PolR.horner_derivE Poly_size.
    rewrite bigXadd'_P //; last exact/Hder_n/intvlP.
    set b := \big[Rplus/R0]_(_ <= i < _) _.
    set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
    have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
    rewrite /b /b2 H2 -Derive_nS.
    exact: (@lower_even_Rneg_over c x0 nm1 _ _ _ _ x).

  - left.
    move=> x Hx.
    have H'x : X >: x by exact/intvlP/(intvl_trans Hl Hx0 Hx).
    have H'x0 : X >: x0 by exact/intvlP.
    have TL :=
      @ITaylor_Lagrange (toXreal_fun (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
    have [|||c [H1 [H2 H3]]] := TL =>//.
      move=> k t Ht; rewrite toR_toXreal.
      case: k => [//|k]; rewrite -ex_derive_nSS.
      by apply: (Hder_n k.+2) =>//; apply: Hdef.
    rewrite /Rdelta' PolR.horner_derivE Poly_size.
    rewrite bigXadd'_P //; last exact/Hder_n/intvlP.
    set b := \big[Rplus/R0]_(_ <= i < _) _.
    set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
    have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
    rewrite /b /b2 H2 -Derive_nS.
    exact: (@lower_odd_Rneg_over c x0 nm1 _ _ _ _ x).
}


apply: (@Rderive_cst_sign _ _ (Rdelta' n x0)) =>//.
* exact: intvl_connected.
* apply: Rderive_delta; last exact/(intvl_xu Hx0).
  by move=> r Hr; apply/intvlP/(intvl_trans Hx0 Hu Hr).

right.
move=> x Hx.
have H'x : X >: x by exact/intvlP/(intvl_trans Hx0 Hu Hx).
have H'x0 : X >: x0 by exact/intvlP.
have TL :=
  @ITaylor_Lagrange (toXreal_fun (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
have [|||c [H1 [H2 H3]]] := TL =>//.
  move=> k t Ht; rewrite toR_toXreal.
  case: k => [//|k]; rewrite -ex_derive_nSS.
  by apply: (Hder_n k.+2) =>//; apply: Hdef.
rewrite /Rdelta' PolR.horner_derivE Poly_size.
rewrite bigXadd'_P //; last exact/Hder_n/intvlP.
set b := \big[Rplus/R0]_(_ <= i < _) _.
set b2 := \big[Rplus/R0]_(_ <= i < _) _ in H2.
have->: b = b2 by apply: eq_bigr => i _; rewrite -Derive_nS.
rewrite /b /b2 H2 -Derive_nS.
exact: (@upper_Rneg_over c x0 nm1 _ _ _ x).
Qed.

Lemma Ztech_derive_sign (n : nat) :
  not_empty (I.convert X) ->
  I.bounded X = true ->
  isNNegOrNPos (Pol.nth (IP X n.+1) n.+1) = true ->
  Rcst_sign (intvl (proj_val (I.convert_bound (I.lower X)))
                   (proj_val (I.convert_bound (I.upper X)))) (Dn n.+1).
Proof.
move=> [t Ht] Hbnd Hsign.
have Hstep : Rcst_sign
  (intvl (proj_val (I.convert_bound (I.lower X)))
         (proj_val (I.convert_bound (I.upper X))))
  (fun x => (Dn n.+1 x) / INR (fact n.+1))%R.
  move: Hsign; set Gamma := Pol.nth _ _.
  set g := fun x => ((Dn n.+1 x) / INR (fact n.+1))%R.
  rewrite /isNNegOrNPos.
  case E : I.sign_large =>// _;
    have := I.sign_large_correct Gamma; rewrite E => Hmain.
  - left; move=> x Hx.
    have inGamma : Gamma >: g x.
      rewrite /g -(Poly_nth _ (n:=n.+1)) //.
      apply: IPoly_nth =>//.
      exact/intvlP.
      exact/Hder_n/intvlP.
      case/(_ _ inGamma): Hmain =>->.
      exact: Rle_refl.
  - right; move=> x Hx.
    have inGamma : Gamma >: g x.
      rewrite /g -(Poly_nth _ (n:=n.+1)) //.
      apply: IPoly_nth =>//.
      exact/intvlP.
      exact/Hder_n/intvlP.
      move/(_ _ inGamma) in Hmain.
      exact: proj2 Hmain.
  - left; move=> x Hx.
    have inGamma : Gamma >: g x.
      rewrite /g -(Poly_nth _ (n:=n.+1)) //.
      apply: IPoly_nth =>//.
      exact/intvlP.
      exact/Hder_n/intvlP.
      move/(_ _ inGamma) in Hmain.
      rewrite /proj_fun.
      exact: proj2 Hmain.
have: Rcst_sign
  (intvl (proj_val (I.convert_bound (I.lower X)))
         (proj_val (I.convert_bound (I.upper X))))
  (fun x : R => Dn n.+1 x / INR (fact n.+1))%R.
  exact: eq'_Rcst_sign Hstep.
case=>[Hpos|Hneg]; [left|right].
- move=> x Hx.
  move/(_ x Hx): Hpos.
  move=> Htop; apply: Rdiv_pos_compat_rev Htop _.
  change R0 with (INR O).
  apply: lt_INR.
  change (fact n + _)%coq_nat with (fact n.+1).
  exact: lt_O_fact.
  (* by change (fact n + _)%coq_nat with (fact n.+1); apply: INR_fact_neq_0. *)
move=> x Hx.
move/(_ x Hx): Hneg.
   move=> Htop; apply: Rdiv_neg_compat_rev Htop _.
   change R0 with (INR O).
   apply: lt_INR.
   change (fact n + _)%coq_nat with (fact n.+1).
   exact: lt_O_fact.
Qed.

Lemma F_Rcontains : forall X x, X >: x -> F X >: f0 x.
Proof.
clear - F_contains; move=> X x Hx.
rewrite /f0.
case Df: (defined xf x); first by rewrite Xreal_toR //; apply: F_contains.
suff->: I.convert (F X) = IInan by [].
move/definedPf in Df.
apply/contains_Xnan.
by rewrite -Df; apply: F_contains.
Qed.

Theorem i_validTM_Ztech (X0 : I.type) n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (IP X0 n) (Ztech prec IP (IP X0 n) F X0 X n)) xf.
Proof.
move=> Hsubs tHt.
case E1 : (isNNegOrNPos (Pol.nth (IP X n.+1) n.+1)); last first.
  rewrite (ZtechE1 _ _ _ _ E1).
  exact: i_validTM_TLrem.
case E2 : (I.bounded X); last first.
  rewrite (ZtechE2 _ _ _ _ _ _ E2).
  exact: i_validTM_TLrem.
have [t Ht] := tHt. (* TODO : useful ? *)
set err := Ztech prec IP (IP X0 n) F X0 X n.
have [r' Hr'0] : not_empty (I.convert X0).
  exact: contains_not_empty Ht.
have Hr' : contains (I.convert X) (Xreal r').
  exact: subset_contains Hsubs _ Hr'0.
pose x' := Xreal r'.
have XNNan : I.convert X <> IInan.
  move=> HX.
  exact: bounded_IInan E2 _.
have Hder : forall r : R, X >: r -> def r.
  move=> r Hr.
  rewrite -[def _]negbK; apply/negP => Kr.
  have Knai := @IPoly_nai validIPoly_ X r Hr Kr n.+1 n.+1 (leqnn _).
  by rewrite isNNegOrNPos_false in E1.
split=>//.
  move=> x Hx; rewrite [defined _ _]Hder //.
  rewrite /= /err /Ztech E1 E2 /=.
  apply: I.join_correct; right.
  have C1 : contains (I.convert (F X0)) (xf (Xreal r')) by exact: F_contains.
  case E0 : (xf (Xreal r')) => [|r'0].
    rewrite I.sub_propagate_r //.
    rewrite (IPoly_nai Hr'0) //.
    by apply/definedPn.
  have->: Xreal 0 = Xsub (Xreal r'0) (Xreal r'0) by simpl; f_equal; ring.
  apply: I.sub_correct; rewrite E0 // in C1.
  rewrite -{}E0 in C1 *.
  suff->: xf (Xreal r') = Xreal (PolR.nth (P r' n) 0) by apply: IPoly_nth.
  by rewrite Poly_nth0 ?Xreal_toR; try apply: Hder_def; try apply: Hder.
move=> x0 Hx0.
exists (P x0 n); first by move=> k; apply: IPoly_nth.
pose Idelta := fun X => I.sub prec (F X) (Pol.horner prec (IP X0 n) (I.sub prec X X0)).
pose Rdelta0 := Rdelta n x0.
move=> x Hx.

rewrite /err /Ztech E1 E2 /=.
set Delta := I.join (I.join _ _) _; rewrite -/(Rdelta n x0 x) -/(Rdelta0 x).
have [Hlower Hupper] := bounded_singleton_contains_lower_upper E2.
have [Hbl Hbu] := I.bounded_correct _ E2.
have [Hcl _] := I.lower_bounded_correct _ Hbl.
have [Hcu _] := I.upper_bounded_correct _ Hbu.
set (l := (proj_val (I.convert_bound (I.lower X)))) in *.
set (u := (proj_val (I.convert_bound (I.upper X)))) in *.
have {Hlower} Hlower :
  Idelta (Ibnd2 (I.lower X)) >: Rdelta0 (proj_val (I.convert_bound (I.lower X))).
  apply: R_sub_correct =>//.
  - rewrite Hcl in Hlower.
    exact: F_Rcontains.
  - apply: Pol.horner_correct.
    exact: IPoly_nth.
    apply: R_sub_correct =>//.
    by rewrite Hcl in Hlower.
have {Hupper} Hupper :
  Idelta (Ibnd2 (I.upper X)) >: Rdelta0 (proj_val (I.convert_bound (I.upper X))).
  apply: R_sub_correct =>//.
  - rewrite Hcu in Hupper.
    exact: F_Rcontains.
  - apply: Pol.horner_correct.
    exact: IPoly_nth.
    apply: R_sub_correct =>//.
    by rewrite Hcu in Hupper.
have HX0 : Idelta X0 >: Rdelta0 x0.
  apply: R_sub_correct =>//.
  - exact: F_Rcontains.
  - apply: Pol.horner_correct.
    exact: IPoly_nth.
    exact: R_sub_correct.
have {Hlower} Hlower : Delta >: Rdelta0 l.
  by apply: I.join_correct; left; apply: I.join_correct; left.
have {Hupper} Hupper : Delta >: Rdelta0 u.
  by apply: I.join_correct; left; apply: I.join_correct; right.
have H'x0 : X >: x0 by exact: (subset_contains (I.convert X0)).
have {HX0} HX0 : contains (I.convert Delta) (Xreal (Rdelta0 x0)).
  apply: I.join_correct; right.
  apply: R_sub_correct; first exact: F_Rcontains.
  rewrite Rminus_diag_eq //.
  suff->: ((P x0 n).[0%R]) = PolR.nth (P x0 n) 0 by apply: IPoly_nth.
  rewrite PolR.hornerE Poly_size big_nat_recl // pow_O Rmult_1_r.
  rewrite big1 ?(Rplus_0_r, Rmult_1_r) //.
  move=> i _.
  by rewrite /= Rmult_0_l Rmult_0_r.
have [||Hlow|Hup] := @intvl_lVu l u x0 x; try exact/intvlP.
  have [|||H1|H2] := @Rmonot_contains Rdelta0 l x0 _ _ _ _ _ _ Hlow.
  + apply: (proj1 (@Zumkeller_monot_rem x0 n E2 H'x0 _)) =>//.
    apply: Ztech_derive_sign =>//.
    by exists x0.
    exact: intvl_l Hlow.
    exact: intvl_u Hlow.
  + exact: (@contains_intvl_trans (Rdelta0 l) (Rdelta0 x0)).
  + exact: (@contains_intvl_trans (Rdelta0 x0) (Rdelta0 l)).
have [|||H1|H2] := @Rmonot_contains Rdelta0 x0 u _ _ _ _ _ _ Hup.
+ apply: (proj2 (@Zumkeller_monot_rem x0 n E2 H'x0 _)) =>//.
  apply: Ztech_derive_sign =>//.
  by exists x0.
  exact: intvl_l Hup.
  exact: intvl_u Hup.
+ exact: (@contains_intvl_trans (Rdelta0 x0) (Rdelta0 u)).
+ exact: (@contains_intvl_trans (Rdelta0 u) (Rdelta0 x0)).
Qed.

End GenericProof.

(*
Section rec1_correct.

Variable (XF_rec : FullXR.T -> FullXR.T -> nat -> FullXR.T).
Variable (F_rec : T -> T -> nat -> T).
Class extension2N := Extension2N :
  forall (ix iy : I.type) (x y : ExtendedR) (n : nat),
  contains (I.convert ix) x ->
  contains (I.convert iy) y ->
  contains (I.convert (F_rec ix iy n)) (XF_rec x y n).
Context { H_F_rec : extension2N }.

Class compat_rec1 := Compat_rec1 :
  forall (r : FullXR.T) (k : nat),
  XF_rec r (XDn k r / Xreal (INR (fact k)))%XR k.+1 =
  (XDn k.+1 r / Xreal (INR (fact k.+1)))%XR.
Context { H_XF_rec : compat_rec1 }.

Definition IP_rec1 X0 := trec1 (F_rec X0) (F0 X0).
Definition XP_rec1 xi0 := PolR.trec1 (XF_rec xi0) (xf xi0).

Instance validXPoly_rec1 :
  validXPoly XP_rec1.
Proof.
constructor; first by move=> *; rewrite PolR.tsize_trec1.
move=> r n k Hkn.
elim: k n Hkn =>[|k IHk] n Hkn.
  rewrite PolR.trec1_spec0 /= XDn_0.
  case (xf r)=> // r0 /=.
  case C: (is_zero 1); last by f_equal; field.
    by rewrite /is_zero (Req_bool_false _ _ R1_neq_R0) in C.
have K := @PolR.trec1_spec (XF_rec r) (xf r) n k.
move: Hkn; rewrite /leq subSS -/(leq _ _) =>/K ->.
by rewrite IHk.
Qed.

Instance validPoly_rec1 :
  validPoly XP_rec1 IP_rec1.
Proof.
constructor; first by move=> *; rewrite PolR.tsize_trec1 Pol.tsize_trec1.
move=> X0 r0 n k Hr0 Hk.
elim: k n Hk =>[|k IHk] n Hk.
  rewrite trec1_spec0 PolR.trec1_spec0.
  exact: F0_contains.
have K := @trec1_spec (F_rec X0) (F0 X0) n k.
case: (leqP k n)=> Hkn.
  move: Hk; rewrite /leq subSS -/(leq _ _) => Hk; rewrite (K Hk).
  have K' := @PolR.trec1_spec (XF_rec r0) (xf r0) n k.
  rewrite (K' Hk).
  apply: H_F_rec =>//.
  exact: IHk.
move/ltP: Hk; move/ltP: Hkn.
by move=> *; exfalso; omega.
Qed.

(** Let's apply the generic proof (for testing purposes). *)

Corollary TM_rec1_correct X0 X n :
  let err := TLrem prec (fun t => trec1 (F_rec X) (F0 t)) X0 X n in
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (trec1 (F_rec X0) (F0 X0) n) err) xf.
Proof. exact: (@i_validTM_TLrem XP_rec1). (* Rely on typeclass_instances *) Qed.

Corollary TM_rec1_correct' X0 X n :
  let err := Ztech prec (fun t => trec1 (F_rec X) (F0 t))
    (trec1 (F_rec X0) (F0 X0) n) F0 X0 X n in
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (trec1 (F_rec X0) (F0 X0) n) err) xf.
Proof. exact: (@i_validTM_Ztech XP_rec1). (* Rely on typeclass_instances *) Qed.

End rec1_correct.

Section rec2_correct.

Variable (XF1 : FullXR.T -> FullXR.T). (* 1st derivative *)
Variable (F1 : T -> T). (* evaluator for 1st derivative *)

Hypothesis XDn_1 : forall x, XDn 1 x = XF1 x.
Hypothesis F1_contains : I.extension XF1 F1.

Variable (XF_rec : FullXR.T -> FullXR.T -> FullXR.T -> nat -> FullXR.T).
Variable (F_rec : T -> T -> T -> nat -> T).
(* for the recurrence u(n) = F(arg, u(n-2), u(n-1), n) *)

Class extension3N := Extension3N :
  forall (ix iy iz : I.type) (x y z : ExtendedR) (n : nat),
  contains (I.convert ix) x ->
  contains (I.convert iy) y ->
  contains (I.convert iz) z ->
  contains (I.convert (F_rec ix iy iz n)) (XF_rec x y z n).
Context { H_F_rec : extension3N }.

Class compat_rec2 := Compat_rec2 :
  forall (r : FullXR.T) (k : nat),
  XF_rec r
  (XDn k r / Xreal (INR (fact k)))%XR
  (XDn k.+1 r / Xreal (INR (fact k.+1)))%XR
  k.+2 =
  (XDn k.+2 r / Xreal (INR (fact k.+2)))%XR.
Context { H_XF_rec : compat_rec2 }.

Definition IP_rec2 X0 := trec2 (F_rec X0) (F0 X0) (F1 X0).
Definition XP_rec2 xi0 := PolR.trec2 (XF_rec xi0) (xf xi0) (XF1 xi0).

Instance validXPoly_rec2 :
  validXPoly XP_rec2.
Proof.
constructor; first by move=> *; rewrite PolR.tsize_trec2.
move=> r n k Hkn.
move: n Hkn.
elim/nat_ind_gen : k => k Hk n Hkn.
case ck : k=> [|k'].
  rewrite PolR.trec2_spec0 /= XDn_0.
  case: (xf r) => // r0 /=.
  case C: (is_zero 1)=>//.
    by rewrite /is_zero (Req_bool_false _ _ R1_neq_R0) in C.
  by f_equal; field.
case ck' : k' => [|k''].
  rewrite /leq subSS -/(leq _ _) in Hkn.
  case cn: n => [|n'].
    by rewrite ck ck' cn ltnn // in Hkn.
  rewrite PolR.trec2_spec1 XDn_1.
  case (XF1 r)=> // r0 /=.
  case C: (is_zero 1).
    by rewrite /is_zero (Req_bool_false _ _ R1_neq_R0) in C.
  by f_equal; field.
rewrite ck ck' /leq subSS -/(leq _ _) in Hkn.
have K := @PolR.trec2_spec (XF_rec r) (xf r) (XF1 r) n k'' Hkn.
by rewrite K Hk =>//; [rewrite Hk // ck ck'|rewrite ck ck'].
Qed.

Instance validPoly_rec2 :
  validPoly XP_rec2 IP_rec2.
Proof.
constructor; first by move=> *; rewrite PolR.tsize_trec2 Pol.tsize_trec2.
move=> X0 r0 n k Hr0 Hkn.
move: n Hkn.
elim/nat_ind_gen : k => k Hk n Hkn.
case ck : k=> [|k'].
  rewrite trec2_spec0 PolR.trec2_spec0.
  exact: F0_contains.
case ck' : k' => [|k''].
  rewrite /leq subSS -/(leq _ _) in Hkn.
  case cn: n => [|n'].
    by rewrite ck ck' cn ltnn // in Hkn.
  rewrite PolR.trec2_spec1 trec2_spec1.
  exact: F1_contains.
rewrite ck ck' /leq subSS -/(leq _ _) in Hkn.
rewrite (@PolR.trec2_spec (XF_rec r0) (xf r0) (XF1 r0) n k'' Hkn).
rewrite (@trec2_spec (F_rec X0) (F0 X0) (F1 X0) n k'' Hkn).
by apply: H_F_rec=>//; apply: Hk; rewrite ?ck ?ck'//.
Qed.

(** Let's apply the generic proof (for testing purposes). *)

Corollary TM_rec2_correct X0 X n :
  let err := TLrem prec
    (fun t => trec2 (F_rec X) (F0 t) (F1 t)) X0 X n in
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (trec2 (F_rec X0) (F0 X0) (F1 X0) n) err) xf.
Proof. exact: (@i_validTM_TLrem XP_rec2). (* Rely on typeclass_instances *) Qed.

Corollary TM_rec2_correct' X0 X n :
  let err := Ztech prec (fun t i => trec2 (F_rec X) (F0 t) (F1 t) i)
    (trec2 (F_rec X0) (F0 X0) (F1 X0) n) F0 X0 X n in
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (trec2 (F_rec X0) (F0 X0) (F1 X0) n) err) xf.
Proof. exact: (@i_validTM_Ztech XP_rec2). (* Rely on typeclass_instances *) Qed.

End rec2_correct.
*)

End ProofOfRec.

Theorem TM_cst_correct (ci X0 X : I.type) (c : ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  contains (I.convert ci) c ->
  i_validTM (I.convert X0) (I.convert X) (TM_cst ci) (Xmask c).
Proof.
move=> Hsubset [t Ht] Hc.
split=>//=.
  move=> x Hx Nx; apply/eqNaiP; rewrite I.mask_propagate_r //.
  case: c Hc Nx; by [move/contains_Xnan|].
  case Eci: (I.convert ci) => [|rci].
    by rewrite I.mask_propagate_r.
  case Ec: c Hc => [|rc] Hc.
    by rewrite I.mask_propagate_r //; apply/contains_Xnan.
    change (Xreal 0%R) with (Xmask (Xreal 0%R) (Xreal rc)).
    apply: I.mask_correct =>//.
    exact: cont0.
move=> x0 Hx0.
case: c Hc => [|c]; first move/contains_Xnan; move => Hc.
exists (PolR.polyC 0%R); first by apply: Pol.polyC_correct; rewrite Hc.
  by move=> x Hx; rewrite I.mask_propagate_r.
exists (PolR.polyC c); first exact: Pol.polyC_correct.
move=> x Hx /=.
rewrite Xreal_sub Xreal_toR //=.
rewrite Rmult_0_l Rplus_0_l Rminus_diag_eq //.
change (Xreal 0) with (Xmask (Xreal 0) (Xreal c)).
apply: I.mask_correct =>//.
exact: cont0.
Qed.

Theorem TM_cst_correct_strong (ci X0 X : I.type) (f : ExtendedR -> ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  is_const f X ci ->
  i_validTM (I.convert X0) (I.convert X) (TM_cst ci) f.
Proof.
move=> Hsubset Hne [c H1 H2].
apply: TM_fun_eq; last apply: TM_cst_correct Hsubset Hne H1.
move=> x Hx /=; by rewrite H2.
Qed.

Lemma size_TM_cst c : Pol.size (approx (TM_cst c)) <= 1.
Proof. by rewrite /TM_cst Pol.polyCE Pol.size_polyCons Pol.size_polyNil. Qed.

(** Note/Erik: This definition could be simplified, removing parameter
    [n], just like [TM_cst]... *)
Definition TM_any (Y : I.type) (X : I.type) (n : nat) :=
  let pol := Pol.polyC (Imid Y) in
  {| approx := if n == 0 then pol
               else Pol.set_nth pol n Pol.Int.zero;
     error := I.mask (I.sub prec Y (Imid Y)) X
  (* which might be replaced with [I.sub prec Y (Imid Y)] *)
  |}.

Definition sizes := (Pol.size_polyNil, Pol.size_polyCons,
                     PolR.size_polyNil, PolR.size_polyCons,
                     Pol.size_set_nth, PolR.size_set_nth,
                     Pol.polyCE).

Lemma size_TM_any c X n : Pol.size (approx (TM_any c X n)) = n.+1.
Proof.
rewrite /TM_any /=.
case: n =>[|n] /=.
  by rewrite !sizes.
by rewrite Pol.size_set_nth !sizes maxnSS maxn0.
Qed.

Lemma Imask_IInan_r (Y X : I.type) :
  not_empty (I.convert Y) ->
  I.convert X = IInan -> I.convert (I.mask Y X) = IInan.
Proof.
move=> [v Hv] HX.
apply contains_Xnan.
have->: Xnan = Xmask (Xreal v) Xnan by [].
apply: I.mask_correct =>//.
by rewrite HX.
Qed.

Lemma Imask_IInan_l (Y X : I.type) :
  not_empty (I.convert X) ->
  I.convert Y = IInan -> I.convert (I.mask Y X) = IInan.
Proof.
move=> [v Hv] HX.
apply contains_Xnan.
have->: Xnan = Xmask Xnan (Xreal v) by [].
apply: I.mask_correct =>//.
by rewrite HX.
Qed.

Lemma anti_subset (X Y : interval) :
  I.subset_ X Y -> I.subset_ Y X -> X = Y.
Proof.
case: X; case: Y =>// a b c d.
case: a=>[|a]; case: b=>[|b]; case: c=>[|c]; case: d=>[|d] //= [H1 H2] [H3 H4];
  rewrite /le_lower /le_upper /Xneg in H1 H2 H3 H4; intuition;
  f_equal; by auto with real.
Qed.

Lemma Imask_contains (Y X : I.type) (y : ExtendedR) :
  not_empty (I.convert X) ->
  contains (I.convert Y) y -> contains (I.convert (I.mask Y X)) y.
Proof.
move=> [v Hv] Hy.
have->: y = Xmask y (Xreal v) by [].
exact: I.mask_correct.
Qed.

Theorem TM_any_correct
  (Y X0 X : I.type) (n : nat) (f : ExtendedR->ExtendedR) :
  not_empty (I.convert X0) -> I.subset_ (I.convert X0) (I.convert X) ->
  (forall x : R, contains (I.convert X) (Xreal x) ->
    contains (I.convert Y) (f (Xreal x))) ->
  i_validTM (I.convert X0) (I.convert X) (TM_any Y X n) f.
Proof.
move=> H0 Hsubset Hf.
have [x0' Hx0'] := H0.
have H'x0': X >: x0' by apply: subset_contains Hsubset _ _.
have Hrr := Hf _ H'x0'.
set r := proj_val (f (Xreal x0')).
have Hr : contains (I.convert Y) (Xreal r).
  exact: contains_Xreal.
split=>//.
  move=> x Hx Nx; apply/eqNaiP; rewrite /TM_any /=.
  rewrite I.mask_propagate_l // I.sub_propagate_l //.
  apply/contains_Xnan.
  have->: Xnan = f (Xreal x) by move: Nx; tac_def1 f.
  exact: Hf.
have Hr' := contains_not_empty _ _ Hr.
  have Hmid := not_empty_Imid Hr'.
  have [v Hv] := Hmid.
  rewrite /TM_any /=.
  case E: (I.convert X) =>[|l u] //.
    (* we could use Imask_IInan *)
    have->: Xreal 0 = Xmask (Xreal 0) (Xreal 0) by [].
    apply: I.mask_correct.
      eapply subset_sub_contains_0; first by eexact Hv.
      exact: Imid_subset.
    by rewrite E.
  have HX : exists x : ExtendedR, contains (I.convert X) x.
    have [w Hw] := H0.
    have Hw' := subset_contains _ _ Hsubset (Xreal w) Hw.
    by exists (Xreal w).
  have [H1 H2] := I.midpoint_correct X HX.
  suff->: Xreal 0 = Xmask (Xreal 0) (I.convert_bound (I.midpoint X)).
    apply: I.mask_correct=>//.
    eapply subset_sub_contains_0; first by eexact Hv.
    exact: Imid_subset.
  by rewrite H1.
move=> x0 Hx0.
set pol0 := PolR.polyC (proj_val (I.convert_bound (I.midpoint Y))).
set pol' := if n == 0 then pol0 else PolR.set_nth pol0 n 0%R.
exists pol'.
rewrite /pol' {pol'} /pol0 /TM_any /=.
+ case: ifP => H.
  apply: Pol.polyC_correct.
  apply: Xreal_Imid_contains.
  exact: contains_not_empty Hrr.
  apply: Pol.set_nth_correct.
  apply: Pol.polyC_correct.
  apply: Xreal_Imid_contains.
  exact: contains_not_empty Hrr.
  exact: cont0.
+ move=> x Hx /=.
  case Efx: (f (Xreal x)) => [|fx].
    rewrite I.mask_propagate_l // I.sub_propagate_l //.
    apply/contains_Xnan.
    rewrite -Efx; exact: Hf.
  have Dx : defined f x by rewrite /defined; rewrite Efx.
  rewrite Xreal_sub Xreal_toR //.
  step_xr (Xmask ((f (Xreal x) - Xreal (pol'.[(x - x0)%Re]))%XR) (Xreal x))=>//.
  apply: I.mask_correct =>//.
  apply: I.sub_correct; first exact: Hf.
  rewrite /pol' /pol0; case: ifP => H.
  rewrite PolR.horner_polyC.
  apply: Xreal_Imid_contains.
  exact: contains_not_empty Hrr.
  rewrite PolR.hornerE !sizes maxnSS maxn0.
  step_r ((pol0.[(x - x0)%Re]))%XR.
  rewrite PolR.horner_polyC.
  apply: Xreal_Imid_contains.
  exact: contains_not_empty Hrr.
  rewrite /pol0 (@PolR.hornerE_wide n.+1) ?sizes //.
  apply: eq_bigr => i _.
  congr Rmult.
  rewrite PolR.polyCE !(PolR.nth_polyCons, PolR.nth_set_nth).
  case: i => [//|i]; first by rewrite eq_sym H.
  by rewrite PolR.nth_polyNil if_same.
Qed.

Lemma size_TM_var X0 : Pol.size (approx (TM_var X0)) = 2.
Proof.
rewrite /TM_var Pol.size_set_nth
Pol.polyXE Pol.size_lift Pol.oneE Pol.polyCE.
by rewrite Pol.size_polyCons Pol.size_polyNil.
Qed.

Lemma TM_var_correct X0 X :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_var X0) (fun x => x).
Proof.
move=> Hsubs Hne.
split=>//; first exact: cont0.
move=> x0 Hx0 /=.
exists (PolR.set_nth PolR.polyX 0 x0).
  apply: Pol.set_nth_correct =>//.
  exact: Pol.polyX_correct.
move=> x Hx /=; rewrite Xreal_sub Xreal_toR //=.
rewrite Rmult_0_l Rplus_0_l Rmult_1_l.
step_r R0; [exact: cont0|ring].
Qed.

Theorem TM_var_correct_strong X0 X (f : ExtendedR -> ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  (forall x : R, contains (I.convert X) (Xreal x) -> f (Xreal x) = (Xreal x)) ->
  i_validTM (I.convert X0) (I.convert X) (TM_var X0) f.
Proof.
move=> Hsubset Hne Hid.
apply: TM_fun_eq; last apply: TM_var_correct Hsubset Hne.
by move=> *; rewrite /defined Hid.
Qed.

(*
Definition TM_var' X0 X (n : nat) :=
  let pol := Pol.tpolyCons X0 Pol.tpolyNil in
  if n == 0 then
  {| approx := pol; error := I.sub prec X X0 |}
  else
  {| approx := Pol.tset_nth pol n Pol.Int.tzero; error := Int.tzero |}.

Lemma size_TM_var' c X n : tsize (approx (TM_var' c X n)) = n.+1.
Proof.
rewrite /TM_var' /=.
case: n =>[|n] /=.
  by rewrite !sizes.
by rewrite tsize_set_nth !sizes maxnSS maxn0.
Qed.
*)

Lemma size_TM_power_int (p : Z) X0 X (n : nat) :
  Pol.size (approx (TM_power_int p X0 X n)) = n.+1.
Proof.
rewrite /= /T_power_int (@Pol.size_dotmuldiv (n.+1)) //.
by rewrite Pol.size_rec1.
by rewrite size_rec1up.
by rewrite size_rec1up.
Qed.

(*
Lemma tnth_pow_aux_rec (p : Z) (x : ExtendedR) n k :
  k <= n ->
  PolR.tnth
  (PolR.trec1 (TX.Rec.pow_aux_rec tt p x) (Xpower_int x p) n) k =
  if Z.ltb p Z0 || Z.geb p (Z.of_nat k) then
    Xpower_int x (p - Z.of_nat k)
  else Xmask (Xreal 0) x.
Proof.
elim: k => [|k IHk] Hkn.
  rewrite PolR.trec1_spec0 Z.sub_0_r.
  rewrite ifT //.
  by case: p.
move/(_ (ltnW Hkn)) in IHk.
move: IHk.
by rewrite PolR.trec1_spec.
Qed.

(*
Lemma Xpower_int_match (p : Z) (x : ExtendedR) :
  match x with
  | Xnan => Xpower_int x p = Xnan
  | Xreal r => ...
  end.
Proof.
*)

Lemma powerRZ_0_l (x : R) (p : Z) :
  x = R0 -> (p > 0)%Z -> powerRZ x p = R0.
Proof.
move=> Hx Hp.
case: p Hp =>[|p|p] Hp; rewrite // /powerRZ.
rewrite Hx pow_ne_zero //.
zify; omega.
Qed.

Inductive Xpower_int_spec (x : ExtendedR) (p : Z) : ExtendedR -> Type :=
  | Powint_nan of x = Xnan :
    Xpower_int_spec x p Xnan
  | Powint_neg of x = Xreal 0 & (p < 0)%Z :
    Xpower_int_spec x p Xnan
  | Powint_zero of x = Xreal 0 & (p = 0)%Z :
    Xpower_int_spec x p (Xreal 1)
  | Powint_pos of x = Xreal 0 & (p > 0)%Z :
    Xpower_int_spec x p (Xreal 0)
  | Powint_nz (r : R) of x = Xreal r & (r <> R0) :
    Xpower_int_spec x p (Xreal (powerRZ r p)).

Lemma Xpower_intP (x : ExtendedR) (p : Z) : Xpower_int_spec x p (Xpower_int x p).
Proof.
case: x=>/=; first exact: Powint_nan.
move=> r.
case: (Req_EM_T r R0) =>[Hr|Hr].
case: (Z_dec p 0) =>[[Hp|Hp]|Hp].
- rewrite Hr zeroT //.
  case: p Hp =>//.
  move=> *; exact: Powint_neg.
- case: p Hp =>//; move=> *.
  rewrite Hr pow_ne_zero; last by zify; omega.
  exact: Powint_pos.
- case: p Hp =>//; move=> *; apply: Powint_zero; by rewrite // Hr.
- case: p =>//; move=> *.
  by rewrite -(powerRZ_O r); apply: Powint_nz.
  exact: Powint_nz.
  rewrite zeroF //.
  exact: Powint_nz.
Qed.

Lemma bigXmul_Xreal_i n (g : 'I_n -> R) :
  \big[Xmul/Xreal 1]_(i < n) Xreal (g i) =
  Xreal (\big[Rmult/R1]_(i < n) g i).
Proof.
elim: n g =>[g|n IHn g]; first by rewrite 2!big_ord0.
by rewrite 2!big_ord_recr IHn.
Qed.
*)

Lemma TM_power_int_correct (p : Z) X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_power_int p X0 X n)
  (fun x => Xpower_int x p).
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_power_int tt p); last 2 first =>//.
exact: I.power_int_correct.
constructor.
- by move=> {n} ? n;
    rewrite ?(@PolR.size_dotmuldiv n.+1, @Pol.size_dotmuldiv n.+1,
    Pol.size_rec1, size_rec1up, PolR.size_rec1) //.
- { move=> x m k Hder Hk.
    rewrite /TR.T_power_int PolR.nth_dotmuldiv ifF; last first.
      rewrite PolR.size_rec1.
      rewrite size_falling_seq size_fact_seq.
      by rewrite !orbb ltnNge Hk.
    elim: k Hk => [|k IHk] Hk.
      simpl Derive_n; simpl INR; rewrite Rdiv_1.
      rewrite falling_seq_correct // fact_seq_correct //.
      rewrite big_mkord big_ord0.
      rewrite [PolR.nth _ _]nth_rec1up /= Rdiv_1 Rmult_1_l.
      rewrite /Xpower_int /toR_fun /proj_fun /powerRZ.
      case: p Hder =>// p Hp.
      have K: ~~ (is_zero x) by admit. (* TODO: power_int *)
      by rewrite (negbTE K).
    rewrite falling_seq_correct // fact_seq_correct //.
    admit. (* TODO: power_int *)
  }
constructor.
- by move=> {n} ? ? n;
    rewrite ?(@PolR.size_dotmuldiv n.+1, @Pol.size_dotmuldiv n.+1,
      Pol.size_rec1, size_rec1up, PolR.size_rec1) //.
- { move=> {X0 n Hsubset Hex} X0 x0 n Hx0.
    unfold T_power_int, TR.T_power_int.
    apply: Pol.dotmuldiv_correct.
    by rewrite size_falling_seq size_fact_seq.
    apply: Pol.rec1_correct =>//.
    + rewrite /pow_aux_rec /TR.pow_aux_rec; move=> _ _ m _.
      case: ifP => H.
      exact: R_power_int_correct.
      apply: R_mask_correct Hx0.
      exact: cont0.
    + exact: R_power_int_correct.
  }
- { move=> {X X0 n Hsubset Hex} X x Hx Dx n k Hk.
    rewrite /T_power_int.
    apply/eqNaiP.
    apply: Pol.dotmuldiv_propagate; last 1 first.
    rewrite (@Pol.size_dotmuldiv n.+1) //.
    by rewrite Pol.size_rec1.
    by rewrite size_falling_seq.
    by rewrite size_fact_seq.
    by rewrite Pol.size_rec1 size_falling_seq.
    by rewrite Pol.size_rec1 size_fact_seq.
    apply: Pol.rec1_propagate.
    move=> y m _.
    rewrite /pow_aux_rec ifT.
    apply/eqNaiP/contains_Xnan.
    have->: Xnan = Xpower_int^~ (p - Z.of_nat m)%Z (Xreal x).
    move: Dx; rewrite /defined /Xpower_int.
    admit. (* TODO: power_int *)
    exact: I.power_int_correct.
    admit. (* TODO: power_int *)
    apply/eqNaiP/contains_Xnan.
    have->: Xnan = Xpower_int^~ p (Xreal x).
    by move: Dx; tac_def1 Xpower_int.
    rewrite /defined in Dx.
    exact: I.power_int_correct.
  }
- move=> k x Hx.
  admit. (* TODO: power_int *)
Qed.

Lemma TM_inv_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_inv X0 X n) Xinv.
Proof.
move=> Hsubset Hex.
rewrite /TM_inv /T_inv /=.
admit. (*
apply TM_rec1_correct' with
  (XDn := (fun n x => ((- Xreal 1)^n * Xreal (INR (fact n)))
    * (Xmask (Xreal 1) x) / x^n.+1)%XR)
  (XF_rec := TX.Rec.inv_rec tt) =>//.
+ by move=> x; apply: nth_Xderive_pt_inv.
+ move=> x X1 HX1.
  exact: I.inv_correct.
+ move=> x0 x X1 X2 m HX1 HX2.
  rewrite /Rec.inv_rec.
  rewrite /TX.Rec.inv_rec.
  apply: I.div_correct =>//.
  exact: I.neg_correct.
move=> r k.
rewrite /TX.Rec.inv_rec.
rewrite !Xpow_idem !Xpow_Xreal.
case r =>[|rr] //.
rewrite !Xpow_Xreal /=.
destruct (Req_EM_T rr 0) as [e | e].
  by rewrite !zeroT //=; rewrite e; ring.
rewrite !zeroF /=.
+ rewrite !zeroF /=.
  - rewrite zeroF /=.
    f_equal.
    rewrite !plus_INR !mult_INR.
    field.
    split; first exact: pow_nonzero.
    split=>//.
    split.
      rewrite -mult_INR -plus_INR.
      change ((fact k + (k * fact k)%coq_nat)%coq_nat) with (fact k.+1).
      move=> H.
      case: (fact_neq_0 k.+1).
      exact: INR_eq.
    move=> H.
    case: (fact_neq_0 k).
    exact: INR_eq.
  exact: Ropp_neq_0_compat.
+ change ((fact k + (k * fact k)%coq_nat)%coq_nat) with (fact k.+1).
  move=> H.
  case: (fact_neq_0 k.+1).
  exact: INR_eq.
+ move=> H.
  case: (fact_neq_0 k).
  exact: INR_eq.
+ change (rr * (rr * rr ^ k))%Re with (rr ^ k.+2)%Re.
  exact: pow_nonzero.
change ((rr * rr ^ k))%Re with (rr ^ k.+1)%Re.
exact: pow_nonzero.
*)
Qed.

Lemma size_TM_inv X0 X (n : nat) : Pol.size (approx (TM_inv X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec1. Qed.

Lemma TM_exp_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_exp X0 X n) Xexp.
Proof.
move=> Hsubset Hex.
rewrite /TM_exp /T_exp /=.
admit.
(*
apply TM_rec1_correct' with
  (XDn := fun n x => Xexp x)
  (F_rec := fun _ => Rec.exp_rec prec)
  (XF_rec := fun _ => TX.Rec.exp_rec tt) =>//.
- by move=> ?; apply: nth_Xderive_pt_exp.
- by move=> x X1 HX1; apply: I.exp_correct.
- move=> x0 x X1 X2 m HX1 HX2.
  rewrite /Rec.exp_rec /TX.Rec.exp_rec.
  apply: I.div_correct =>//.
  rewrite /tnat.
  rewrite INR_IZR_INZ -Z2R_IZR.
  exact: I.fromZ_correct.
move=> r k.
rewrite /TX.Rec.exp_rec.
case Cex: (Xexp r) =>[//|re].
rewrite /Xdiv !(fact_zeroF) zeroF.
  congr Xreal.
  rewrite S_INR /= plus_INR mult_INR; field.
  split.
    rewrite -mult_INR -plus_INR.
    change ((fact k + (k * fact k)%coq_nat)%coq_nat) with (fact k.+1).
    move=> H.
    case: (fact_neq_0 k.+1).
    exact: INR_eq.
  split.
    move=> H.
    case: (fact_neq_0 k).
    exact: INR_eq.
  apply: Rgt_not_eq.
  change 1%Re with (INR 1).
  rewrite -plus_INR plusE.
  by apply: Rlt_gt; apply: lt_0_INR; apply/ltP; rewrite addn1.
by apply: Rgt_not_eq; apply: lt_0_INR; apply/ltP.
*)
Qed.

Lemma size_TM_exp X0 X (n : nat) : Pol.size (approx (TM_exp X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec1. Qed.

(*
Lemma PolR_size_dotmuldiv k a rec z :
  PolR.size
    (PolR.dotmuldiv tt (falling_seq a k) (behead (fact_seq k.+1))
    (PolR.rec1 rec z k)) = k.+1.
Proof.
rewrite (@PolR.size_dotmuldiv k.+1) //.
by rewrite PolR.size_rec1.
by rewrite size_rec1up.
by rewrite size_behead size_rec1up.
Qed.

Lemma PolI_size_dotmuldiv u k a rec z :
  Pol.size
    (Pol.dotmuldiv u (falling_seq a k) (behead (fact_seq k.+1))
    (Pol.rec1 rec z k)) = k.+1.
Proof.
rewrite (@Pol.size_dotmuldiv k.+1) //.
by rewrite Pol.size_rec1.
by rewrite size_rec1up.
by rewrite size_behead size_rec1up.
Qed.
*)

(*
Lemma aux_tnth_ln (x : R) n k :
  k < n ->
  is_positive x ->
  PolR.tnth
  (PolR.trec1 (TX.Rec.pow_aux_rec tt (-1) (Xreal x))
  (Xpower_int (Xreal x) (-1)) n.-1) k =
  Xpower_int (Xreal x) (- Z.of_nat k.+1).
Proof.
move=> Hk Hx.
rewrite tnth_pow_aux_rec; last by apply: ltn_leq_pred.
rewrite orTb; repeat f_equal.
by zify; auto with zarith.
Qed.
*)

Lemma Xreal_Rinv r :
  is_zero r = false ->
  Xreal (/ r) = Xpower_int (Xreal r) (-1).
Proof. by move=> Hr; rewrite /Xpower_int Hr /= Rmult_1_r. Qed.

Lemma TM_ln_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_ln X0 X n) Xln.
Proof.
move=> Hsubset [t Ht].
admit.
(*
eapply (i_validTM_Ztech
  (XDn :=
    (fun k x => if k isn't k'.+1 then Xln x else
      if x is Xreal r then
        if is_positive r then
          Xreal (\big[Rmult/R1]_(i < k') (Z2R (- Z.of_nat i.+1))) *
          Xpower_int (Xreal r) (- Z.of_nat k'.+1)%Z
        else Xnan
      else Xnan)%XR)); last by eexists; exact Ht.
6: done.
done.
red=> x; simpl.
apply nth_Xderive_pt_ln.
apply: I.ln_correct.

(* validXPoly *)
instantiate (1 := TX.T_ln tt).
split.
move=> x [ |k]; rewrite /TX.T_ln !sizes ?PolR_tsize_dotmuldiv //.
rewrite /T_ln /TX.T_ln.
move=> x n' k Hk.
rewrite PolR.tnth_polyCons; last first.
  case: n' Hk =>[ |n']; first by rewrite ltnS leqn0; move/eqP->.
  by rewrite ltnS => Hk; rewrite PolR_tsize_dotmuldiv.
case: k Hk =>[//|k Hk]; first by rewrite Xdiv_1_r.
rewrite ltnS in Hk.
rewrite -(subnKC Hk) /= -addnE.
have->: k + (n' - k.+1) = n'.-1 by rewrite -[in RHS](subnKC Hk) addSn.
have->: k.+1 + (n' - k.+1) = n'.-1.+1 by rewrite -[in RHS](subnKC Hk) addSn.
case: x =>[ |x] /=.
rewrite PolR.tnth_dotmuldiv.
case: k Hk =>[//|k Hk].
rewrite PolR.trec1_spec0 XmulC //.
rewrite PolR.trec1_spec.
rewrite /TX.Rec.pow_aux_rec XmulC //.
exact: ltn_leq_pred.
rewrite PolR_tsize_dotmuldiv.
exact: ltn_leq_pred.
case: is_positive_spec=> Hx.
rewrite /= zeroF; last by case: (is_positive_spec x) Hx =>//; auto with real.
rewrite PolR.tnth_dotmuldiv; last first.
rewrite PolR_tsize_dotmuldiv.
exact: ltn_leq_pred.
rewrite Rmult_1_r Xreal_Rinv; last first.
rewrite zeroF; case: (is_positive_spec x) Hx =>//; auto with real.
rewrite aux_tnth_ln.
rewrite [Xpower_int _ _]/=.
rewrite zeroF; last by case: (is_positive_spec x) Hx =>//; auto with real.
rewrite falling_seq_correct.
rewrite nth_behead.
rewrite fact_seq_correct.
rewrite !Xdiv_split.
rewrite !Xmul_assoc (Xmul_comm (Xinv _)).
rewrite -!Xmul_assoc; congr Xmul.
- rewrite [Z.sub]lock /= -lock; repeat f_equal.
  rewrite big_mkord.
  apply: (@big_ind2 _ _ (fun a b => IZR a = b)) =>//.
  by move=> a b c d <- <-; rewrite mult_IZR.
  move=> i _;   rewrite minus_IZR /=.
  rewrite Pos.of_nat_succ P2R_INR Nat2Pos.id // S_INR -INR_IZR_INZ.
  rewrite Ropp_plus_distr Rplus_comm.
  by auto with real.
- by repeat f_equal; rewrite INR_IZR_INZ; repeat f_equal.
exact: ltn_leq_pred.
exact: ltn_leq_pred.
done.
by rewrite /is_positive /Rlt_bool Rcompare_Lt.
rewrite PolR.tnth_dotmuldiv; last first.
by rewrite PolR_tsize_dotmuldiv; apply: ltn_leq_pred.
simpl.
case: is_zero =>//.
elim: k Hk =>[ |k IHk] Hk; first by rewrite PolR.trec1_spec0 XmulC.
rewrite PolR.trec1_spec //=; exact: ltn_leq_pred.

(* validPoly *)
split=> Y y m.
rewrite /TX.T_ln /T_ln sizes.
case: m =>[ |m]; first by rewrite !sizes.
by rewrite !sizes !PolR_tsize_dotmuldiv !PolI_tsize_dotmuldiv.
(* . *)
move=> k Hy Hk.
rewrite /TX.T_ln /T_ln.
rewrite ?(PolR.tnth_polyCons, tnth_polyCons); first last.
case: m Hk => [ |m]; first by rewrite ltnS leqn0; move/eqP->.
by move=> Hk; rewrite PolI_tsize_dotmuldiv.
case: m Hk => [ |m]; first by rewrite ltnS leqn0; move/eqP->.
by move=> Hk; rewrite PolR_tsize_dotmuldiv.
case: k Hk =>[ |k] Hk.
exact: I.ln_correct.
rewrite ltnS in Hk.
rewrite -(ltn_predK Hk).
rewrite ?(PolR.tnth_dotmuldiv,tnth_dotmuldiv); first last.
rewrite PolI_tsize_dotmuldiv; exact: ltn_leq_pred.
rewrite PolR_tsize_dotmuldiv; exact: ltn_leq_pred.
apply I.mul_correct.
apply I.div_correct; rewrite -Z2R_IZR; exact: I.fromZ_correct.
case: k Hk =>[ |k] Hk.
rewrite trec1_spec0 // PolR.trec1_spec0 //.
apply: I.power_int_correct.
apply: I.mask_correct =>//.
exact: I.ln_correct.
rewrite trec1_spec // ?PolR.trec1_spec //.
rewrite /Rec.pow_aux_rec /TX.Rec.pow_aux_rec.
rewrite orTb.
apply: I.power_int_correct.
apply: I.mask_correct =>//.
exact: I.ln_correct.
exact: ltn_leq_pred.
exact: ltn_leq_pred.
*)
Qed.

Lemma size_TM_ln X0 X (n : nat) : Pol.size (approx (TM_ln X0 X n)) = n.+1.
Proof.
rewrite /= /T_ln.
case: n => [|n]; first by rewrite !sizes.
rewrite sizes (@Pol.size_dotmuldiv n.+1) //.
by rewrite Pol.size_rec1.
by rewrite size_rec1up.
by rewrite size_behead size_rec1up.
Qed.

Definition is_not_empty X : bool :=
  match Xlower X, Xupper X with
  | Xnan, _ | _ , Xnan => true
  | Xreal l, Xreal u => Rle_bool l u
  end.

Lemma not_emptyP X : reflect (not_empty X) (is_not_empty X).
Proof.
apply: introP; rewrite /is_not_empty /not_empty; case: X => [|[|l][|u]]//=;
  move=> H.
by exists R0; split.
by exists R0; split.
by exists u; split; try apply: Rle_refl.
by exists l; split; try apply: Rle_refl.
exists l; split; try exact: Rle_refl.
by case: Rle_bool_spec H.
move=> [v Hv].
have Hlu := Rle_trans _ _ _ (proj1 Hv) (proj2 Hv).
case: Rle_bool_spec H =>//.
by move/Rlt_not_le.
Qed.

Lemma TM_sqrt_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_sqrt X0 X n) Xsqrt.
Proof.
move=> Hsubset [t Ht].
admit. (* TODO 
apply(*:*) (i_validTM_Ztech (P := TR.T_sqrt tt)) =>//; last by exists t.
- move=> r; case: Rlt_bool_spec => H1 H2; rewrite /defined /=.
  by rewrite negativeF //; apply: Rlt_le.
  by rewrite negativeT.
- move=> k r Hr.
  admit.
- clear; move=> X.
  pose b := is_not_empty X && Xgt0 X; case Eb : b; [left|right].
  admit. (* TODO / easy / automated ? *)
  admit. (* TODO / easy / automated ? *)
- exact: I.sqrt_correct.
- admit. (* TODO *)
- admit. (* TODO *)
*)
Qed.

(*
apply TM_rec1_correct' with
  (XDn := (fun (k : nat) (x : ExtendedR) =>
    (\big[Xmul/Xreal 1]_(i < k) Xreal (/ 2 - INR i) * (Xsqrt x / x ^ k))%XR))
  (XF_rec := TX.Rec.sqrt_rec tt)
=>//.
- by move=> x; apply: (nth_Xderive_pt_sqrt x).
- by move=> x X1 HX1; apply: I.sqrt_correct.
- move=> x0 x X1 X2 m HX1 HX2; rewrite /Rec.sqrt_rec /TX.Rec.sqrt_rec.
  by apply:I.div_correct=>//; apply: I.mul_correct =>//;
   [apply: I.sub_correct; try apply: I.mul_correct | apply: I.mul_correct| ];
   rewrite // /tnat INR_IZR_INZ -Z2R_IZR;
   apply: I.fromZ_correct.
move=> r k.
have h2n0 : (2 <> 0)%Re.
  move/Rlt_not_eq: Rlt_0_2 => // Hdiff Heq.
  by rewrite Heq in Hdiff.
rewrite /TX.Rec.sqrt_rec.
set b1 := \big[Xmul/Xreal 1]_(i < k) _.
set b2 := \big[Xmul/Xreal 1]_(i < k.+1) _.
set s := (_ - _)%XR.
have -> : b2 = (((Xreal (INR 1) - Xreal (INR 2) *
                  Xreal (INR k))/Xreal (INR 2)) * b1)%XR.
  rewrite /b2; rewrite big_ord_recr /= Xmul_comm.
  congr Xmul.
  by rewrite zeroF //; congr Xreal;field.
rewrite !Xdiv_split -!(Xmul_assoc s).
have -> : (s * Xinv (Xreal (INR 2)) * b1 = s * b1 *Xinv (Xreal (INR 2)))%XR.
  by rewrite Xmul_comm -Xmul_assoc; congr Xmul; rewrite Xmul_comm.
rewrite !Xmul_assoc;congr Xmul;congr Xmul.
rewrite (Xmul_comm (Xinv (Xreal (INR 2)))) !Xmul_assoc; congr Xmul.
case : r; first done.
move=> r.
case:(boolP (r == R0))=> /eqP r0.
  rewrite r0; clear b1 b2 s; case: k.
    rewrite /= (zeroF (R1_neq_R0)) Rinv_1 !Rmult_1_r !Xmul_1_l.
    by rewrite Rmult_0_r is_zero_correct_zero.
  move=> k; rewrite !Xpow_idem !Xpow_Xreal !pow_i; try apply/ltP => //=.
  by rewrite /Xinv is_zero_correct_zero.
have rk : forall k, (r ^ k)%Re <> R0.
  by move=> *; apply: pow_nonzero.
rewrite !Xmul_Xreal !Xpow_idem !Xpow_Xreal.
set i:= (INR 2 * (r * INR k.+1))%Re.
set fk1:= fact k.+1.
rewrite /= (zeroF (rk k)).
have : (INR 2 * r * INR k.+1)%Re <> R0.
  apply: Rmult_integral_contrapositive; split.
    by apply: Rmult_integral_contrapositive.
  exact: not_0_INR.
rewrite Rmult_assoc (zeroF (rk k.+1)).
rewrite /i;move/zeroF ->.
rewrite (zeroF (not_0_INR _ (fact_neq_0 k))).
rewrite /fk1 (zeroF (not_0_INR _ (fact_neq_0 k.+1))).
rewrite (zeroF h2n0) !Xmul_Xreal.
congr Xreal.
rewrite fact_simpl !mult_INR -(addn1 k) /=.
field.
by do !split =>//; apply: not_0_INR =>//; [apply: fact_neq_0 |rewrite addn1].

Qed.
*)

Lemma size_TM_sqrt X0 X (n : nat) : Pol.size (approx (TM_sqrt X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec1. Qed.

Ltac Inc :=
  rewrite (*?*) INR_IZR_INZ -Z2R_IZR;
  apply: I.fromZ_correct.

Lemma TM_invsqrt_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_invsqrt X0 X n)
            (fun x => Xinv (Xsqrt x)).
Proof.
move=> Hsubset Hex.
admit.
(*
apply TM_rec1_correct' with
  (XDn := (fun (k : nat) (x : ExtendedR) =>
    (\big[Xmul/Xreal 1]_(i < k) Xreal (-/2 - INR i)*(Xinv (Xsqrt x) / x^k))%XR))
  (XF_rec := TX.Rec.invsqrt_rec tt)
=>//.
- by move=> x; apply: nth_Xderive_pt_invsqrt.
- move=> x X1 HX1;rewrite /tinvsqrt.
  by apply: I.inv_correct; apply: I.sqrt_correct.
- move=> x0 x X1 X2 m HX1 HX2; rewrite /Rec.invsqrt_rec /TX.Rec.invsqrt_rec.
  apply:I.div_correct; apply:I.mul_correct=> //;try Inc.
    apply: I.neg_correct; apply:I.add_correct=> //; try Inc.
    by apply:I.mul_correct; Inc.
  by apply:I.mul_correct=>//; Inc.
move=> r k.
rewrite /TX.Rec.invsqrt_rec.
have -> : (k.+1.-1) = k by [].
set b := \big[Xmul/Xreal 1]_ _ _.
rewrite Xmul_comm !Xdiv_split big_ord_recr /b {b} !Xmul_assoc; congr Xmul.
rewrite 2!Xinv_Xmul_distr.
case: r => // r.
case: (boolP (is_negative r)); first by rewrite /=; move ->.
move/negbTE=> rpos.
have rge0: (0 <= r)%Re.
  move:rpos; rewrite /is_negative.
  case: (Rlt_bool_spec 0 r).
    by move => rpos Hf; apply:Rcompare_not_Gt_inv; rewrite (Rcompare_Lt _ _ rpos).
  case/Rle_lt_or_eq_dec; first by move/Rlt_bool_true ->.
  by move -> => _; apply:Rle_refl.
case:(boolP (r == R0))=> /eqP r0.
  by rewrite r0 !Xpow_idem /Xpow_iter iter_nat_S Xinv_Xmul_distr /Xinv !is_zero_correct_zero !(Xmul_comm _ Xnan).
rewrite /Xsqrt rpos.
case: (boolP (sqrt r == R0)).
  by move/eqP /(sqrt_eq_0 _ rge0) => re0; rewrite re0 in r0.
move/eqP=> sqrtn0.
have n_n0 i: INR i.+1 <> 0%Re by exact : not_0_INR.
have Hfact n0:INR (fact n0) <> 0%Re by exact: (not_0_INR _ (fact_neq_0 n0)).
have Hrk m : (r ^ m)%Re <> 0%Re by apply: pow_nonzero.
have Rm0 x1 x2 := (Rmult_integral_contrapositive_currified x1 x2).
rewrite -!Xinv_Xmul_distr !Xpow_idem !Xpow_Xreal !Xmul_Xreal.
have H2rk: (INR 2 * (r * INR k.+1))%Re <> R0.
  by apply: (Rm0);[| apply:(Rm0 r)]=>//; apply: not_0_INR.
have Hrk2: (sqrt r * (r ^ k.+1 * INR (fact k.+1)))%Re <> R0.
 by apply:(Rm0) => //; apply: (Rm0).
rewrite /Xinv !zeroF // !Xmul_Xreal; f_equal.
rewrite fact_simpl !mult_INR (S_INR k) -tech_pow_Rmult /= -(S_INR k).
by field; split =>//; split.
*)
Qed.

Lemma size_TM_invsqrt X0 X (n : nat) :
  Pol.size (approx (TM_invsqrt X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec1. Qed.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0 -> P 1 ->
  (forall k, P k -> P k.+1 -> P k.+2) ->
  forall k, P k.
Proof.
move=> H0 H1 Hind k.
suff : P k /\ P k.+1 by case.
elim: k => [|k [IHk0 IHk1]]; first by split.
split; by [|apply: Hind].
Qed.

Lemma TM_sin_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_sin X0 X n) Xsin.
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_sin tt); last 2 first =>//.
exact: I.sin_correct.
constructor.
- by move=> x m; rewrite /TR.T_sin PolR.size_rec2.
- move=> x m k Hx Hk; rewrite /TR.T_sin toR_toXreal.
  rewrite toR_toXreal in Hx.
  rewrite /PolR.nth /PolR.rec2; clear - Hk Hx.
  { move: k Hk; apply: nat_ind2.
    - by move=> _; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 0)) //= Rdiv_1.
    - move=> Hm; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 1)) //=.
      (* typical script: *)
      by rewrite Rdiv_1; symmetry; apply: is_derive_unique; auto_derive; auto with real.
    - move=> k Hk0 Hk1 Hm.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k.+2)) // nth_rec2upSS'.
      rewrite /TR.sin_rec in Hk0 Hk1 *.
      set F := (fun (a _ : FullR.T) (n : nat) => - a / (INR n * INR n.-1)) in Hk0 Hk1 *.
      have Hkm : k <= m by do 2![apply: ltnW].
      move/(_ Hkm) in Hk0.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k)) // in Hk0.
      rewrite Hk0 !Derive_nS; clear.
      rewrite [in RHS](Derive_n_ext _ (fun x => - sin x)); last first.
        move=> t; change (Derive (Derive sin) t) with (Derive_n sin 2 t).
        rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_sin _ _)) /= Rmult_1_r.
        by rewrite Ropp_mult_distr_l_reverse Rmult_1_l.
      rewrite Derive_n_opp.
      field_simplify;
        try (try repeat split; exact: INR_fact_neq_0 || exact: not_0_INR).
      congr Rdiv; rewrite 2!fact_simpl !mult_INR.
      by rewrite !Rmult_assoc Rmult_comm Rmult_assoc.
  }
constructor.
- by move=> x m k; rewrite /TR.T_sin Pol.size_rec2 PolR.size_rec2.
- by move=> Y x m Hx; apply: Pol.rec2_correct; first move=> ai bi a b l Ha Hb;
  repeat first [apply: R_div_correct|
                apply: R_neg_correct|
                apply: R_mul_correct|
                apply: R_from_nat_correct|
                apply: R_sin_correct|
                apply: R_cos_correct].
- move=> Y x Hx Dx m k Hk; rewrite /T_sin.
- done.
- move=> *; apply/ex_derive_n_is_derive_n/is_derive_n_sin.
Qed.

Lemma size_TM_sin X0 X (n : nat) : Pol.size (approx (TM_sin X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec2. Qed.

Lemma TM_cos_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_cos X0 X n) Xcos.
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_cos tt); last 2 first =>//.
exact: I.cos_correct.
constructor.
- by move=> x m; rewrite /TR.T_cos PolR.size_rec2.
- move=> x m k Hx Hk; rewrite /TR.T_cos toR_toXreal.
  rewrite toR_toXreal in Hx.
  rewrite /PolR.nth /PolR.rec2; clear - Hk Hx.
  { move: k Hk; apply: nat_ind2.
    - by move=> _; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 0)) //= Rdiv_1.
    - move=> Hm; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 1)) //=.
      (* typical script: *)
      by rewrite Rdiv_1; symmetry; apply: is_derive_unique; auto_derive; auto with real.
    - move=> k Hk0 Hk1 Hm.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k.+2)) // nth_rec2upSS'.
      rewrite /TR.cos_rec in Hk0 Hk1 *.
      set F := (fun (a _ : FullR.T) (n : nat) => - a / (INR n * INR n.-1)) in Hk0 Hk1 *.
      have Hkm : k <= m by do 2![apply: ltnW].
      move/(_ Hkm) in Hk0.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k)) // in Hk0.
      rewrite Hk0 !Derive_nS; clear.
      rewrite [in RHS](Derive_n_ext _ (fun x => - cos x)); last first.
        move=> t; change (Derive (Derive cos) t) with (Derive_n cos 2 t).
        rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_cos _ _)) /= Rmult_1_r.
        by rewrite Ropp_mult_distr_l_reverse Rmult_1_l.
      rewrite Derive_n_opp.
      field_simplify;
        try (try repeat split; exact: INR_fact_neq_0 || exact: not_0_INR).
      congr Rdiv; rewrite 2!fact_simpl !mult_INR.
      by rewrite !Rmult_assoc Rmult_comm Rmult_assoc.
  }
constructor.
- by move=> x m k; rewrite /TR.T_cos Pol.size_rec2 PolR.size_rec2.
- by move=> Y x m Hx; apply: Pol.rec2_correct; first move=> ai bi a b l Ha Hb;
  repeat first [apply: R_div_correct|
                apply: R_neg_correct|
                apply: R_mul_correct|
                apply: R_from_nat_correct|
                apply: R_sin_correct|
                apply: R_cos_correct].
- done.
- move=> *; apply/ex_derive_n_is_derive_n/is_derive_n_cos.
Qed.

Lemma size_TM_cos X0 X (n : nat) : Pol.size (approx (TM_cos X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec2. Qed.

Lemma size_TM_tan X0 X (n : nat) : Pol.size (approx (TM_tan X0 X n)) = n.+1.
Proof. by rewrite Pol.size_grec1. Qed.

Lemma size_TM_atan X0 X (n : nat) : Pol.size (approx (TM_atan X0 X n)) = n.+1.
Proof. by rewrite Pol.size_grec1. Qed.

Lemma TM_atan_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_atan X0 X n) Xatan.
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_atan tt); last 2 first =>//.
exact: I.atan_correct.
constructor.
- by move=> ? ?; rewrite PolR.size_grec1.
- { move=> {X0 X n Hsubset Hex} x n k Hdef H;
    rewrite /TR.T_atan /PolR.nth /PolR.grec1
      (nth_grec1up_indep _ _ _ _ _ 0%R (m2 := k)) //
      nth_grec1up_last.
    case: k H => [|k H]; first by rewrite /= ?Rdiv_1.
    rewrite last_grec1up // head_gloop1.
    rewrite [size _]/= subn1 [_.+1.-1]/=.
    elim: k H x {Hdef} (* Erik: is this clear really necessary? *) =>[|k IHk] H x.
    + rewrite /= Rmult_0_l Rplus_0_l Rmult_1_r Rdiv_1.
      symmetry; apply: is_derive_unique; auto_derive =>//.
      by rewrite Rmult_1_r.
    + move/ltnW in H; move/(_ H) in IHk.
      rewrite [INR]lock [PolR.lift]lock [fact]lock /= -!lock.
      set qk := iteri k
        (fun i c => PolR.div_mixed_r tt _ (INR (i + 1).+1)) PolR.one in IHk *.
      rewrite (@Derive_ext _
        (fun x => PolR.horner tt qk x / (1+x*x) ^ (k+1) * INR (fact k.+1))%R);
        first last.
      move=> t; move/(_ t) in IHk; rewrite -pow_powerRZ in IHk.
      simpl_R.
      apply: (@Rmult_eq_reg_r ri0); first rewrite -IHk // Rmult_assoc Hri0; try lra.
      by rewrite -Hr0; apply: INR_fact_neq_0.
      apply: Rinv_r_neq0 (Hri0 _).
      by rewrite -Hr0; apply: INR_fact_neq_0.
      clear IHk.
      rewrite PolR.horner_div_mixed_r PolR.horner_sub PolR.horner_add.
      rewrite PolR.horner_mul_mixed !PolR.horner_lift Derive_scal_l.
      rewrite Derive_div; first last.
      * by apply: pow_nonzero; apply: Rsqr_plus1_neq0.
      * by auto_derive.
      * exact: PolR.ex_derive_horner.
      rewrite Derive_pow; try by auto_derive.
      rewrite Derive_plus; try by auto_derive.
      rewrite Derive_const ?Rplus_0_l.
      rewrite Derive_mult; try by auto_derive.
      rewrite Derive_id.
      rewrite PolR.Derive_horner.
      rewrite -{1}(Rmult_1_r (qk^`().[x])) -Rmult_plus_distr_l.
      rewrite SuccNat2Pos.id_succ.
      rewrite -addnE addn1 Rmult_1_r Rmult_1_l; simpl predn.
      (* Now, some reals' bookkeeping *)
      suff->: forall x, x * INR (fact k.+1) / INR (fact k.+2) = x / INR k.+2.
      suff->: INR (k.+1).*2 = (2 * INR k.+1)%R.
      suff->: (((1 + x * x) ^ k.+1) ^ 2 = (1 + x * x) ^ k.+2 * (1 + x * x) ^ k)%R.
      suff->: (((1 + x * x) ^ k.+1) = (1 + x ^ 2) * (1 + x * x) ^ k)%R.
      * by field_simplify; first apply: Rdiv_eq_reg; first ring;
        repeat first [ split
                     | apply: Rmult_neq0
                     | apply: not_0_INR
                     | apply: pow_nonzero
                     | apply: Rsqr_plus1_neq0].
      * by rewrite !pow_S pow_O Rmult_1_r.
      * by rewrite -pow_mult multE muln2 -pow_add plusE addSnnS -addnn.
      * by rewrite -mul2n -multE mult_INR.
      * clear; move=> x; apply: Rdiv_eq_reg.
        - by rewrite [in RHS]fact_simpl mult_INR; lra.
        - exact: INR_fact_neq_0.
        - exact: not_0_INR.
  }
constructor.
- by move=> *; rewrite PolR.size_grec1 Pol.size_grec1.
- { move => {X0 X n Hsubset Hex} X0 xi0 n Hx.
    apply: Pol.grec1_correct =>//.
    + move=> qi q m Hq.
      by repeat first [apply: Pol.div_mixed_r_correct|
                       apply: Pol.sub_correct|
                       apply: Pol.add_correct|
                       apply: Pol.deriv_correct|
                       apply: Pol.lift_correct|
                       apply: Pol.mul_mixed_correct|
                       apply: R_from_nat_correct].
    + move=> qi q m Hq.
      by repeat first [apply: R_div_correct|
                       apply: R_power_int_correct|
                       apply: Pol.horner_correct|
                       apply: R_add_correct|
                       apply: R_sqr_correct|
                       apply: I.fromZ_correct|
                       apply: Pol.one_correct].
    + exact: Pol.one_correct.
    + move=> [/=|k]; last by rewrite /PolR.nth !nth_default //; apply: cont0.
      exact: R_atan_correct.
  }
- done.
- by move=> *; apply: ex_derive_n_atan.
Qed.

(*
  (XDn :=
    (fun k x => if k isn't k'.+1 then Xatan x else
      if x is Xreal r then
        Xreal (1 / (1 + x ^ 2))
      else Xnan)%XR)); last by eexists; exact Ht.
6: done.
done.
red=> x; simpl.
apply nth_Xderive_pt_ln.
apply: I.ln_correct.

(* validXPoly *)
instantiate (1 := TX.T_ln tt).
split.
move=> x [ |k]; rewrite /TX.T_ln !sizes ?PolR_tsize_dotmuldiv //.
rewrite /T_ln /TX.T_ln.
move=> x n' k Hk.
rewrite PolR.tnth_polyCons; last first.
  case: n' Hk =>[ |n']; first by rewrite ltnS leqn0; move/eqP->.
  by rewrite ltnS => Hk; rewrite PolR_tsize_dotmuldiv.
case: k Hk =>[//|k Hk]; first by rewrite Xdiv_1_r.
rewrite ltnS in Hk.
rewrite -(subnKC Hk) /= -addnE.
have->: k + (n' - k.+1) = n'.-1 by rewrite -[in RHS](subnKC Hk) addSn.
have->: k.+1 + (n' - k.+1) = n'.-1.+1 by rewrite -[in RHS](subnKC Hk) addSn.
case: x =>[ |x] /=.
rewrite PolR.tnth_dotmuldiv.
case: k Hk =>[//|k Hk].
rewrite PolR.trec1_spec0 XmulC //.
rewrite PolR.trec1_spec.
rewrite /TX.Rec.pow_aux_rec XmulC //.
exact: ltn_leq_pred.
rewrite PolR_tsize_dotmuldiv.
exact: ltn_leq_pred.
case: is_positive_spec=> Hx.
rewrite /= zeroF; last by case: (is_positive_spec x) Hx =>//; auto with real.
rewrite PolR.tnth_dotmuldiv; last first.
rewrite PolR_tsize_dotmuldiv.
exact: ltn_leq_pred.
rewrite Rmult_1_r Xreal_Rinv; last first.
rewrite zeroF; case: (is_positive_spec x) Hx =>//; auto with real.
rewrite aux_tnth_ln.
rewrite [Xpower_int _ _]/=.
rewrite zeroF; last by case: (is_positive_spec x) Hx =>//; auto with real.
rewrite falling_seq_correct.
rewrite nth_behead.
rewrite fact_seq_correct.
rewrite !Xdiv_split.
rewrite !Xmul_assoc (Xmul_comm (Xinv _)).
rewrite -!Xmul_assoc; congr Xmul.
- rewrite [Z.sub]lock /= -lock; repeat f_equal.
  rewrite big_mkord.
  apply: (@big_ind2 _ _ (fun a b => IZR a = b)) =>//.
  by move=> a b c d <- <-; rewrite mult_IZR.
  move=> i _;   rewrite minus_IZR /=.
  rewrite Pos.of_nat_succ P2R_INR Nat2Pos.id // S_INR -INR_IZR_INZ.
  rewrite Ropp_plus_distr Rplus_comm.
  by auto with real.
- by repeat f_equal; rewrite INR_IZR_INZ; repeat f_equal.
exact: ltn_leq_pred.
exact: ltn_leq_pred.
done.
by rewrite /is_positive /Rlt_bool Rcompare_Lt.
rewrite PolR.tnth_dotmuldiv; last first.
by rewrite PolR_tsize_dotmuldiv; apply: ltn_leq_pred.
simpl.
case: is_zero =>//.
elim: k Hk =>[ |k IHk] Hk; first by rewrite PolR.trec1_spec0 XmulC.
rewrite PolR.trec1_spec //=; exact: ltn_leq_pred.

(* validPoly *)
split=> Y y m.
rewrite /TX.T_ln /T_ln sizes.
case: m =>[ |m]; first by rewrite !sizes.
by rewrite !sizes !PolR_tsize_dotmuldiv !PolI_tsize_dotmuldiv.
(* . *)
move=> k Hy Hk.
rewrite /TX.T_ln /T_ln.
rewrite ?(PolR.tnth_polyCons, tnth_polyCons); first last.
case: m Hk => [ |m]; first by rewrite ltnS leqn0; move/eqP->.
by move=> Hk; rewrite PolI_tsize_dotmuldiv.
case: m Hk => [ |m]; first by rewrite ltnS leqn0; move/eqP->.
by move=> Hk; rewrite PolR_tsize_dotmuldiv.
case: k Hk =>[ |k] Hk.
exact: I.ln_correct.
rewrite ltnS in Hk.
rewrite -(ltn_predK Hk).
rewrite ?(PolR.tnth_dotmuldiv,tnth_dotmuldiv); first last.
rewrite PolI_tsize_dotmuldiv; exact: ltn_leq_pred.
rewrite PolR_tsize_dotmuldiv; exact: ltn_leq_pred.
apply I.mul_correct.
apply I.div_correct; rewrite -Z2R_IZR; exact: I.fromZ_correct.
case: k Hk =>[ |k] Hk.
rewrite trec1_spec0 // PolR.trec1_spec0 //.
apply: I.power_int_correct.
apply: I.mask_correct =>//.
exact: I.ln_correct.
rewrite trec1_spec // ?PolR.trec1_spec //.
rewrite /Rec.pow_aux_rec /TX.Rec.pow_aux_rec.
rewrite orTb.
apply: I.power_int_correct.
apply: I.mask_correct =>//.
exact: I.ln_correct.
exact: ltn_leq_pred.
exact: ltn_leq_pred.
*)

(* **************************************************************** *)

Local Notation "a + b" := (Xadd a b).
Local Notation "a - b" := (Xsub a b).

Lemma Xneg_Xadd (a b : ExtendedR) : Xneg (Xadd a b) = Xadd (Xneg a) (Xneg b).
Proof. by case: a; case b => * //=; f_equal; ring. Qed.

Lemma TM_add_correct_gen
  (smallX0 : interval) (X : I.type) (TMf TMg : rpa) f g :
  I.subset_ smallX0 (I.convert X) ->
  i_validTM smallX0 (I.convert X) TMf f ->
  i_validTM smallX0 (I.convert X) TMg g ->
  i_validTM smallX0 (I.convert X) (TM_add TMf TMg)
  (fun xr => Xadd (f xr) (g xr)).
Proof.
move=> HinX [Hdf Hef H0 Hf] [Hdg Heg _ Hg].
admit. (* TODO
split=>//=.
  move=> x Hx /andP [Df Dg].
  by move: (Hdf x Hx Df) (Hdg x Hx Dg); tac_def2 f g.
  step_xr (Xreal 0 + Xreal 0); by [apply: I.add_correct|rewrite /= Rplus_0_l].
move=> x0 Hx0 /=.
case Dfg0 : andb.
  have /andP [Df0 Dg0] := Dfg0.
  move: (Hf x0 Hx0) (Hg x0 Hx0); rewrite Df0 Dg0.
  move => [pf Hf1 Hf2] [pg Hg1 Hg2].
  exists (PolR.add tt pf pg); first exact: Pol.add_correct.
move=> x Hx /=.
case Dfg : andb.
  have /andP [Df Dg] := Dfg.
rewrite PolR.horner_add.
rewrite Xreal_sub Xreal_toR // ?Xreal_add; last first.
  by move: (Hdf x Hx Df) (Hdg x Hx Dg); tac_def2 f g.
set fx := f _; set gx := g _; set pfx := _ (pf.[_]); set pgx := _ (pg.[_]).
have->: (fx + gx - (pfx + pgx) = (fx - pfx) + (gx - pgx))%XR.
  rewrite /fx /gx /pfx /pgx -(Xreal_toR (Hdf x Hx Df)) -(Xreal_toR (Hdg x Hx Dg)) /=.
  congr Xreal; ring.
rewrite /fx /gx /pfx /pgx -(Xreal_toR (Hdf x Hx Df)) -(Xreal_toR (Hdg x Hx Dg)) /=.
apply: R_add_correct.
by have := Hf2 x Hx; rewrite Df.
by have := Hg2 x Hx; rewrite Dg.
move/negbT in Dfg.
rewrite negb_and in Dfg.
have /orP [nDf|nDg] := Dfg.
have := Hf2 x Hx; rewrite (negbTE nDf) /TM_add /= => /eqNaiP H.
by apply/eqNaiP; rewrite I.add_propagate_l.
have := Hg2 x Hx; rewrite (negbTE nDg) /TM_add /= => /eqNaiP H.
by apply/eqNaiP; rewrite I.add_propagate_r.

move/negbT in Dfg0.
rewrite negb_and in Dfg0.
have /orP [nDf|nDg] := Dfg0.
have := Hf x0 Hx0; rewrite (negbTE nDf) /TM_add /= => /eqNaiP H.
by apply/eqNaiP; rewrite I.add_propagate_l.
have := Hg x0 Hx0; rewrite (negbTE nDg) /TM_add /= => /eqNaiP H.
by apply/eqNaiP; rewrite I.add_propagate_r.
*)
Qed.

Lemma TM_add_correct (X0 X : I.type) (TMf TMg : rpa) f g :
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X) (TM_add TMf TMg)
  (fun xr => Xadd (f xr) (g xr)).
Proof.
move=> Hf Hg.
case Hf => [Df _ H0 _].
exact: TM_add_correct_gen.
Qed.

Lemma TM_opp_correct (X0 X : interval) (TMf : rpa) f :
  i_validTM X0 X TMf f ->
  i_validTM X0 X (TM_opp TMf)
  (fun xr => Xneg (f xr)).
Proof.
move=> [Hdef Hsubset Hzero /= Hmain].
admit. (* TODO
split=>//.
  by move=> x Hx Dx; move: (Hdef x Hx Dx); tac_def1 f.
  rewrite -Ropp_0 Xreal_neg.
  exact: I.neg_correct.
simpl=> x0 Hx0.
case Df0 : df.
move/(_ x0 Hx0) in Hmain.
rewrite Df0 in Hmain.
have [Q H1 H2] := Hmain.
exists (PolR.opp Q); first exact: Pol.opp_correct.
move=> x Hx.
case Df : df.
move/(_ x Hx) in H2.
rewrite Df in H2.
rewrite PolR.horner_opp.
set g := Xreal (toR_fun _ _ - - _)%R.
suff->: g = Xreal (Ropp ((toR_fun f x) - (Q.[(x - x0)%Re]))%R) by exact: R_neg_correct.
rewrite /g !(Xreal_sub, Xreal_toR, Xreal_neg) //.
by rewrite !(Xsub_split, Xneg_involutive, Xneg_Xadd).
by rewrite Hdef.
by move: (Hdef x Hx Df); tac_def1 f.
move/(_ x Hx): H2; rewrite Df; move/eqNaiP => H2.
apply/eqNaiP; by rewrite I.neg_propagate.
move/(_ x0 Hx0): Hmain; rewrite Df0; move/eqNaiP => ?.
apply/eqNaiP; by rewrite I.neg_propagate.
*)
Qed.

Lemma TM_sub_correct (X0 X : interval) (TMf TMg : rpa) f g :
  i_validTM X0 X TMf f ->
  i_validTM X0 X TMg g ->
  i_validTM X0 X (TM_sub TMf TMg)
  (fun xr => Xsub (f xr) (g xr)).
Proof.
move=> [Hdf Hzero1 Hsubset1 /= Hf] [Hdg Hzero2 _ /= Hg].
admit. (* TODO
split=>//=.
  move=> x Hx /andP [Df Dg].
  by move: (Hdf x Hx Df) (Hdg x Hx Dg); tac_def2 f g.
  suff->: Xreal 0 = (Xreal 0 - Xreal 0)%XR by apply: I.sub_correct.
  by rewrite /= Rminus_0_r.
move=> x0 Hx0 /=.
case Dfg0 : andb.
  have /andP [Df0 Dg0] := Dfg0.
  move: (Hf x0 Hx0) (Hg x0 Hx0); rewrite Df0 Dg0.
  move => [pf Hf1 Hf2] [pg Hg1 Hg2].
  exists (PolR.sub tt pf pg); first exact: Pol.sub_correct.
move=> x Hx /=.
case Dfg : andb.
  have /andP [Df Dg] := Dfg.
rewrite PolR.horner_sub.
rewrite Xreal_sub Xreal_toR // ?(Xreal_add, Xreal_neg); last first.
  by move: (Hdf x Hx Df) (Hdg x Hx Dg); tac_def2 f g.
set fx := f _; set gx := g _; set pfx := _ (pf.[_]); set pgx := _ (pg.[_]).
have->: (fx - gx - (pfx + (- pgx)) = (fx - pfx) - (gx - pgx))%XR.
  rewrite /fx /gx /pfx /pgx.
  rewrite -(Xreal_toR (Hdf x Hx Df)) -(Xreal_toR (Hdg x Hx Dg)) /=.
  congr Xreal; ring.
rewrite /fx /gx /pfx /pgx.
rewrite -(Xreal_toR (Hdf x Hx Df)) -(Xreal_toR (Hdg x Hx Dg)) /=.
apply: R_sub_correct.
by have := Hf2 x Hx; rewrite Df.
by have := Hg2 x Hx; rewrite Dg.
move/negbT in Dfg.
rewrite negb_and in Dfg.
have /orP [nDf|nDg] := Dfg.
have := Hf2 x Hx; rewrite (negbTE nDf) /TM_add /= => /eqNaiP H.
by apply/eqNaiP; rewrite I.sub_propagate_l.
have := Hg2 x Hx; rewrite (negbTE nDg) /TM_add /= => /eqNaiP H.
by apply/eqNaiP; rewrite I.sub_propagate_r.

move/negbT in Dfg0.
rewrite negb_and in Dfg0.
have /orP [nDf|nDg] := Dfg0.
have := Hf x0 Hx0; rewrite (negbTE nDf) /TM_add /= => /eqNaiP H.
by apply/eqNaiP; rewrite I.sub_propagate_l.
have := Hg x0 Hx0; rewrite (negbTE nDg) /TM_add /= => /eqNaiP H.
by apply/eqNaiP; rewrite I.sub_propagate_r.
*)
Qed.

(* TO REMOVE

Definition TM_mul_mixed (a : I.type) (M : rpa) (X0 X : I.type) : rpa :=
  RPA (MapI.tpolymap (I.mul prec a) (approx M))
      (I.add prec
             (I.mul prec
                    (I.sub prec a (Imid a)) (* will often be [0, 0] *)
                    (horner prec (approx M) (I.sub prec X X0))
             (* (ComputeBound M X0 X) *) )
             (I.mul prec a (error M))).
*)

Definition TM_mul_mixed (a : I.type) (M : rpa) : rpa :=
  RPA (Pol.map (I.mul prec a) (approx M))
      (I.mul prec a (error M)).

Definition TM_div_mixed_r (M : rpa) (b : I.type) : rpa :=
  RPA (Pol.map (I.div prec ^~ b) (approx M))
      (I.div prec (error M) b).

Lemma size_TM_mul_mixed a M :
  Pol.size (approx (TM_mul_mixed a M)) = Pol.size (approx M).
Proof. by rewrite Pol.size_map. Qed.

Lemma size_TM_div_mixed_r M b :
  Pol.size (approx (TM_div_mixed_r M b)) = Pol.size (approx M).
Proof. by rewrite Pol.size_map. Qed.

Lemma Xdiv_0_r x : Xdiv x (Xreal 0) = Xnan.
Proof. by rewrite /Xdiv; case: x=>// r; rewrite zeroT. Qed.

Let TM_div_mixed_r_aux0 M b X0 X f :
  contains (I.convert b) (Xreal R0) ->
  i_validTM (I.convert X0) (I.convert X) M f (* hyp maybe too strong *) ->
  i_validTM (I.convert X0) (I.convert X) (TM_div_mixed_r M b)
  (fun x => Xdiv (f x) (Xreal R0)).
Proof.
move=> Hzero [H0 Hss /= Hmain].
have Lem : contains (I.convert (error (TM_div_mixed_r M b))) Xnan.
  rewrite /TM_div_mixed_r.
  simpl.
  rewrite -(Xdiv_0_r (Xreal R0)).
  exact: I.div_correct.
admit.
(* TODO
split=>//.
   by move=> x Hx /= /andP => [[]]; rewrite eqxx.
   by rewrite (proj1 (contains_Xnan _) Lem).
move=> /= x0 Hx0; rewrite ifF; first exact/eqNaiP/contains_Xnan.
by rewrite eqxx andbF.
*)
Qed.

Lemma TM_mul_mixed_correct a M X0 X f (y : R) :
  contains (I.convert a) (Xreal y) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul_mixed a M)
  (fun x => Xmul (Xreal y) (f x)).
Proof.
move=> Hy [Hdef H0 Hss Hmain].
admit. (* TODO 
split=>//.
  by move=> x Hx Dx; move: (Hdef x Hx); tac_def1 f.
  have->: (Xreal 0) = (Xmul (Xreal y) (Xreal 0)) by simpl; congr Xreal; ring.
  exact: I.mul_correct.
move=> /= x0 Hx0.
case Df0 : df.
move/(_ x0 Hx0) in Hmain.
rewrite Df0 in Hmain.
have [q H1 H2] := Hmain.
exists (PolR.map (Rmult y) q).
- apply: Pol.map_correct =>//.
  by rewrite Rmult_0_r.
  by move=> *; apply: R_mul_correct.
- move=> x Hx.
  case Df : df.
  move/(_ x Hx) in H2.
  rewrite Df in H2.
  rewrite PolR.horner_mul_mixed.
  set g := Xreal (toR_fun _ _ - _)%R.
  suff->: g = Xreal (Rmult y (toR_fun f x - (q.[(x - x0)]))%R).
    exact: R_mul_correct =>//.
  rewrite /g !(Xreal_mul, Xreal_sub, Xreal_toR, Xreal_neg) //.
  case: (f) =>[//|r] /=; congr Xreal; ring.
by rewrite Hdef.
by move: (Hdef x Hx Df); tac_def1 f.
move/negbT in Df.
have := H2 x Hx; rewrite (negbTE Df) =>/eqNaiP H.
by apply/eqNaiP; rewrite I.mul_propagate_r.
move/negbT in Df0.
have := Hmain x0 Hx0; rewrite (negbTE Df0) =>/eqNaiP H.
by apply/eqNaiP; rewrite I.mul_propagate_r.
*)
Qed.

Lemma TM_mul_mixed_nai a M f X0 X :
  contains (I.convert a) Xnan ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  I.convert (error (TM_mul_mixed a M)) = IInan.
Proof.
move/contains_Xnan => Ha /=.
case=>[Hnan Hsubst Hmain].
by rewrite I.mul_propagate_l.
Qed.

Corollary TM_mul_mixed_correct_strong a M X0 X f g :
  not_empty (I.convert X0) ->
  is_const f X a ->
  i_validTM (I.convert X0) (I.convert X) M g ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul_mixed a M)
  (fun x => Xmul (f x) (g x)).
Proof.
move=> tHt [[|y] Hy1 Hy2] Hg; move: (Hg) => [Hdef Hnan Hsubset Hmain].
admit.
(* TODO
split=>//.

move=> x Hx /andP [Df Dg].
by move: Df (Hdef x Hx Dg); tac_def2 f g.
by rewrite (TM_mul_mixed_nai Hy1 Hg).
move=> /= x0 Hx0.
case D0 : andb.
  have /andP [Df0 Dg'0] := D0.
  have Dg0 : defined g x0 by rewrite Hdef//; apply: subset_contains Hsubset _ _.
  move/(_ x0 Hx0) in Hmain.
  rewrite Dg'0 in Hmain.
  have [q H1 H2] := Hmain.
  exists (PolR.map (Rmult (* dummy *) R0) q).
    apply: Pol.map_correct =>//.
    by rewrite Rmult_0_r.
    move=> *; apply: R_mul_correct =>//.
    by move/contains_Xnan: Hy1 =>->.
  move=> x Hx /=.
  case D : andb.
  have /andP [Df Dg'] := D.
    move/(_ x Hx) in H2.
    rewrite Dg' in H2.
    rewrite I.mul_propagate_l //.
    exact/contains_Xnan.
  exact/eqNaiP/I.mul_propagate_l/contains_Xnan.
exact/eqNaiP/I.mul_propagate_l/contains_Xnan.
apply: TM_fun_eq; last exact: TM_mul_mixed_correct Hy1 Hg.
move=> x Hx /=.
suff->: defined f x = true by [].
by move: (Hy2 x Hx); tac_def1 f.
by move=> x Hx /=; rewrite Hy2.
*)
admit.
Qed.

Lemma not_empty_Imid_ex2 (X : I.type) :
  not_empty (I.convert X) ->
  exists2 y : R, contains (I.convert (Imid X)) (Xreal y)
                 & contains (I.convert X) (Xreal y).
Proof.
move=> H; move: (H) => [x Hx].
have [H1 H2] := I.midpoint_correct X (ex_intro _ (Xreal x) Hx).
suff [[|z] Hz1 Hz2] : exists2 z : ExtendedR,
  contains (I.convert (Imid X)) z & contains (I.convert X) z.
  exists R0; rewrite (proj1 (contains_Xnan _) Hz1) // || rewrite (proj1 (contains_Xnan _) Hz2) //.
  by exists z.
exists (I.convert_bound (I.midpoint X)) =>//.
exact: Imid_contains.
Qed.

Lemma TM_div_mixed_r_correct M b X0 X f (y : R) :
  contains (I.convert b) (Xreal y) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  i_validTM (I.convert X0) (I.convert X) (TM_div_mixed_r M b)
  (fun x => Xdiv (f x) (Xreal y)).
Proof.
have [->|Hy0] := Req_dec y R0.
  exact: TM_div_mixed_r_aux0.
move=> Hy [Hdef H0 Hss Hmain].
admit.
(* TODO
split=>//.
  move=> x Hx /andP [Df Dy].
  by move: (Hdef x Hx Df); rewrite /defined; case: (f) =>//=; rewrite zeroF.
  have->: (Xreal 0) = (Xdiv (Xreal 0) (Xreal y)).
  simpl.
  rewrite zeroF //.
  by simpl; congr Xreal; rewrite /Rdiv Rmult_0_l.
  exact: I.div_correct.
move=> /= x0 Hx0.
case D1f0 : andb.
have /andP [Df0 Dy] := D1f0.
move/(_ x0 Hx0) in Hmain; rewrite Df0 in Hmain.
have [q H1 H2] := Hmain.
exists (PolR.map (Rdiv ^~ y) q).
- apply: Pol.map_correct =>//.
  by rewrite /Rdiv Rmult_0_l.
  by move=> *; apply: R_div_correct.
- move=> x Hx /=.
  case D1f : andb.
  have /andP [Df _] := D1f.
  move/(_ x Hx) in H2.
  rewrite Df in H2.
  clear - H2 Hy Hy0 D1f Df Hdef Hx.
  set sub2 := Xreal (Rminus _ _).
  set sub1 := Xreal (Rminus _ _) in H2.
  suff->: sub2 = Xdiv sub1 (Xreal y) by exact: I.div_correct.
  rewrite /sub1 /sub2 !(Xreal_sub, Xreal_toR) //.
  rewrite !(Xsub_split, Xdiv_split) Xmul_Xadd_distr_r; congr Xadd.
  by rewrite PolR.horner_div_mixed_r Xreal_div // Xdiv_split Xmul_Xneg_distr_l.
  by rewrite Hdef.
  by move: (Hdef x Hx Df); tac_def1 f =>//=; rewrite zeroF.
- apply/eqNaiP.
  move/negbT in D1f; rewrite negb_and in D1f.
  have /orP [nDf|nDy] := D1f.
  rewrite I.div_propagate_l //.
  by move/(_ x Hx): H2; rewrite (negbTE nDf) => /eqNaiP ->.
  by rewrite Dy in nDy.
- apply/eqNaiP.
  move/negbT in D1f0; rewrite negb_and in D1f0.
  have /orP [nDf0|nDy] := D1f0.
  rewrite I.div_propagate_l //.
  by move/(_ x0 Hx0): Hmain; rewrite (negbTE nDf0) => /eqNaiP ->.
  by move/eqrP: Hy0 nDy => ->.
*)
Qed.

Lemma TM_div_mixed_r_nai M b f X0 X :
  contains (I.convert b) Xnan ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  I.convert (error (TM_div_mixed_r M b)) = IInan.
Proof.
move/contains_Xnan => Ha /=.
case=>[Hdef Hnan Hsubst Hmain].
exact: I.div_propagate_r.
Qed.

Corollary TM_div_mixed_r_correct_strong M b X0 X f g :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  is_const g X b ->
  i_validTM (I.convert X0) (I.convert X) (TM_div_mixed_r M b)
  (fun x => Xdiv (f x) (g x)).
Proof.
move=> tHt Hf [[|y] Hy1 Hy2]; move: (Hf) => [Hdef Hnan Hsubset Hmain].
admit.
(* TODO
split=>//=.
  move=> x Hx /andP [Df Dg].
  by move: (Hdef x Hx Df) Dg; rewrite /Xinv;
    tac_def2 f g =>//= r r0; case: is_zero_spec.
  by rewrite (TM_div_mixed_r_nai Hy1 Hf).
move=> /= x0 Hx0.
case D20 : andb.
  have /andP [Df0 Dg0] := D20.
  move/(_ x0 Hx0) in Hmain.
  rewrite Df0 in Hmain.
  have [q H1 H2] := Hmain.
  exists (PolR.map (Rdiv ^~ R0) q).
    apply: Pol.map_correct =>//.
    by rewrite /Rdiv Rmult_0_l.
    move=> *; apply: R_div_correct =>//.
    by move/contains_Xnan: Hy1 =>->.
  move=> x Hx /=.
  case D2 : andb.
    have /andP [Df Dg] := D2.
    move/(_ x Hx) in H2.
    rewrite Df in H2.
    rewrite I.div_propagate_r //.
    exact/contains_Xnan.
  exact/eqNaiP/I.div_propagate_r/contains_Xnan.
exact/eqNaiP/I.div_propagate_r/contains_Xnan.
apply: (@TM_fun_eq (fun x => f x / Xreal y)%XR _ (predI df (fun _ : R => y != 0%Re))).
- move=> x Hx /=; congr andb; rewrite /defined Hy2 //=.
  by case: is_zero_spec => /eqP // ->.
- by move=> x Hx; rewrite Hy2.
- exact: TM_div_mixed_r_correct.
*)
admit.
Qed.

Definition mul_error prec n (f g : rpa) X0 X :=
 let pf := approx f in
 let pg := approx g in
 let sx := (I.sub prec X X0) in
 let B := I.mul prec (Bnd.ComputeBound prec (Pol.mul_tail prec n pf pg) sx)
                (I.power_int prec sx (Z_of_nat n.+1)) in
 let Bf := Bnd.ComputeBound prec pf sx in
 let Bg := Bnd.ComputeBound prec pg sx in
   I.add prec B (I.add prec (I.mul prec (error f) Bg)
     (I.add prec (I.mul prec (error g) Bf)
       (I.mul prec (error f) (error g)))).

Definition TM_mul (Mf Mg : rpa) X0 X n : rpa :=
 RPA (Pol.mul_trunc prec n (approx Mf) (approx Mg))
     (mul_error prec n Mf Mg X0 X).

(*
Lemma horner_poly_nan k p x :
  k < PolR.tsize p -> PolR.tnth p k = Xnan ->
  PolR.horner tt p x = Xnan.
Proof.
move=> Hk Heq.
elim/PolR.tpoly_ind: p k Hk Heq =>[|a p IHp] k Hk Heq.
  by rewrite PolR.tsize_polyNil in Hk.
rewrite PolR.tsize_polyCons in Hk.
case ck: k => [|k']; rewrite ck in IHp Heq.
  rewrite PolR.tnth_polyCons // in Heq.
  by rewrite PolR.horner_polyCons Heq Xadd_comm.
rewrite ck /= in Hk.
rewrite -(addn1 k') -(addn1 (PolR.tsize p)) ltn_add2r in Hk.
rewrite PolR.tnth_polyCons // in Heq.
by rewrite PolR.horner_polyCons (IHp k').
Qed.
*)

Lemma poly_mul n (a b : nat -> R) (x : R) :
  (forall i, n < i -> (a i = R0)/\ (b i = R0))->
  \big[Rplus/R0]_(k < (n + n).+1)
    \big[Rplus/R0]_(i < k.+1) (a i * b (k - i)%N * x ^ k)%Re =
  \big[Rplus/R0]_(i < n.+1)
    \big[Rplus/R0]_(j < n.+1) (a i * b j * x ^ (i + j))%Re.
Proof.
move=> Habn.
rewrite pair_big.
rewrite (eq_bigr (fun (k : 'I_(n + n).+1)=>
        \big[Rplus/0%Re]_(i < (n + n).+1 | i < k.+1)
           (a i * b (k - i)%N * x ^ k)%Re)); last first.
  move=> [k Hk0] _ /=.
  pose F := (fun i => (a i * b (k - i)%N * x ^ k)%Re).
  by apply:(@big_ord_widen R R0 Rplus _ (n + n).+1 F Hk0).
rewrite pair_big_dep /=.
set s := \big[Rplus/0%Re]_p _.
rewrite (bigID (fun (p: 'I_(n+n).+1 * 'I_(n+n).+1) => p.2 < n+1)) /=.
set t := \big[Rplus/0%Re]_(i | _) _.
rewrite big1; last first.
  move=> i /andP; case => _; rewrite - leqNgt; rewrite addn1 => Hi2.
  by case:(Habn i.2 Hi2) => -> _; rewrite !Rmult_0_l.
rewrite Rplus_0_r /t {t}.
rewrite (bigID (fun (p: 'I_(n+n).+1 * 'I_(n+n).+1) => p.1- p.2 < n+1)) /=.
set t := \big[Rplus/0%Re]_(i | _) _.
rewrite big1; last first.
  move=> i /andP; case => _; rewrite - leqNgt; rewrite addn1 => Hi2.
  by case:(Habn (i.1 - i.2)%N Hi2) => _ ->; rewrite Rmult_0_r Rmult_0_l.
rewrite Rplus_0_r /s {s}.
have H : forall (i j : 'I_n.+1), (i + j)%N < (n + n).+1.
  by move=>[i Hi][j Hj] /=; have := leq_add Hi Hj; rewrite !addSn !addnS ltnS.
have H1 : forall i : 'I_n.+1, i < (n + n).+1.
  move=> [i Hi] /=.
  apply:(@leq_trans n.+1 i.+1 (n + n).+1 Hi).
  by rewrite -addnS -{1}(addn0 n) ltn_add2l.
pose h :=(fun (p:'I_n.+1 * 'I_n.+1)=>(Ordinal (H p.1 p.2),Ordinal (H1 p.1))).
rewrite /t.
have Hmin : forall i, minn i n < n.+1 by move=> i; rewrite ltnS geq_minr.
have Hjmi i j : (i + j - i)%N = j by rewrite -{2}(addn0 i) subnDl subn0.
pose h' := (fun (p : 'I_(n + n).+1 * 'I_(n + n).+1) =>
             (Ordinal (Hmin p.2), Ordinal (Hmin (p.1 - p.2)%N))).
have hh': forall i, h' (h i) = i.
  move=> [[i Hi] [j Hj]]; apply/ pair_eqP; rewrite /h /h' /=.
  apply/andP; split; apply/eqP; apply:ord_inj => /=.
    by apply/minn_idPl; rewrite -ltnS.
  by rewrite Hjmi; apply/minn_idPl; rewrite -ltnS.
rewrite (reindex_onto h h')/=; last first.
  move=>[[ i Hi] [j Hj]]=>/=.
  case/andP; case/andP => Hji Hjn Himj.
  apply/pair_eqP; rewrite /h /h' /=.
  have minjn k : k < n + 1 -> minn k n = k.
    by move=> Hjm; apply/minn_idPl; rewrite -ltnS -(addn1 n).
  by apply/andP;split;
   apply/eqP; apply:ord_inj=> /=; rewrite !minjn ?subnKC.
apply:eq_big=> i.
  rewrite hh' eqxx /= andbT.
  case: i => [[i Hi] [j Hj]] /=.
  rewrite addn1 Hi andbT /= Hjmi Hj.
  by rewrite -addnS -{1}(addn0 i) ltn_add2l.
by do !case/andP=> *; rewrite Hjmi.
Qed.

Lemma Xreal_inj : injective Xreal.
Proof. by move=> x y []. Qed.

Lemma TM_mul_correct_gen
  (smallX0 : interval) (TMf TMg : rpa) f g (X0 X : I.type) n :
  I.subset_ smallX0 (I.convert X0) ->
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty smallX0 ->
  i_validTM smallX0 (I.convert X) TMf f ->
  i_validTM smallX0 (I.convert X) TMg g ->
  i_validTM smallX0 (I.convert X) (TM_mul TMf TMg X0 X n.-1)
  (fun xr => Xmul (f xr) (g xr)).
Proof.
move=> HinX0 HinX [t Ht'] [Hdf Hef H0 Hf] [Hdg Heg _ Hg].
have Ht0 : X0 >: t by apply: (subset_contains smallX0).
have Ht : X >: t by apply: subset_contains Ht'.
have Hf0 := Hf t Ht'.
have Hg0 := Hg t Ht'.
admit.
(* TODO
split =>//.
by move=> x Hx /andP [Dfx Dgx]; move: (Hdf x Hx Dfx) (Hdg x Hx Dgx); tac_def2 f g.
  case Df0: (df t); case Dg0: (dg t); rewrite Df0 in Hf0; rewrite Dg0 in Hg0.
    have [qf Hf1 Hf2] := Hf0.
    have [qg Hg1 Hg2] := Hg0.
    step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
    apply: R_add_correct.
    apply: (mul_0_contains_0_r _
      (y := (Xreal (PolR.horner tt (PolR.mul_tail tt n.-1 qf qg) (t - t)%R))));
      last first.
      apply: pow_contains_0 =>//.
      exact: subset_sub_contains_0 Ht0 _.
    apply: Bnd.ComputeBound_correct.
    exact: Pol.mul_tail_correct.
    exact: R_sub_correct.
    step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
    apply: R_add_correct.
    apply: (mul_0_contains_0_l _
      (y := (Xreal (PolR.horner tt qg (t - t)%R)))) =>//.
    apply: Bnd.ComputeBound_correct=>//.
    exact: R_sub_correct.
    step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
    apply: R_add_correct.
    apply: (mul_0_contains_0_l _
      (y := (Xreal (PolR.horner tt qf (t - t)%R)))) =>//.
    apply: Bnd.ComputeBound_correct=>//.
    exact: R_sub_correct.
  exact: (mul_0_contains_0_l _ (*!*) (y := Xreal 0)).
rewrite /= /mul_error; rewrite 3?I.add_propagate_r //.
by rewrite I.mul_propagate_r //; apply/eqNaiP.
rewrite /= /mul_error; rewrite 3?I.add_propagate_r //.
by rewrite I.mul_propagate_l //; apply/eqNaiP.
rewrite /= /mul_error; rewrite 3?I.add_propagate_r //.
by rewrite I.mul_propagate_l //; apply/eqNaiP.
move=> x0 Hx0 {Hf0 Hg0} /=.
have Hf0 := Hf x0 Hx0; have Hg0 := Hg x0 Hx0.
case D0: andb.
have /andP [Df0 Dg0] := D0.
rewrite Df0 in Hf0; rewrite Dg0 in Hg0.
have [pf Hf1 Hf2] := Hf0.
have [pg Hg1 Hg2] := Hg0.
exists (PolR.mul_trunc tt n.-1 pf pg); first exact: Pol.mul_trunc_correct.
move=> x Hx; rewrite [(predI _ _) _]/=.
case D2 : andb.
have /andP [Df Dg] := D2.
move/(_ x Hx) in Hf2; move/(_ x Hx) in Hg2.
rewrite Df in Hf2; rewrite Dg in Hg2.
step_r ((PolR.mul_tail tt n.-1 pf pg).[x - x0] * (x - x0)^n.-1.+1 +
  (((toR_fun f x - pf.[x - x0]) * pg.[x - x0] +
  ((toR_fun g x - pg.[x - x0]) * pf.[x - x0] +
  (toR_fun f x - pf.[x - x0]) * (toR_fun g x - pg.[x - x0])))))%R.
  apply: R_add_correct.
    apply: R_mul_correct.
      apply: Bnd.ComputeBound_correct.
        exact: Pol.mul_tail_correct.
      apply: R_sub_correct =>//; exact: (subset_contains smallX0).
      rewrite pow_powerRZ; apply: R_power_int_correct.
      apply: R_sub_correct=>//; exact: (subset_contains smallX0).
    apply: R_add_correct.
    apply: R_mul_correct =>//.
    apply: Bnd.ComputeBound_correct =>//.
    by apply: R_sub_correct =>//; apply: (subset_contains smallX0).
  apply: R_add_correct.
    apply: R_mul_correct =>//.
    apply: Bnd.ComputeBound_correct =>//.
    by apply: R_sub_correct =>//; apply: (subset_contains smallX0).
  exact: R_mul_correct.
clear - Hdf Hdg Df Dg Hx.
have Hdfx := Hdf x Hx Df.
have Hdgx := Hdg x Hx Dg.
set sf := pf.[x - x0]%R.
set sg := pg.[x - x0]%R.
(****************)
rewrite !PolR.hornerE PolR.size_mul_trunc PolR.size_mul_tail.
rewrite (big_endo (fun r => r * (x-x0) ^ n.-1.+1)%R); first last.
  by rewrite Rmult_0_l.
  by move=> a b /=; rewrite Rmult_plus_distr_r.
rewrite (eq_big_nat _ _ (F2 := fun i =>
  PolR.mul_coeff tt pf pg (i + n.-1.+1) * (x - x0) ^ (i + n.-1.+1))%R);
  last first.
  move=> i Hi; rewrite Rmult_assoc; congr Rmult; last by rewrite pow_add.
  rewrite PolR.nth_mul_tail ifF; first by rewrite addnC.
  by case/andP: Hi; case: leqP.
rewrite -(big_addn 0 _ n.-1.+1 predT (fun i =>
  PolR.mul_coeff tt pf pg i * (x - x0) ^ i)%R).
set e := ((_ f x - sf) * sg + ((_ g x - sg) * sf + (_ f x - sf) * (_ g x - sg)))%R.
rewrite Rplus_comm.
have->: e = ((toR_fun (fun xr => (f xr * g xr))%XR x) - sf * sg)%R.
(* begin flip-flop *)
apply/Xreal_inj.
rewrite ![in RHS](Xreal_sub, Xreal_mul, Xreal_toR);
  last by move: Hdfx Hdgx; tac_def2 f g.
rewrite -![in RHS](Xreal_sub, Xreal_mul, Xreal_toR) // /e.
congr Xreal; ring.
(* end flip-flop *)
rewrite Rplus_assoc; congr Rplus.
rewrite {}/e {}/sf {}/sg.
rewrite !PolR.hornerE.
rewrite big_addn.

(* apply: (Rplus_eq_reg_r (toR_fun (fun xr => (f xr * g xr))%XR x)).
case cn : n => [|n'] /=.

apply/Xreal_inj; rewrite !(Xreal_add, Xreal_sub, Xreal_mul).
  rewrite !Xreal_toR; first last.
  move: (Hdf x Hx Df); by tac_def1 f.
  move: (Hdg x Hx Dg); by tac_def1 g.
  move: (Hdf x Hx Df) (Hdg x Hx Dg); by tac_def2 f g.
  simpl.
  *)

  admit. admit. admit.
  (*
  rewrite cn in Heq.
  rewrite -/n cn in Hf1.
  rewrite -Heq in Hg1.
  rewrite /sf /sg (@tpolyNil_size0 pf) // (@tpolyNil_size0 pg) //.
  rewrite PolR.horner_polyNil cxx0 /=.
  have Htail : PolR.tsize (PolR.tmul_tail tt 0 PolR.tpolyNil PolR.tpolyNil) = 0.
    by rewrite PolR.tsize_mul_tail PolR.tsize_polyNil //=.
  rewrite (@tpolyNil_size0 _ Htail) PolR.horner_polyNil.
  rewrite PolR.is_horner /=.
  rewrite PolR.tsize_mul_trunc
    /=.
  rewrite big_ord_recr /= big_ord0 PolR.tmul_trunc_nth //.
  rewrite big_ord_recr big_ord0 /= subnn.
  rewrite PolR.tnth_polyNil /=.
  case (f x) => [|rf] //=.
  case (g x) => [|rg] //=.
  by f_equal; ring.
(**************** finished polyNil ****************)
rewrite 2!PolR.is_horner /=.
rewrite PolR.tsize_mul_trunc PolR.tsize_mul_tail /=.
 have ->:
\big[Xadd/Xreal 0]_(i < n'.+1) (PolR.tnth (PolR.tmul_trunc tt n' pf pg) i *
                                 Xreal rxx0 ^ i)%XR =
 \big[Xadd/Xreal 0]_(k < n'.+1)
  (\big[Xadd/Xreal 0]_(i < k.+1) ((PolR.tnth pf i) * (PolR.tnth pg (k - i))) *
                                 Xreal rxx0 ^ k)%XR.
  apply: eq_bigr => i _.
  by f_equal; rewrite PolR.tmul_trunc_nth.
have ->:
(\big[Xadd/Xreal 0]_(i < (PolR.tsize pf).-1 + (PolR.tsize pg).-1 - n')
 (PolR.tnth (PolR.tmul_tail tt n' pf pg) i * Xreal rxx0 ^ i))%XR =
(\big[Xadd/Xreal 0]_(k < (PolR.tsize pf).-1 + (PolR.tsize pg).-1 - n')
(\big[Xadd/Xreal 0]_(i < (k+n'.+1).+1)
   ((PolR.tnth pf (i)) * (PolR.tnth pg ((k+n'.+1) - i))) * Xreal rxx0 ^ k))%XR.
  by apply: eq_bigr => i _; f_equal; rewrite PolR.tmul_tail_nth.
rewrite cn in Heq.
rewrite -/n cn in Hf1.
rewrite -Heq in Hg1.
rewrite Hf1 Hg1 /=.
case ctr : (\big[Xadd/Xreal 0]_(k < n'.+1)
  (\big[Xadd/Xreal 0]_(i < k.+1) (PolR.tnth pf i * PolR.tnth pg (k - i)) *
                                 Xreal rxx0 ^ k))%XR => [|rtr].
  case:(bigXadd_Xnan ctr) => [j Hj].
  have Hj' :
  \big[Xadd/Xreal 0]_(i < j.+1) (PolR.tnth pf i * PolR.tnth pg (j - i))%XR
   = Xnan.
    case c1 :
    (\big[Xadd/Xreal 0]_(i < j.+1) (PolR.tnth pf i * PolR.tnth pg (j - i))%XR).
      by [].
    by rewrite c1 Xpow_idem Xpow_Xreal /= in Hj.
  have [i Hi] :=(bigXadd_Xnan Hj').
  clear ctr Hj Hj'.
  have H2 : (PolR.tnth pf i = Xnan) \/ (PolR.tnth pg (j - i) = Xnan).
    case c1 : (PolR.tnth pf i) => [|ri]; first by left.
    case c2 : (PolR.tnth pg (j-i)) => [|rj]; first by right.
    by rewrite c1 c2 /= in Hi.
  case: H2 => [H2|H2].
    have H1 : PolR.horner tt pf (x - x0) = Xnan.
      apply: (@horner_poly_nan i) =>//.
      by rewrite Hf1; apply: (@leq_trans j.+1).
    rewrite /sf H1.
    have H' : forall a, (a - Xnan)%XR = Xnan by case.
    rewrite 2!H' /=; clear H'.
    have H' : forall a, (a + Xnan)%XR = Xnan by case.
    by rewrite H'.
  have H1 : PolR.horner tt pg (x - x0) = Xnan.
    apply: (@horner_poly_nan (j - i)%N) =>//.
    rewrite Hg1; apply: (@leq_trans j.+1) =>//.
    exact: leq_subr.
  rewrite /sg H1.
  have H' : forall a, (a - Xnan)%XR = Xnan by case.
  rewrite 2!H' /=; clear H'.
  have H' : forall a, (a + Xnan)%XR = Xnan by case.
  by rewrite H'.
have [G HG] := (bigXadd_Xreal1 ctr).
have Hf : forall i : 'I_n'.+1, PolR.tnth pf i <> Xnan /\ PolR.tnth pg i <> Xnan.
  move=> i.
  move/(_ i) in HG.
  have H1 : exists r,
   (\big[Xadd/Xreal 0]_(i0 < i.+1) (PolR.tnth pf i0 * PolR.tnth pg (i - i0)))%XR
    = Xreal r.
    case c1 :
    (\big[Xadd/Xreal 0]_(i0 < i.+1) (PolR.tnth pf i0 * PolR.tnth pg (i - i0))%XR)
    => [|rc1].
      by rewrite c1 in HG.
    by exists rc1.
  have [r1 Hr1]:= H1; have [gi0 Hi0]:= bigXadd_Xreal1 Hr1.
  have Hif := Hi0 ord_max.
  case cf : (PolR.tnth pf (@ord_max i)) => [|rf].
    by rewrite cf /= in Hif.
  have Hig := Hi0 ord0.
  case cg : (PolR.tnth pg (@ord_max i)) => [|r].
    by rewrite subn0 cg Xmul_comm /= in Hig.
  by split.
have Hn : forall k, k < n'.+1 \/ n'.+1 <= k.
  move=> k.
  have [H1 | H2]: (k < n'.+1 \/ n' < k)%coq_nat by omega.
    by left; apply/ltP.
  by right; apply/ltP.
have Hfr : exists rf, forall i, PolR.tnth pf i = Xreal (rf i).
  apply: not_Xnan_Xreal_fun.
  move=> i; case: (Hn i) => [H |H].
    by case:(Hf (Ordinal H)).
  by rewrite PolR.tnth_out ?Hf1.
have Hgr : exists rg, forall i, PolR.tnth pg i = Xreal (rg i).
  apply: not_Xnan_Xreal_fun.
  move=> i; case:(Hn i) => [H| H].
    by case: (Hf (Ordinal H)).
  by rewrite PolR.tnth_out ?Hg1.
clear Hf.
case: Hfr => [rf Hrf].
case: Hgr => [rg Hrg].
have H1 : sf = Xreal (\big[Rplus/R0]_(i < n'.+1) (rf i * rxx0^i)%Re).
  rewrite /sf is_horner_pos Hf1 //.
  have -> : \big[Xadd/Xreal 0]_(i < n'.+1) (PolR.tnth pf i * (x - x0) ^ i)%XR =
   \big[Xadd/Xreal 0]_(i < n'.+1) Xreal (rf i * rxx0^i)%Re.
    by apply: eq_bigr=> i _; rewrite cxx0 Hrf Xpow_idem Xpow_Xreal.
  by rewrite bigXadd_Xreal_i.
have H2 : sg = Xreal (\big[Rplus/R0]_(i < n'.+1) (rg i * rxx0^i)%Re).
  rewrite /sg is_horner_pos Hg1 //.
  have -> : \big[Xadd/Xreal 0]_(i < n'.+1) (PolR.tnth pg i * (x - x0) ^ i)%XR =
   \big[Xadd/Xreal 0]_(i < n'.+1) Xreal (rg i * rxx0^i)%Re.
    by apply: eq_bigr=> i _; rewrite cxx0 Hrg Xpow_idem Xpow_Xreal.
  by rewrite bigXadd_Xreal_i.

have H3 : (\big[Xadd/Xreal 0]_(k < n'.+1)
  (\big[Xadd/Xreal 0]_(i < k.+1) (PolR.tnth pf i * PolR.tnth pg (k - i)) *
                                 Xreal rxx0 ^ k))%XR =
 Xreal (\big[Rplus/R0]_(k < n'.+1)
  (\big[Rplus/R0]_(i < k.+1) (rf i *
  rg (k - i)%nat * rxx0 ^ k))%Re).
  rewrite -bigXadd_Xreal_i.
  apply: eq_bigr => k _.
  rewrite -bigXadd_Xreal_i.
  rewrite Xpow_idem Xpow_Xreal big_Xmul_Xadd_distr.
  apply: eq_bigr => i _.
  by rewrite Hrf Hrg /=.
have H4 :
(\big[Xadd/Xreal 0]_(k < n' + n' - n') (\big[Xadd/Xreal 0]_(i < (k+n'.+1).+1)
                                        (PolR.tnth pf (i) *
                                         PolR.tnth pg ((k+n'.+1)- i)) *
                                        Xreal rxx0 ^ k)%XR =
Xreal (\big[Rplus/R0]_(k < n') (\big[Rplus/R0]_(i < (k+n'.+1).+1)
                                         (rf (i)%nat *
   rg ((k+n'.+1) - i)%nat * rxx0 ^ k))%Re)).
  rewrite -bigXadd_Xreal_i.
  have->: (n' + n' - n')%nat = n' by rewrite addKn.
  apply: eq_bigr => k _.
  rewrite -bigXadd_Xreal_i.
  rewrite Xpow_idem Xpow_Xreal big_Xmul_Xadd_distr.
  apply: eq_bigr => i _.
  by rewrite Hrf Hrg.
rewrite -ctr H3 H1 H2 H4.
clear ctr H3 H1 H2 H4 sf sg G HG.
case (f x) => [|rfx] //=.
case (g x) => [|rgx] //=.
f_equal; ring_simplify.
set a' := \big[Rplus/R0]_(k < n'.+1)
   (\big[Rplus/R0]_(i < k.+1) (rf i * rg (k - i)%nat *
                                                     rxx0 ^ k))%Re.
apply: (Rplus_eq_reg_l (- (rfx * rgx - a'))).
ring_simplify.
rewrite /a' {a'}.
rewrite SuccNat2Pos.id_succ.
rewrite big_distrl /=.
have->: \big[Rplus/R0]_(i < n')
  (\big[Rplus/0]_(i0 < ((i+n'.+1).+1)) (rf i0 *
    rg ((i+n'.+1) - i0)%N * rxx0 ^ i) *
    (rxx0 * rxx0 ^ n'))%Re =
  \big[Rplus/R0]_(0 <= i < n'.+1 + n' - n'.+1)
  (fun j => \big[Rplus/0]_(i0 < (j+n'.+1).+1) (rf (i0)%N *
    rg ((j+n'.+1) - i0)%N *
    rxx0 ^ ((j+n'.+1))%nat))%Re i.
  rewrite addKn big_mkord.
  apply: eq_bigr => i _.
  rewrite big_distrl /=.
  apply: eq_bigr => j _.
  by rewrite pow_add /=; ring.
have <- := (@big_addn R R0 Rplus O (n'.+1+n') n'.+1 (fun _ => true)
 (fun i => \big[Rplus/R0]_(i0 < i.+1) (rf i0 * rg (i - i0)%N *
                                         rxx0 ^ i)%Re)).
rewrite add0n.
have <- := @big_mkord R R0 Rplus n'.+1 (fun _ => true)
   (fun i => \big[Rplus/R0]_(i0 < i.+1) (rf i0 * rg (i - i0)%N * rxx0 ^ i)%Re).
have <- := @big_cat_nat R R0 Radd_monoid n'.+1 0%N (n'.+1 +n')%N
  (fun _ => true) (fun i => \big[Rplus/R0]_(i0 < i.+1) (rf i0 * rg (i - i0)%N *
                                         rxx0 ^ i)%Re); [|done|]; last first.
  by apply/ltP; rewrite addnE /addn_rec; omega.
rewrite /= big_mkord.
rewrite big_distrlr /=.
symmetry; apply: Rminus_diag_eq.
rewrite addSn.
set s := \big[Rplus/0%Re]_(i < (n' + n').+1) _.
rewrite (eq_bigr (fun (i : 'I_n'.+1) =>
  \big[Rplus/0%Re]_(j < n'.+1) (rf i * rg j * rxx0 ^ (i + j))%Re)); last first.
  by move=> i _; apply: eq_bigr; first by move=> j _;rewrite pow_add; field.
apply: poly_mul.
move=> i Hi.
split.
  have H : Xreal (rf i) = Xreal 0%R; last by case: H.
  by rewrite -Hrf PolR.tnth_out // Hf1.
have H : Xreal (rg i) = Xreal 0%R; last by case: H.
by rewrite -Hrg PolR.tnth_out // Hg1.
*)
*)
Qed.

Lemma TM_mul_correct (X0 X : I.type) (TMf TMg : rpa) f g n :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul TMf TMg X0 X n.-1)
  (fun xr => Xmul (f xr) (g xr)).
Proof.
move=> Ht [Hdf Hef H0 Hf] Hg.
apply: TM_mul_correct_gen => //.
exact: subset_refl.
Qed.

Definition poly_horner_tm n p (Mf : rpa) (X0 X : I.type) : rpa :=
  @Pol.fold rpa
  (fun a b => (TM_add (TM_cst a) (TM_mul b Mf X0 X n)))
  (TM_cst I.zero) p.

Lemma size_TM_add Mf Mg :
  Pol.size (approx (TM_add Mf Mg)) =
  maxn (Pol.size (approx Mf)) (Pol.size (approx Mg)).
Proof.
by rewrite /TM_add /= Pol.size_add.
Qed.

Lemma size_TM_mul Mf Mg n X0 X :
  Pol.size (approx (TM_mul Mf Mg X0 X n)) = n.+1.
Proof. by rewrite /TM_mul /= Pol.size_mul_trunc. Qed.

Lemma size_TM_sub Mf Mg :
  Pol.size (approx (TM_sub Mf Mg)) =
  maxn (Pol.size (approx Mf)) (Pol.size (approx Mg)).
Proof. by rewrite /TM_sub /= Pol.size_sub. Qed.

Lemma size_TM_opp Mf :
  Pol.size (approx (TM_opp Mf)) = Pol.size (approx Mf).
Proof. by rewrite /TM_opp /= Pol.size_opp. Qed.

Lemma size_poly_horner_tm n p Mf X0 X :
  Pol.size (approx (poly_horner_tm n p Mf X0 X)) = n.+1.
Proof.
rewrite /poly_horner_tm.
elim/Pol.poly_ind: p =>[|a p IHp].
  admit. admit. (* FIXME/WIP
  by rewrite Pol.fold_polyNil /TM_cst Pol.size_rec1.
by rewrite Pol.fold_polyCons size_TM_add /TM_cst Pol.size_rec1 size_TM_mul maxnn.
*)
Qed.

(* Attention!
la taille du TM (e.g. Mf) est decorrelee de celle du poly pour le fold
*)

(*
Lemma poly_horner_tm_correct_aux_gen smallX0 X0 X Mf f pi :
  I.subset_ smallX0 (I.convert X0) ->
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty smallX0 ->
  f Xnan = Xnan ->
  i_validTM smallX0 (I.convert X) Mf f ->
  let n := tsize pi in
  forall nf, tsize (approx Mf) = nf.+1 ->
  forall pr, n = PolR.tsize pr ->
  (forall k, k < n -> contains (I.convert (tnth pi k)) (PolR.tnth pr k)) ->
  i_validTM smallX0 (I.convert X) (poly_horner_tm nf pi Mf X0 X)
  (fun x => @PolR.tfold _
    (fun a b => Xadd a (Xmul b (f x)))
    (Xmask (Xreal 0) x) pr).
Proof.
move=> Hsmall Hin Hts Hnan [Hf0 Hf1 Hf2] n nf Hnf px Hsize Hnth.
have Ht : not_empty (I.convert X0).
  case Hts => t Hts'.
  exists t.
  exact: (subset_contains smallX0).
rewrite /n {n} in Hsize Hnth.
elim/tpoly_ind: pi px Hsize Hnth =>[|ai pi IHpi];
  elim/PolR.tpoly_ind => [|ax px IHpx] Hsize Hnth.
+ rewrite /poly_horner_tm tfold_polyNil.
  apply: (TM_fun_eq (f := fun x => Xmask (Xreal 0) x)).
    by move=> *; rewrite PolR.tfold_polyNil.
  apply: (@i_validTM_subset_X0 X0) =>//.
  apply: TM_cst_correct =>//.
  by rewrite I.zero_correct; split; auto with real.
+ by rewrite PolR.tsize_polyCons tsize_polyNil in Hsize.
+ by rewrite tsize_polyCons PolR.tsize_polyNil in Hsize.
clear IHpx.
rewrite /poly_horner_tm tfold_polyCons.
apply: (TM_fun_eq (f := fun x =>
  (Xmask ax x) + Xmul (@PolR.tfold ExtendedR
  (fun (a1 : FullXR.T) (b : ExtendedR) => a1 + Xmul b (f x))
  (Xmask (Xreal 0) x) px) (f x))).
  move=> x; rewrite PolR.tfold_polyCons.
  case cx : x =>//.
  by rewrite Hnan Xmul_comm /= Xadd_comm.
apply: TM_add_correct_gen =>//.
- by rewrite size_TM_mul /TM_cst tsize_trec1.
- apply: (@i_validTM_subset_X0 X0) =>//.
  apply: TM_cst_correct =>//.
  rewrite tsize_polyCons in Hnth.
  have H := Hnth 0 (ltn0Sn _).
  rewrite tnth_polyCons in H => //.
  by rewrite PolR.tnth_polyCons in H.
rewrite -/(poly_horner_tm nf pi Mf X0 X).
have H1 := @TM_mul_correct_gen smallX0 X0 X (poly_horner_tm nf pi Mf X0 X) Mf
  (fun xr : ExtendedR =>
    (@PolR.tfold ExtendedR
    (fun (a1 : FullXR.T) (b : ExtendedR) => a1 + Xmul b (f xr))
    (Xmask (Xreal 0) xr) px)) f Hsmall Hin Hts.
rewrite size_poly_horner_tm Hnf in H1.
apply: H1 =>//.
apply: IHpi.
  rewrite tsize_polyCons PolR.tsize_polyCons in Hsize.
  by case: Hsize.
move=> k Hk.
have Hkc : k.+1 < tsize (tpolyCons ai pi).
  by rewrite tsize_polyCons /leq subSS.
move/(_ k.+1 Hkc) in Hnth.
rewrite tnth_polyCons // PolR.tnth_polyCons // in Hnth.
rewrite tsize_polyCons PolR.tsize_polyCons in Hsize.
by case: Hsize=><-.
Qed.

Lemma poly_horner_tm_correct_gen (smallX0 : interval) (X0 X : I.type) Mf f p :
  I.subset_ smallX0 (I.convert X0) ->
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty smallX0 ->
  f Xnan = Xnan ->
  i_validTM smallX0 (I.convert X) Mf f ->
  forall n, tsize p = n.+1 ->
  forall nf, tsize (approx Mf) = nf.+1 ->
  forall pr, tsize p = PolR.tsize pr ->
  (forall k, k < tsize p ->
  contains (I.convert (tnth p k)) (PolR.tnth pr k)) ->
  i_validTM smallX0 (I.convert X)
  (poly_horner_tm nf p Mf X0 X)
  (fun x => PolR.horner tt pr (f x)).
Proof.
move=> HinX0 HinX H Hnan H0 n Hn nf Hnf pr H1 H2.
have HH := @poly_horner_tm_correct_aux_gen smallX0
    X0 X Mf f p HinX0 HinX H Hnan H0 nf Hnf pr H1 H2.
apply: (TM_fun_eq (f := (fun x : ExtendedR =>
    @PolR.tfold ExtendedR
    (fun (a : FullXR.T) (b : ExtendedR) => a + Xmul b (f x))
    (Xmask (Xreal 0) x) pr))) =>// x Hx.
rewrite Hn in H1.
clear H2 HH Hn.
elim/PolR.tpoly_ind: pr n H1 => [|ar pr IHpr] n H1.
  by rewrite PolR.tsize_polyNil in H1.
elim/PolR.tpoly_ind: pr ar H1 IHpr => [|a2 p2 IHp2] ar H1 IHpr.
  rewrite is_horner_pos.
    rewrite PolR.tsize_polyCons PolR.tfold_polyCons.
    rewrite PolR.tfold_polyNil.
    rewrite big_ord_recl.
    rewrite PolR.tsize_polyNil big_ord0 PolR.tnth_polyCons //=.
    case cx : x => [|rx].
      by rewrite /= Xadd_comm Xmul_comm Hnan.
    case cfx : (f (Xreal rx)) => [|rfx].
      by rewrite /= Xadd_comm Xmul_comm.
    rewrite /= /Xpow /=.
    by case ca : ar => //=; f_equal; ring.
  by rewrite PolR.tsize_polyCons.
clear IHp2.
rewrite is_horner_pos.
  rewrite PolR.tsize_polyCons PolR.tfold_polyCons.
  move/(_ (PolR.tsize p2)) in IHpr.
  rewrite IHpr.
    rewrite big_ord_recl.
    rewrite PolR.tnth_polyCons //=.
    case E: (f x)=> [|r].
      rewrite Xmul_comm /=.
      unfold Xpow; simpl.
      rewrite Xmul_comm /=.
      by rewrite Xadd_comm.
    have->: (ar * (Xreal r) ^ 0)%XR = ar.
      unfold Xpow; simpl.
      case: (ar) =>//.
      by move=> r'; simpl; f_equal; ring.
    congr Xadd.
    rewrite PolR.is_horner /=.
    rewrite PolR.tsize_polyCons.
    have->: (\big[Xadd/Xreal 0]_(i < (PolR.tsize p2).+1)
      (PolR.tnth (PolR.tpolyCons a2 p2) i * Xreal r ^ i) * Xreal r)%XR
      = (\big[Xadd/Xreal 0]_(i < (PolR.tsize p2).+1)
      (PolR.tnth (PolR.tpolyCons a2 p2) i * Xreal r ^ i * Xreal r))%XR
      by apply big_Xmul_Xadd_distr.
    apply: eq_bigr => i _.
    rewrite [in RHS](PolR.tnth_polyCons _) /=.
      rewrite Xmul_assoc.
      congr Xmul.
      rewrite SuccNat2Pos.id_succ /=.
      rewrite Rmult_comm.
      have->: (Xreal (r ^ i * r) = Xreal (r ^ i) * Xreal r)%XR by done.
      congr Xmul.
      by rewrite Xpow_idem Xpow_Xreal.
    have Hi := ltn_ord i.
    by rewrite PolR.tsize_polyCons.
  by rewrite PolR.tsize_polyCons.
by rewrite PolR.tsize_polyCons.
Qed.

Lemma poly_horner_tm_correct_aux X0 X Mf f p :
  not_empty (I.convert X0) ->
  f Xnan = Xnan ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  let n := tsize p in
  forall nf, tsize (approx Mf) = nf.+1 ->
  forall pr, n = PolR.tsize pr ->
  (forall k, k < n -> contains (I.convert (tnth p k)) (PolR.tnth pr k)) ->
  i_validTM (I.convert X0) (I.convert X) (poly_horner_tm nf p Mf X0 X)
  (fun x => @PolR.tfold _
    (fun a b => Xadd a (Xmul b (f x)))
    (Xmask (Xreal 0) x) pr).
Proof.
move=> Ht Hnan [Hf0 Hf1 Hf2] n nf Hnf px Hsize Hnth.
apply: poly_horner_tm_correct_aux_gen =>//.
exact: subset_refl.
Qed.

Lemma poly_horner_tm_correct X0 X Mf f p :
  not_empty (I.convert X0) ->
  f Xnan = Xnan ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  forall n, tsize p = n.+1 ->
  forall nf, tsize (approx Mf) = nf.+1 ->
  forall pr, PolR.tsize pr = tsize p ->
  (forall k, k < tsize p ->
  contains (I.convert (tnth p k)) (PolR.tnth pr k)) ->
  i_validTM (I.convert X0) (I.convert X) (poly_horner_tm nf p Mf X0 X)
  (fun x => PolR.horner tt pr (f x)).
Proof.
move=> H Hnan H0 n Hn nf Hnf pr H1 H2.
apply: (poly_horner_tm_correct_gen _ _ _ _ _ (n := n)) =>//.
  exact: subset_refl.
by case: H0.
Qed.
*)

Definition TM_type := I.type -> I.type -> nat -> rpa.

Definition TMset0 (Mf : rpa) t :=
  RPA (Pol.set_nth (approx Mf) 0 t) (error Mf).

Definition TM_comp (TMg : TM_type) (Mf : rpa) X0 X n :=
  let Bf := Bnd.ComputeBound prec (approx Mf) (I.sub prec X X0) in
  let Mg := TMg (Pol.nth (approx Mf) 0) (I.add prec Bf (error Mf)) n in
  let M1 := TMset0 Mf I.zero in
  let M0 := poly_horner_tm n (approx Mg) M1 X0 X in
  RPA (approx M0) (I.add prec (error M0) (error Mg)).

(** REMARK: the TM is supposed not void *)

Lemma TMset0_correct X0 X TMf f :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  forall nf, Pol.size (approx TMf) = nf.+1 ->
  forall fi0, contains (I.convert X0) fi0 ->
  exists a0, i_validTM (Interval_interval.Ibnd fi0 fi0) (I.convert X)
  (TMset0 TMf I.zero) (fun x => f x - a0).
Proof.
move=> Ht [Hf0 Hf1 Hf2] nf Hnf.
move=> fi0 Hfi0.
  admit.
(*
have {Hf2} [alf [Hsize Hnth Herr]] := Hf2 fi0 Hfi0.
exists (PolR.tnth alf 0).
split=>//.
  have H0 := subset_contains _ _ Hf1 _ Hfi0.
  case cf: fi0 H0 Hf1 Hfi0 =>[|r];
    case: (I.convert X0) =>[|l0 u0];
     case: (I.convert X) =>[|l u] => H0 Hf1 Hfi0 //=.
  have {H0} [H0a H0b] := H0; rewrite /le_lower /le_upper; split.
    by case: l Hf1 H0a => [|rl] //=; psatzl R.
  by case: u Hf1 H0b.
move=> N fi0' Hfi0'.
exists (PolR.tset_nth alf 0 (Xreal 0)).
split.
    rewrite /N /=.
    rewrite PolR.tsize_set_nth ?tsize_set_nth //.
    by rewrite Hsize Hnf.
  move=> k Hk /=.
  rewrite /N /= in Hk.
  case ck : k => [|k'].
    rewrite tnth_set_nth.
    rewrite PolR.tnth_set_nth.
    by rewrite I.zero_correct; split; auto with real.
  rewrite tnth_set_nth =>//.
  rewrite PolR.tnth_set_nth=>//.
  apply: Hnth.
  rewrite -ck; rewrite tsize_set_nth in Hk=> //.
  suff<-: maxn 1 (tsize (approx TMf)) = tsize (approx TMf) by [].
  by apply/maxn_idPr; rewrite Hnf.
move=> x Hx /=.
move/(_ x Hx) in Herr.
rewrite PolR.is_horner Hsize Hnf in Herr.
rewrite PolR.is_horner PolR.tsize_set_nth Hsize Hnf //.
rewrite (appP idP maxn_idPr) //.
rewrite big_ord_recl.
rewrite big_ord_recl in Herr.
rewrite /ord0 /= PolR.tnth_set_nth eqxx.
case E: fi0 => [|r].
  subst.
  rewrite !Xsub_split in Herr.
  rewrite /= [Xadd _ Xnan]Xadd_comm /= in Herr.
  rewrite /Xpow /= in Herr.
  rewrite /= [Xmul _ Xnan]Xmul_comm /= in Herr.
  rewrite /= [Xadd _ Xnan]Xadd_comm /= in Herr.
  by case: (I.convert (error TMf)) Hf0 Herr.
have->: fi0' = (Xreal r).
  rewrite /contains E in Hfi0'.
  case: fi0' Hfi0' =>//.
  move=> ? [? ?]; f_equal.
  exact: Rle_antisym.
rewrite -E.
case xf : (x - fi0)%XR => [|xr].
  rewrite /Xpow /= Xsub_split /= Xadd_comm /=.
  by rewrite xf /Xpow Xmul_comm Xsub_split Xadd_comm /= in Herr.
rewrite xf /(Xpow _ 0) /= Xmul_comm Xmul0 in Herr.
simpl Xmul; rewrite Rmult_0_l Xadd0.
have Hbig : \big[Xadd/Xreal 0]_(i < nf)
    (PolR.tnth (PolR.tset_nth alf 0 (Xreal 0))
    (bump 0 i) * Xreal xr ^ bump 0 i)%XR =
    \big[Xadd/Xreal 0]_(i < nf) (PolR.tnth alf (bump 0 i) *
    Xreal xr ^ bump 0 i)%XR.
  apply: eq_bigr => i _ /=.
  by rewrite PolR.tnth_set_nth.
rewrite {}Hbig.
suff <- : forall a b c : ExtendedR, (a - (b + c) = a - b - c)%XR by [].
move=> a b c; case: a; case: b; case: c=> //=.
by move=> *; f_equal; ring.
*)
Qed.

Definition dom_comp dg df f r :=
  df r &&
  match f (Xreal r) with
  | Xnan => false
  | Xreal r => dg r
  end.

Lemma TM_comp_correct (X0 X : I.type) (Tyg : TM_type) (TMf : rpa) g f :
  f Xnan = Xnan ->
  not_empty (I.convert X0) ->
  forall n, Pol.size (approx TMf) = n.+1 ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  (forall Y0 Y k, I.subset_ (I.convert Y0) (I.convert Y) ->
    not_empty (I.convert Y0) ->
    i_validTM (I.convert Y0) (I.convert Y) (Tyg Y0 Y k) g
    /\ Pol.size (approx (Tyg Y0 Y k)) = k.+1) ->
  i_validTM (I.convert X0) (I.convert X)
  (TM_comp Tyg TMf X0 X n) (fun xr => (g (f xr))).
Proof.
move=> Hnan Ht n Hn Hf Hg.
have {Ht} /not_empty'E [t Ht] := Ht.
case Hf => [H0 H1 H2].
split=>//.
  move=> x Hx Dx.
  admit.
  rewrite /= (_ : (Xreal 0) = (Xreal 0 + Xreal 0)); last by rewrite /= Rplus_0_l.
  admit.
(*
  have [pr [Hpr Hnth Herr]] := (H2 t Ht).
  have Hcp : Link.contains_pointwise _ _ := conj (esym Hpr) Hnth. (* FIXME *)
  have [||[Hokg1 Hokg2 Hokg4] Hokg3] :=
      Hg (tnth (approx TMf) 0)
      (I.add prec
        (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0)) (error TMf)) n.
  - have L := @ComputeBound_nth0 prec (approx TMf) pr (I.sub prec X X0) Hcp.
    have H := (L (@subset_sub_contains_0 _ _ _ _ _ _)).
    have {H L} L := (H t Ht H1).
    apply: (subset_subset _
        (I.convert (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0)))) =>//.
    apply: Iadd_zero_subset_r =>//.
    exists (PolR.horner tt pr (Xreal 0)).
    apply: Bnd.ComputeBound_correct =>//.
    exact: (@subset_sub_contains_0 _ t).
  - apply: not_emptyE; exists (PolR.tnth pr 0).
    by apply: Hnth; rewrite Hn.
  have {Hokg4} Hokg4 := Hokg4 (PolR.tnth pr 0).
  have [|prg [Hprg1 Hprg2 Hprg3]] := Hokg4.
    by apply Hnth; rewrite Hn.
  rewrite Hokg3 in Hprg1 Hprg2.
  apply: I.add_correct =>//.
(**************** start TMset0_correct ****************)
  have H_TMset0 :
   i_validTM (Interval_interval.Ibnd t t) (I.convert X)
      (TMset0 TMf I.zero) (fun x : ExtendedR => f x - (PolR.tnth pr 0)).
    split; first done.
      have H0' := subset_contains _ _ H1 _ Ht.
      case cf: t => [|r];
       rewrite cf in Ht H0';
       destruct (I.convert X0) as [|l0 u0];
       destruct (I.convert X) as [|l u]; rewrite //=.
      rewrite /= in H0'.
      split; destruct H0'; rewrite /le_lower /le_upper.
        by destruct l as [|rl] => //=; psatzl R.
      by destruct u as [|ru].
    move=> N fi0' Hfi0'.
      exists (PolR.tset_nth pr 0 (Xreal 0)).
      split.
          rewrite /N /=.
          rewrite PolR.tsize_set_nth ?tsize_set_nth //.
          by rewrite Hpr Hn.
        move=> k Hk /=.
        rewrite /N /= in Hk.
        case ck : k => [|k'].
          rewrite tnth_set_nth.
          rewrite PolR.tnth_set_nth eqxx.
          by rewrite I.zero_correct; split; auto with real.
        rewrite tnth_set_nth=>//=.
        rewrite PolR.tnth_set_nth=>//.
        apply: Hnth.
        by rewrite ck tsize_set_nth leq_max /= in Hk.
      move=> x Hx /=.
      move/(_ x Hx) in Herr.
      rewrite PolR.is_horner Hpr Hn in Herr.
      rewrite PolR.is_horner PolR.tsize_set_nth Hpr Hn //.
      rewrite (appP idP maxn_idPr) //.
      rewrite big_ord_recl.
      rewrite big_ord_recl in Herr.
      rewrite /ord0 /= PolR.tnth_set_nth eqxx.
      case E: t => [|r].
        subst.
        rewrite !Xsub_split in Herr.
      rewrite /= [Xadd _ Xnan]Xadd_comm /= in Herr.
      rewrite /Xpow /= in Herr.
      rewrite /= [Xmul _ Xnan]Xmul_comm /= in Herr.
      rewrite /= [Xadd _ Xnan]Xadd_comm /= in Herr.
      by case: (I.convert (error TMf)) Herr.
    have->: fi0' = (Xreal r).
      rewrite /contains in Hfi0'.
      rewrite E in Hfi0'.
      case: fi0' Hfi0' =>//.
      move=> ? [? ?]; f_equal.
      exact: Rle_antisym.
    rewrite -E.
    case xf : (x - t)%XR => [|xr].
      rewrite /Xpow /= Xsub_split /= Xadd_comm /=.
      by rewrite xf /Xpow Xmul_comm Xsub_split Xadd_comm /= in Herr.
    rewrite xf /(Xpow _ 0) /= Xmul_comm Xmul0 in Herr.
    simpl Xmul; rewrite Rmult_0_l Xadd0.
    have Hbig : \big[Xadd/Xreal 0]_(i < n)
     (PolR.tnth (PolR.tset_nth pr 0 (Xreal 0))
                                 (bump 0 i) * Xreal xr ^ bump 0 i)%XR =
     \big[Xadd/Xreal 0]_(i < n) (PolR.tnth pr (bump 0 i) *
                                      Xreal xr ^ bump 0 i)%XR.
      apply: eq_bigr => i _ /=.
      by rewrite PolR.tnth_set_nth.
    rewrite Hbig {Hbig}.
    have H : forall a b c : ExtendedR, (a - (b + c) = a - b - c)%XR.
      move=> a b c; case: a; case: b; case: c=> //=.
      by move=> *; f_equal; ring.
    by rewrite -H.
(**************** end TMset0_correct ****************)
  have [H1set0 H2set0 H3set0] := H_TMset0.
  have Hpe:=
   @poly_horner_tm_correct_gen (Interval_interval.Ibnd t t) X0 X
   (TMset0 TMf (I.zero)) (fun x : ExtendedR => f x - PolR.tnth pr 0)
   (approx
            (Tyg (tnth (approx TMf) 0)
               (I.add prec (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0))
                  (error TMf)) n)).
  have H' : I.subset_ (Interval_interval.Ibnd t t) (I.convert X0).
    case cf: t => [|r];
     rewrite cf in Ht;
     destruct (I.convert X0) as [|l0 u0]; rewrite //=.
    rewrite /= in Ht.
    split; case: Ht; rewrite /le_lower /le_upper.
      by case: (l0) =>[|rl] //=; psatzl R.
    by case: (u0) =>[|ru].
  have hex : not_empty (Interval_interval.Ibnd t t).
    case ct : t => [|rt].
      by exists R0.
    by exists rt => /=; split; apply: Rle_refl.
  have {Hpe H'} Hpe := Hpe H' H1 hex.
  rewrite Hnan /= in Hpe.
  have {Hpe} Hpe := Hpe (refl_equal Xnan) H_TMset0 n _ n _ prg.
  rewrite Hokg3 Hprg1 in Hpe.
  case: Hpe => [||||H _] => //=.
  rewrite tsize_set_nth Hn; exact/maxn_idPr.
move=> N fi0 Hfi0.
have [pr [Hpr Hnth Herr]] := H2 fi0 Hfi0.
have Hcp : Link.contains_pointwise _ _ := conj (esym Hpr) Hnth. (* FIXME *)
have [||[Hokg1 Hokg2 Hokg4] Hokg3] :=
    (Hg (tnth (approx TMf) 0)
    (I.add prec (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0)) (error TMf)) n).
- have L := ComputeBound_nth0 prec (approx TMf) pr (I.sub prec X X0) Hcp.
  have H := (L (@subset_sub_contains_0 _ _ _ _ _ _)).
  have {H L} L := (H fi0 Hfi0 H1).
  apply: (subset_subset _
       (I.convert (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0)))) =>//.
    apply: Iadd_zero_subset_r =>//.
    exists (PolR.horner tt pr (Xreal 0)).
    apply: Bnd.ComputeBound_correct =>//.
    exact: (@subset_sub_contains_0 _ t).
  apply: not_emptyE; exists (PolR.tnth pr 0).
  by apply: Hnth; rewrite Hn.
have {Hokg4} Hokg4 := Hokg4 (PolR.tnth pr 0).
have [|prg [Hprg1 Hprg2 Hprg3]] := Hokg4.
  by apply: Hnth; rewrite Hn.
rewrite Hokg3 in Hprg1 Hprg2.
(**************** start TMset0_correct ****************)
have H_TMset0 :
 i_validTM (Interval_interval.Ibnd fi0 fi0) (I.convert X)
        (TMset0 TMf I.zero) (fun x : ExtendedR => f x - (PolR.tnth pr 0)).
  split; first done.
    have H0' := subset_contains _ _ H1 _ Hfi0.
    case cf: fi0 => [|r];
        rewrite cf in Hfi0 H0';
        destruct (I.convert X0) as [|l0 u0];
        destruct (I.convert X) as [|l u]; rewrite //=.
    rewrite /= in H0'.
    split; destruct H0'; rewrite /le_lower /le_upper.
      by destruct l as [|rl] => //=; psatzl R.
    by destruct u as [|ru].
  move=> N' fi0' Hfi0'.
  exists (PolR.tset_nth pr 0 (Xreal 0)).
  split.
      rewrite /N' /=.
      rewrite PolR.tsize_set_nth ?tsize_set_nth //.
      by rewrite Hpr Hn.
    move=> k Hk /=.
    rewrite /N' /= in Hk.
    case ck : k => [|k'].
      rewrite tnth_set_nth.
      rewrite PolR.tnth_set_nth eqxx.
      by rewrite I.zero_correct; split; auto with real.
    rewrite tnth_set_nth=>//=.
    rewrite PolR.tnth_set_nth=>//.
    apply: Hnth.
    by rewrite ck tsize_set_nth leq_max /= in Hk.
  move=> x Hx /=.
  move/(_ x Hx) in Herr.
  rewrite PolR.is_horner Hpr Hn in Herr.
  rewrite PolR.is_horner PolR.tsize_set_nth Hpr Hn //.
  rewrite (appP idP maxn_idPr) //.
  rewrite big_ord_recl.
  rewrite big_ord_recl in Herr.
  rewrite /ord0 /= PolR.tnth_set_nth eqxx.

  case E: fi0 => [|r].
    subst.
    rewrite !Xsub_split in Herr.
    rewrite /= [Xadd _ Xnan]Xadd_comm /= in Herr.
    rewrite /Xpow /= in Herr.
    rewrite /= [Xmul _ Xnan]Xmul_comm /= in Herr.
    rewrite /= [Xadd _ Xnan]Xadd_comm /= in Herr.
    by case: (I.convert (error TMf)) Herr.
  have->: fi0' = (Xreal r).
    rewrite /contains in Hfi0'.
    rewrite E in Hfi0'.
    case: fi0' Hfi0' =>//.
    move=> ? [? ?]; f_equal.
    exact: Rle_antisym.
  rewrite -E.
  case xf : (x - fi0)%XR => [|xr].
    rewrite /Xpow /= Xsub_split /= Xadd_comm /=.
    by rewrite xf /Xpow Xmul_comm Xsub_split Xadd_comm /= in Herr.
  rewrite xf /(Xpow _ 0) /= Xmul_comm Xmul0 in Herr.
  simpl Xmul; rewrite Rmult_0_l Xadd0.
  have Hbig : \big[Xadd/Xreal 0]_(i < n)
   (PolR.tnth (PolR.tset_nth pr 0 (Xreal 0))
                                   (bump 0 i) * Xreal xr ^ bump 0 i)%XR =
    \big[Xadd/Xreal 0]_(i < n) (PolR.tnth pr (bump 0 i) *
                                        Xreal xr ^ bump 0 i)%XR.
    apply: eq_bigr => i _ /=.
    by rewrite PolR.tnth_set_nth.
  rewrite Hbig.
  clear Hbig.
  have H : forall a b c : ExtendedR, (a - (b + c) = a - b - c)%XR.
    move=> a b c; case: a; case: b; case: c=> //=.
    by move=> *; f_equal; ring.
  by rewrite -H.
(**************** end TMset0_correct ****************)
have [H1set0 H2set0 H3set0] := H_TMset0.

have Hpe:=
  @poly_horner_tm_correct_gen (Interval_interval.Ibnd fi0 fi0) X0 X
  (TMset0 TMf I.zero) (fun x : ExtendedR => f x - PolR.tnth pr 0)
  (approx
              (Tyg (tnth (approx TMf) 0)
                 (I.add prec (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0))
                    (error TMf)) n)).
have H' : I.subset_ (Interval_interval.Ibnd fi0 fi0) (I.convert X0).
  case cf: fi0 => [|r];
      rewrite cf in Hfi0;
      destruct (I.convert X0) as [|l0 u0] =>//=.
  rewrite /= in Hfi0.
  split; case: Hfi0; rewrite /le_lower /le_upper.
    by case: l0 Hf Ht H1 H2 Hpe => [|rl] //=; psatzl R.
  by case: (u0).
have hex: not_empty (Interval_interval.Ibnd fi0 fi0).
  case cf: fi0 => [|rf].
    by exists R0.
  by exists rf => /=; split; apply: Rle_refl.
have {Hpe H'} Hpe := Hpe H' H1 hex.
rewrite Hnan /= in Hpe.
have {Hpe} Hpe := Hpe (refl_equal Xnan) H_TMset0 n _ n _ prg.
rewrite Hokg3 Hprg1 in Hpe.
have {Hpe} [||||Hpe1 Hpe2 Hpe3] := Hpe; rewrite //=.
  rewrite tsize_set_nth Hn; exact/maxn_idPr.
(**************** discussion on fi0 ****************)
case cf : fi0 => [|r].
  rewrite cf in Hpe3.
  have {Hpe3} Hpe3 := Hpe3 (Xreal 0).
  have [|cn [Hpes Hpen Hpe]] := Hpe3; first done.
  exists cn.
  split =>// x Hx.
  have HX := subset_contains _ _ H1 _ Hfi0.
  rewrite cf in HX.
  have {Hpe} Hpe := Hpe _ HX.
  set erpe := (error
      (poly_horner_tm n
      (approx
      (Tyg (tnth (approx TMf) 0)
      (I.add prec (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0))
      (error TMf)) n)) (TMset0 TMf I.zero) X0 X)).
  set erg := (error
      (Tyg (tnth (approx TMf) 0)
      (I.add prec (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0)) (error TMf))
      n)).
  have Herpe : I.convert erpe = Interval_interval.Inan.
    rewrite -/erpe in Hpe.
    have Heqnan : (PolR.horner tt prg (f Xnan - PolR.tnth pr 0) -
         PolR.horner tt cn (Xnan - Xreal 0)) = Xnan.
      rewrite Hnan /=.
      elim/PolR.tpoly_ind: prg Hprg1 Hprg2 Hprg3 Hpe Hpe3
          => [|ag pg Hpg] Hprg1 Hprg2 Hprg3 Hpe Hpe3.
        by rewrite PolR.horner_polyNil.
      by rewrite PolR.horner_polyCons /= Xmul_comm.
    rewrite Heqnan in Hpe.
    case c : (I.convert erpe) => [|l u] //.
    by rewrite c in Hpe.
  rewrite /= -/erpe -/erg.
  have Heq :(I.convert (I.add prec erpe erg)) = Interval_interval.Inan.
    exact: (@Iadd_Inan_propagate_l _ (Xreal 0)).
  by rewrite Heq.
(**************** cas non degenere ****************)
rewrite cf in Hpe3.
have {Hpe3} Hpe3 := Hpe3 (Xreal r).
have {Hpe3} [|cn [Hpes Hpen Hpe]] := Hpe3.
  by split; apply: Rle_refl.
exists cn.
split=>// x Hx.
have HX := subset_contains _ _ H1 _ Hfi0.
rewrite cf in HX.
have {Hpe} Hpe := Hpe _ Hx.
set erpe := (error
    (poly_horner_tm n
    (approx
    (Tyg (tnth (approx TMf) 0)
    (I.add prec (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0))
    (error TMf)) n)) (TMset0 TMf I.zero) X0 X)).
set erg := (error
    (Tyg (tnth (approx TMf) 0)
    (I.add prec (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0)) (error TMf))
    n)).
rewrite -/erpe in Hpe.
rewrite /= -/erpe -/erg.
have {Hprg3} Hprg3 := Hprg3 (f x).
rewrite -/erg in Hprg3.
have H : contains
    (I.convert
    (I.add prec (Bnd.ComputeBound prec (approx TMf) (I.sub prec X X0)) (error TMf)))
    (f x).
  have {Herr} Herr := Herr x Hx.
  apply: (@Iadd_Isub_aux _ (PolR.horner tt pr (x - fi0))) =>//.
  apply: Bnd.ComputeBound_correct =>//.
  exact: I.sub_correct.
have {Hprg3 H} H := Hprg3 H.
set a := (PolR.horner tt prg (f x - PolR.tnth pr 0)).
rewrite -/a in Hpe H.
case ca : a => [|ra].
  rewrite ca /= in Hpe H.
  rewrite Xsub_split Xadd_comm /= in H.
  rewrite (@Iadd_Inan_propagate_l _ Xnan) => //=.
  by case: (I.convert erpe) Hpe.
suff->: (g (f x) - PolR.horner tt cn (x - Xreal r))
  = ((a - PolR.horner tt cn (x - Xreal r)) + (g (f x) - a)).
  exact: I.add_correct.
rewrite ca.
case: (g (f x)); case: (PolR.horner tt cn (x - Xreal r)) =>//=.
move=> *; f_equal; ring.
*)
admit.
Qed.

Definition TM_inv_comp Mf X0 X (n : nat) := TM_comp TM_inv Mf X0 X n.

Lemma TM_inv_comp_correct (X0 X : I.type) (TMf : rpa) f :
  f Xnan = Xnan ->
  not_empty (I.convert X0) ->
  forall n, Pol.size (approx TMf) = n.+1 ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X)
  (TM_inv_comp TMf X0 X n) (fun xr => Xinv (f xr)).
Proof.
move=> Hnan Ht n Hn Hf.
apply: TM_comp_correct=> //.
have {Hf} [Hef H0 Hf] := Hf => a Y k Ha Ht'.
split; first exact: TM_inv_correct.
by rewrite size_TM_inv.
Qed.

Definition TM_div Mf Mg X0 X n :=
   TM_mul Mf (TM_inv_comp Mg X0 X n) X0 X n.

Lemma TM_div_correct (X0 X : I.type) (TMf TMg : rpa) f g n :
  g Xnan = Xnan->
  not_empty (I.convert X0) ->
  n = Pol.size (approx TMf) ->
  n = Pol.size (approx TMg) -> 0 < n ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X)
  (TM_div TMf TMg X0 X n.-1) (fun xr => Xdiv (f xr) (g xr)).
Proof.
move=> Hnan Hex Hn1 Hn2 Hnpos Hf Hg.
apply: (TM_fun_eq (f := fun xr => Xmul (f xr) (Xinv (g xr)))).
  by move=> x; rewrite Xdiv_split.
rewrite /TM_div.
apply: TM_mul_correct =>//.
apply TM_inv_comp_correct =>//.
by rewrite -Hn2 (prednK Hnpos).
Qed.

Lemma size_TM_comp (X0 X : I.type) (Tyg : TM_type) (TMf : rpa) (n : nat) :
  Pol.size (approx (TM_comp Tyg TMf X0 X n)) = n.+1.
Proof. by rewrite /= size_poly_horner_tm. Qed.

End PrecArgument.


(* FIXME: Generalize TM_integral to handle "X1" and "Y1"
   FIXME: Finish the experiment below to define "TM_atan" using "TM_integral"

Definition TM_atan2 (u : U) (X0 X : I.type) : T :=
  let one := TM_cst u.1 (I.fromZ 1) X0 X u.2 in
  let tm := TM_div u.1 X one (TM_add u X one (TM_power_int u.1 2 X0 X n)) in
  (* prim *) TM_integral u X X1 (I.atan u.1 X1) t'.

Definition atan2 := Eval hnf in fun_gen I.atan TM_atan2.

Lemma Xatan_RInt_f : forall (xF : ExtendedR -> ExtendedR) x1,
let f := toR_fun xF in
let xG := toXreal_fun
  (fun r => RInt (fun x => Derive f x / (1 + (f x)^2)) x1 r + Ratan.atan (f x1))%R in
forall x, xG x = Xatan (xF x).
Proof.
admit. (* Coquelicot proof *)
Qed.

Theorem atan2_correct :
  forall u (X : I.type) tf xF,
  approximates X tf xF ->
  approximates X (atan2 u X tf) (fun x => Xatan (xF x)).
Proof.
intros.
pose x1 := proj_val (I.convert_bound (I.midpoint X)).
pose f := toR_fun xF.
pose xG := toXreal_fun
  (fun r => RInt (fun x => Derive f x / (1 + (f x)^2)) x1 r + Ratan.atan (f x1))%R.
apply: approximates_ext.
apply: xG.
move=> x; apply: Xatan_RInt_f.
rewrite /atan2.
rewrite /xG /toXreal_fun.
apply: prim_correct.
exact: toXreal_fun (fun r : R => Derive f r / (1 + f r ^ 2)).
admit. (* midpoint *)
apply: I.atan_correct.
split =>//.
admit. (* to see later *)
rewrite /atan2 /prim.
case: tf H.
apply: prim_correct.

move=> u Y tf f [Hnan Hnil Hmain].
split=>//; first by rewrite Hnan.
by rewrite /= /tmsize size_TM_any.
move=> Hne; apply: TM_any_correct.
exact: not_empty_Imid.
exact: Imid_subset.
move=> x Hx.
apply: I.atan_correct.
exact: horner_correct.
Qed.
*)

End TaylorModel.
