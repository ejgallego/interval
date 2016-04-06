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

Require Import ZArith Psatz Reals.
Require Import Flocq.Core.Fcore_Raux.
Require Import Coquelicot.Coquelicot.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq mathcomp.ssreflect.fintype mathcomp.ssreflect.bigop.
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
Require Import Rstruct.
Require Import xreal_ssr_compat.
Require Import seq_compl.
Require Import interval_compl.
Require Import poly_datatypes.
Require Import taylor_poly.
Require Import basic_rec.
Require Import poly_bound.
Require Import coquelicot_compl integral_pol.

(********************************************************************)
(** This theory implements Taylor models with interval polynomials for
    univariate real-valued functions. The implemented algorithms rely
    on the so-called Zumkeller's technique, which allows one to obtain
    sharp enclosures of the approximation error, when it detects that
    the Taylor-Lagrange remainder of the elementary function at stake
    is monotonic over the interval under study.
*)
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

Section PrecArgument.
(** For greater convenience, set the precision as a section variable.
    Note that this will not hinder any dynamic-change of the precision
    inside the functions that are defined or called below.
*)
Variable prec : I.precision.

Section TaylorModel.

Variable M : rpa.

Variable Tcoeffs : I.type -> nat -> Pol.T.
(** For complexity reasons, [Tcoeffs] must return more than one coefficient. *)

(** The generic functions [TLrem]/[Ztech] are intended to ease the
    computation of the interval remainder for basic functions.
*)
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

(** Note that Zumkeller's technique is not necessary for [TM_cst] & [TM_var]. *)
Definition TM_cst X c : rpa :=
  RPA (Pol.polyC c) (I.mask (I.mask I.zero X) c).

Definition TM_var X X0 :=
  RPA (Pol.set_nth Pol.polyX 0 X0) (I.mask I.zero X).

Definition TM_exp X0 X (n : nat) : rpa :=
  (** Note that this let-in is essential in call-by-value context. *)
  let P := (T_exp prec X0 n) in
  RPA P (Ztech (T_exp prec) P (I.exp prec) X0 X n).

Definition TM_sin X0 X (n : nat) : rpa :=
  let P := (T_sin prec X0 n) in
  RPA P (Ztech (T_sin prec) P (I.sin prec) X0 X n).

Definition TM_cos X0 X (n : nat) : rpa :=
  let P := (T_cos prec X0 n) in
  RPA P (Ztech (T_cos prec) P (I.cos prec) X0 X n).

Definition TM_atan X0 X (n : nat) : rpa :=
  let P := (T_atan prec X0 n) in
  RPA P (Ztech (T_atan prec) P (I.atan prec) X0 X n).

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
  [/\
 (* forall x : ExtendedR, contains X x -> f x = Xnan -> eqNai (error M), *)
    forall x : R, contains X (Xreal x) -> ~~ defined xf x -> eqNai (error M),
    X = IInan -> I.convert (error M) = IInan,
    contains (I.convert (error M)) (Xreal 0),
    I.subset_ X0 X &
    forall x0, contains X0 (Xreal x0) ->
    exists2 Q, approx M >:: Q
    & forall x, contains X (Xreal x) ->
      error M >: toR_fun xf x - (PolR.horner tt Q (x - x0))%R].
(** Otherwise, we could replace [toR_fun xf x] with [proj_val (xf (Xreal x))] *)

Lemma TM_fun_eq f g X0 X TMf :
  (forall x, contains X (Xreal x) -> f (Xreal x) = g (Xreal x)) ->
  i_validTM X0 X TMf f -> i_validTM X0 X TMf g.
Proof.
move=> Hfg [Hdom Hnai H0 Hsubs Hmain].
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
  now rewrite -> Rmin_left, Rmax_right by now apply Rlt_le.
- rewrite Heq. rewrite RInt_point.
  apply: (@mul_0_contains_0_l _ (Xreal (f3 x1))).
  + apply: (Hext x1); split.
    apply Rmin_l.
    apply Rmax_l.
  + have -> :
    Xreal 0 = Xsub (Xreal x2) (Xreal x1) ; first by rewrite Heq /= Rminus_eq_0.
    by apply: I.sub_correct.
- apply: contains_RInt_gt => // .
    by apply: ex_RInt_swap.
  move => x H1x2; apply: Hext.
  now rewrite -> Rmin_right, Rmax_left by now apply Rlt_le.
Qed.

Lemma pol_int_sub pol x1 x2 x3:  ex_RInt (fun y : R => PolR.horner tt pol (y - x3)) x1 x2.
Proof.
have -> : x1 = x1 - x3 + x3 by ring.
have -> : x2 = x2 - x3 + x3 by ring.
apply: ex_RInt_translation_sub.
exact: Rpol_integrable.
Qed.

(** the following section is now concerned with computing just one integral
    from a to b, for the "interval" tactic *)
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

Lemma integralEnclosure_correct :
  i_validTM iX0 iX Mf xF ->
  contains (I.convert integralEnclosure) (Xreal (RInt f a b)).
Proof.
move => [] Hdef Hnai Hcontains0 HX0X H.
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
      revert Hx.
      now rewrite -> Rmin_left, Rmax_right.
    apply Rnot_le_lt, Rlt_le in Hba.
    apply: contains_intvl_trans Hb Ha _; red.
    revert Hx.
    now rewrite -> Rmin_right, Rmax_left.
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
move => Hx0X0 [Hdef Hnai ErrMf0 HX0X HPol].
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

Lemma TM_integral_correct (x0 : Rdefinitions.R) :
contains iX0 (Xreal x0) ->
i_validTM (I.convert X0) iX Mf xF ->
i_validTM (I.convert X0) iX TM_integral (Xlift (RInt f x0)).
Proof.
move => Hx0X0 [Hdef Hnai ErrMf0 HX0X HPol] /= ; split =>//.
    rewrite /TM_integral /TM_integral_error /= /iX => H.
    by rewrite I.add_propagate_l // I.mul_propagate_l // I.sub_propagate_l.
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

Section Misc.
(* Note: some of these lemmas might be moved in a better place *)

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

Lemma Rdiv_pos_compat (x y : R) :
  (0 <= x -> 0 < y -> 0 <= x / y)%Re.
Proof.
move=> Hx Hy.
rewrite /Rdiv -(@Rmult_0_l (/ y)).
apply: Rmult_le_compat_r =>//.
by left; apply: Rinv_0_lt_compat.
Qed.

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

End Misc.

Section GenericProof.
(** Generic proof for [TLrem] and [Ztech]. *)

Variable xf : ExtendedR -> ExtendedR.
Variable F : I.type -> I.type.
Variable P : R -> nat -> PolR.T.
Variable IP : I.type -> nat -> Pol.T.

Let f0 := toR_fun xf.
Let def := defined xf.
Let Dn n := Derive_n f0 n.

Hypothesis xf_Xnan : xf Xnan = Xnan.
Hypothesis F_contains : I.extension xf F.

Variables X : I.type.

Class validPoly : Prop := ValidPoly {
  Poly_size : forall (x0 : R) n, PolR.size (P x0 n) = n.+1;
  Poly_nth :
    forall (x : R) n k,
    X >: x ->
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

Hypothesis Hder_n : forall n x, X >: x -> ex_derive_n f0 n x.

Lemma Poly_nth0 x n : X >: x -> PolR.nth (P x n) 0 = f0 x.
Proof. by move=> H; rewrite Poly_nth // ?Rcomplements.Rdiv_1 //. Qed.

Theorem i_validTM_TLrem (X0 : I.type) n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (IP X0 n) (TLrem IP X0 X n)) xf.
Proof.
move=> Hsubs [t Ht].
pose err := TLrem IP X0 X n.
split=>//=.

(* Def *)
move=> x Hx Nx; rewrite /TLrem; apply/eqNaiP.
rewrite I.mul_propagate_l //.
exact: (IPoly_nai Hx Nx).

(* Nai *)
move=> HX; rewrite /TLrem.
by rewrite I.mul_propagate_r // I.power_int_propagate // I.sub_propagate_l.

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
by apply: eq_big_nat => i Hi; rewrite Poly_nth.
rewrite Hbig.
have Hder' : forall n r, X >: r -> ex_derive_n (toR_fun xf) n r.
  move=> m r Hr.
  exact: Hder_n.
have [c [Hcin [Hc Hc']]] := (@ITaylor_Lagrange xf (I.convert X) n Hder' x0 x H0 Hx).
rewrite Hc {Hc t Ht} /TLrem.
apply: R_mul_correct=>//.
  rewrite -(@Poly_nth _ c n.+1 n.+1) //;
  exact: IPoly_nth.
rewrite pow_powerRZ.
apply: R_power_int_correct.
exact: R_sub_correct.
Qed.

Definition Rdelta (n : nat) (x0 x : R) :=
  (f0 x - (P x0 n).[x - x0])%R.

(** We now define the derivative of [Rdelta n x0] *)
Definition Rdelta' (n : nat) (x0 x : R) :=
  (Dn 1 x - (PolR.deriv tt (P x0 n)).[x - x0])%R.

Lemma bigXadd'_P (m n : nat) (x0 s : R) :
  X >: x0 ->
  ex_derive_n f0 n x0 ->
  m <= n ->
  \big[Rplus/R0]_(0 <= i < m) (PolR.nth (P x0 n) i.+1 * INR i.+1 * s ^ i)%R =
  \big[Rplus/R0]_(0 <= i < m) ((Dn i.+1 x0) / INR (fact i) * s ^ i)%R.
Proof.
move=> H0 Hx0 Hmn; rewrite !big_mkord.
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

Lemma powerRZ_1_even (k : Z) : (0 <= powerRZ (-1) (2 * k))%Re.
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
          @ITaylor_Lagrange (Xlift (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
        have [|||c [H1 [H2 H3]]] := TL =>//.
          move=> k t Ht; rewrite toR_toXreal.
          case: k => [//|k]; rewrite -ex_derive_nSS.
          exact: (Hder_n k.+2).
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
          @ITaylor_Lagrange (Xlift (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
        have [|||c [H1 [H2 H3]]] := TL =>//.
          move=> k t Ht; rewrite toR_toXreal.
          case: k => [//|k]; rewrite -ex_derive_nSS.
          exact: (Hder_n k.+2).
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
    @ITaylor_Lagrange (Xlift (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
  have [|||c [H1 [H2 H3]]] := TL =>//.
    move=> k t Ht; rewrite toR_toXreal.
    case: k => [//|k]; rewrite -ex_derive_nSS.
    exact: (Hder_n k.+2).
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
      @ITaylor_Lagrange (Xlift (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
    have [|||c [H1 [H2 H3]]] := TL =>//.
      move=> k t Ht; rewrite toR_toXreal.
      case: k => [//|k]; rewrite -ex_derive_nSS.
      exact: (Hder_n k.+2).
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
      @ITaylor_Lagrange (Xlift (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
    have [|||c [H1 [H2 H3]]] := TL =>//.
      move=> k t Ht; rewrite toR_toXreal.
      case: k => [//|k]; rewrite -ex_derive_nSS.
      exact: (Hder_n k.+2).
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
  @ITaylor_Lagrange (Xlift (Derive f0)) (I.convert X) n.-1  _ x0 x _ _.
have [|||c [H1 [H2 H3]]] := TL =>//.
  move=> k t Ht; rewrite toR_toXreal.
  case: k => [//|k]; rewrite -ex_derive_nSS.
  exact: (Hder_n k.+2).
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
      exact/intvlP.
      case/(_ _ inGamma): Hmain =>->.
      exact: Rle_refl.
  - right; move=> x Hx.
    have inGamma : Gamma >: g x.
      rewrite /g -(Poly_nth _ (n:=n.+1)) //.
      apply: IPoly_nth =>//.
      exact/intvlP.
      exact/intvlP.
      move/(_ _ inGamma) in Hmain.
      exact: proj2 Hmain.
  - left; move=> x Hx.
    have inGamma : Gamma >: g x.
      rewrite /g -(Poly_nth _ (n:=n.+1)) //.
      apply: IPoly_nth =>//.
      exact/intvlP.
      exact/intvlP.
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
  (RPA (IP X0 n) (Ztech IP (IP X0 n) F X0 X n)) xf.
Proof.
move=> Hsubs Hne.
case E1 : (isNNegOrNPos (Pol.nth (IP X n.+1) n.+1)); last first.
  rewrite (ZtechE1 _ _ _ E1).
  exact: i_validTM_TLrem.
case E2 : (I.bounded X); last first.
  rewrite (ZtechE2 _ _ _ _ _ E2).
  exact: i_validTM_TLrem.
set err := Ztech IP (IP X0 n) F X0 X n.
have [r' Hr'0] := Hne.
have Hr' : contains (I.convert X) (Xreal r').
  exact: subset_contains Hsubs _ Hr'0.
pose x' := Xreal r'.
have XNNan : I.convert X <> IInan.
  apply I.bounded_correct in E2.
  now rewrite (proj2 (I.lower_bounded_correct _ _)).
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

Lemma size_TM_cst X c : Pol.size (approx (TM_cst X c)) = 1.
Proof. by rewrite /TM_cst Pol.polyCE Pol.size_polyCons Pol.size_polyNil. Qed.

Theorem TM_cst_correct (ci X0 X : I.type) (c : ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  contains (I.convert ci) c ->
  i_validTM (I.convert X0) (I.convert X) (TM_cst X ci) (Xmask c).
Proof.
move=> Hsubset [t Ht] Hc.
split=>//=.
  move=> x Hx Nx; apply/eqNaiP; rewrite I.mask_propagate_r //.
  by case: c Hc Nx; first move/contains_Xnan.
  by move=> HX; rewrite I.mask_propagate_l // I.mask_propagate_r.
  case Eci: (I.convert ci) => [|rci].
    by rewrite I.mask_propagate_r.
  case Ec: c Hc => [|rc] Hc.
    by rewrite I.mask_propagate_r //; apply/contains_Xnan.
    change (Xreal 0%R) with (Xmask (Xmask (Xreal 0%R) (Xreal t)) (Xreal rc)).
    repeat apply: I.mask_correct =>//.
    exact: cont0.
    exact: subset_contains Hsubset _ _.
move=> x0 Hx0.
case: c Hc => [|c]; first move/contains_Xnan; move => Hc.
exists (PolR.polyC 0%R); first by apply: Pol.polyC_correct; rewrite Hc.
  by move=> x Hx; rewrite I.mask_propagate_r.
exists (PolR.polyC c); first exact: Pol.polyC_correct.
move=> x Hx /=.
rewrite Xreal_sub Xreal_toR //=.
rewrite Rmult_0_l Rplus_0_l Rminus_diag_eq //.
change (Xreal 0) with (Xmask (Xmask (Xreal 0) (Xreal t)) (Xreal c)).
repeat apply: I.mask_correct =>//.
exact: cont0.
exact: subset_contains Hsubset _ _.
Qed.

Theorem TM_cst_correct_strong (ci X0 X : I.type) (f : ExtendedR -> ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  is_const f X ci ->
  i_validTM (I.convert X0) (I.convert X) (TM_cst X ci) f.
Proof.
move=> Hsubset Hne [c H1 H2].
apply: TM_fun_eq; last apply: TM_cst_correct Hsubset Hne H1.
move=> x Hx /=; by rewrite H2.
Qed.

(** Return a dummy Taylor model of order [n] that contains every point of [Y] *)
Definition TM_any (Y : I.type) (X : I.type) (n : nat) :=
  let pol := Pol.polyC (Imid Y) in
  {| approx := if n == 0 then pol
               else Pol.set_nth pol n Pol.Int.zero;
     error := I.mask (I.sub prec Y (Imid Y)) X
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
by move=> HX; rewrite I.mask_propagate_r.
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

Lemma size_TM_var X X0 : Pol.size (approx (TM_var X X0)) = 2.
Proof.
rewrite /TM_var Pol.size_set_nth
Pol.polyXE Pol.size_lift Pol.oneE Pol.polyCE.
by rewrite Pol.size_polyCons Pol.size_polyNil.
Qed.

Lemma TM_var_correct X0 X :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_var X X0) (fun x => x).
Proof.
move=> Hsubs [t Ht].
split=>//.
  by move=> HX; rewrite I.mask_propagate_r.
  change (Xreal 0) with (Xmask (Xreal 0) (Xreal t)).
  apply: I.mask_correct. 
  exact: cont0.
  exact: subset_contains Hsubs _ _.
move=> x0 Hx0 /=.
exists (PolR.set_nth PolR.polyX 0 x0).
  apply: Pol.set_nth_correct =>//.
  exact: Pol.polyX_correct.
move=> x Hx /=; rewrite Xreal_sub Xreal_toR //=.
rewrite Rmult_0_l Rplus_0_l Rmult_1_l.
step_xr (Xmask (Xreal 0) (Xreal x)).
  apply: I.mask_correct =>//; exact: cont0.
simpl; congr Xreal; ring.
Qed.

Theorem TM_var_correct_strong X0 X (f : ExtendedR -> ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  (forall x : R, contains (I.convert X) (Xreal x) -> f (Xreal x) = (Xreal x)) ->
  i_validTM (I.convert X0) (I.convert X) (TM_var X X0) f.
Proof.
move=> Hsubset Hne Hid.
apply: TM_fun_eq; last apply: TM_var_correct Hsubset Hne.
by move=> *; rewrite /defined Hid.
Qed.

Lemma size_TM_exp X0 X (n : nat) : Pol.size (approx (TM_exp X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec1. Qed.

Lemma TM_exp_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_exp X0 X n) Xexp.
Proof.
move=> Hsubset Hex.
apply i_validTM_Ztech with (TR.T_exp tt); last 2 first =>//.
exact: I.exp_correct.
constructor.
- by move=> *; rewrite PolR.size_rec1.
- { move=> {X0 n Hsubset Hex} x n k Hx Hk; rewrite toR_toXreal /PolR.nth.
    elim: k Hk => [|k IHk] Hk.
    - by rewrite (nth_rec1up_indep _ _ _ 0%R (m2 := 0)) //= Rdiv_1.
      rewrite (nth_rec1up_indep _ _ _ 0%R (m2 := k)) // in IHk; last exact: ltnW.
      rewrite (nth_rec1up_indep _ _ _ 0%R (m2 := k.+1)) // nth_rec1upS.
      rewrite {}IHk /TR.exp_rec; last exact: ltnW.
      rewrite !(is_derive_n_unique _ _ _ _ (is_derive_n_exp _ _)).
      rewrite fact_simpl mult_INR.
      field_simplify; first apply: Rdiv_eq_reg; try ring;
        by repeat first [ split
                        | apply: Rmult_neq0
                        | apply: not_0_INR
                        | apply: pow_nonzero
                        | apply: Rsqr_plus1_neq0
                        | apply: fact_neq_0 ].
  }
constructor.
- by move=> *; rewrite PolR.size_rec1 Pol.size_rec1.
- { move => {X0 X n Hsubset Hex} X0 xi0 n Hx.
    apply: Pol.rec1_correct =>//.
    by move=> *;
      repeat first [apply: R_div_correct
                   |apply: R_from_nat_correct
                   ].
    exact: R_exp_correct.
  }
- done.
- move=> {n} n x Hx; eapply ex_derive_n_is_derive_n; exact: is_derive_n_exp.
Qed.

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

Lemma size_TM_sin X0 X (n : nat) : Pol.size (approx (TM_sin X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec2. Qed.

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
- move=> x m k Dx Hk; rewrite /TR.T_sin toR_toXreal.
  rewrite /PolR.nth /PolR.rec2; clear - Hk.
  { move: k Hk; apply: nat_ind2.
    - by move=> _; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 0)) //= Rdiv_1.
    - move=> Hm; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 1)) //=.
      (* typical script: *)
      by rewrite Rdiv_1; symmetry; apply: is_derive_unique; auto_derive; auto with real.
    - move=> k Hk0 Hk1 Hm.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k.+2)) // nth_rec2upSS'.
      rewrite /TR.sin_rec in Hk0 Hk1 *.
      set F := (fun (a _ : FullR.T) (n : nat) => - a / (INR n * INR n.-1))%R in Hk0 Hk1 *.
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

Lemma size_TM_cos X0 X (n : nat) : Pol.size (approx (TM_cos X0 X n)) = n.+1.
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
- move=> x m k Dx Hk; rewrite /TR.T_cos toR_toXreal.
  rewrite /PolR.nth /PolR.rec2; clear - Hk.
  { move: k Hk; apply: nat_ind2.
    - by move=> _; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 0)) //= Rdiv_1.
    - move=> Hm; rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := 1)) //=.
      (* typical script: *)
      by rewrite Rdiv_1; symmetry; apply: is_derive_unique; auto_derive; auto with real.
    - move=> k Hk0 Hk1 Hm.
      rewrite (nth_rec2up_indep _ _ _ _ 0%R (m2 := k.+2)) // nth_rec2upSS'.
      rewrite /TR.cos_rec in Hk0 Hk1 *.
      set F := (fun (a _ : FullR.T) (n : nat) => - a / (INR n * INR n.-1))%R in Hk0 Hk1 *.
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
- { (* The proof of this goal might be shortened by reusing is_derive_n_atan *)
    move=> {X0 n Hsubset Hex} x n k Hx H;
    rewrite /TR.T_atan /PolR.nth /PolR.grec1
      (nth_grec1up_indep _ _ _ _ _ 0%R (m2 := k)) //
      nth_grec1up_last.
    case: k H => [|k H]; first by rewrite /= ?Rdiv_1.
    rewrite last_grec1up // head_gloop1.
    rewrite [size _]/= subn1 [_.+1.-1]/=.
    elim: k H x {Hx} =>[|k IHk] H x.
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
        rewrite IHk /Rdiv Rmult_assoc Rinv_l ?Rmult_1_r //.
        exact: INR_fact_neq_0.
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
      suff->: forall x, (x * INR (fact k.+1) / INR (fact k.+2) = x / INR k.+2)%R.
      suff->: INR (k.+1).*2 = (2 * INR k.+1)%R.
      suff->: (((1 + x * x) ^ k.+1) ^ 2 = (1 + x * x) ^ k.+2 * (1 + x * x) ^ k)%R.
      suff->: (((1 + x * x) ^ k.+1) = (1 + x ^ 2) * (1 + x * x) ^ k)%R.
      * by field_simplify; first apply: Rdiv_eq_reg; first ring;
        repeat first [ split
                     | apply: Rmult_neq0
                     | apply: not_0_INR
                     | apply: pow_nonzero
                     | apply: Rsqr_plus1_neq0].
      * by rewrite /= Rmult_1_r.
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
- by move=> m x Hx; apply: ex_derive_n_is_derive_n (is_derive_n_atan m x).
Qed.

Definition TM_tan X0 X (n : nat) : rpa :=
  let P := (T_tan prec X0 n) in
  let ic := I.cos prec X in
  if apart0 ic
  then RPA P (Ztech (T_tan prec) P (I.tan prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_tan X0 X (n : nat) : Pol.size (approx (TM_tan X0 X n)) = n.+1.
Proof. by rewrite /TM_tan; case: apart0; rewrite Pol.size_grec1. Qed.

(* Erik: This lemma could be generalized... *)
Lemma toR_tan : forall x, defined Xtan x -> toR_fun Xtan x = tan x.
Proof. by rewrite /defined /Xtan /toR_fun /proj_fun => x /=; case: is_zero. Qed.

Lemma def_tan : forall x, defined Xtan x <-> cos x <> R0.
Proof.
by move=> x; split; rewrite /defined /Xtan /=; case E0: is_zero =>//;
  move: E0; case: is_zero_spec.
Qed.

Lemma TM_tan_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_tan X0 X n) Xtan.
Proof.
move=> Hsubset Hex.
rewrite /TM_tan.
case E0: apart0.

apply i_validTM_Ztech with (TR.T_tan tt); last 2 first =>//.
exact: I.tan_correct.
constructor.
- by move=> ? ?; rewrite PolR.size_grec1.
- { (* The proof of this goal might be shortened by reusing is_derive_n_tan *)
    move=> {X0 n Hsubset Hex} x n k Hx H;
    rewrite /TR.T_tan /PolR.nth /PolR.grec1
      (nth_grec1up_indep _ _ _ _ _ 0%R (m2 := k)) //
      nth_grec1up_last.
    have->: Derive_n (toR_fun Xtan) k x = Derive_n tan k x.
      apply: (@Derive_n_ext_loc _ tan).
      have Hdef : cos x <> 0%R.
        move/apart0_correct in E0.
        by apply: E0; apply: R_cos_correct.
      eapply locally_open with
        (1 := open_comp cos (fun y => y <> 0%R)
          (fun y _ => continuous_cos y)
        (open_neq R0)) (3 := Hdef).
      move=> {Hdef Hx x} x Hdef.
      by rewrite toR_tan // def_tan.
    rewrite last_grec1up // head_gloop1.
    rewrite [size _]/= subn0.
    have Hdef : cos x <> 0%R.
      move/apart0_correct in E0.
      by apply: E0; apply: R_cos_correct.
    elim: k H x {Hx} Hdef =>[|k IHk] H x Hdef.
    + by rewrite /= !Rsimpl.
    + move/ltnW in H; move/(_ H) in IHk.
      rewrite [INR]lock [PolR.lift]lock [fact]lock /= -!lock.
      set qk := iteri k
        (fun i c => PolR.div_mixed_r tt _ (INR (i + 0).+1)) (PolR.lift 1 PolR.one) in IHk *.
      rewrite (@Derive_ext_loc _ (fun x => qk.[tan x] * INR (fact k))%R);
        first last.
        eapply locally_open with
          (1 := open_comp cos (fun y => y <> 0%R)
            (fun y _ => continuous_cos y)
          (open_neq 0%R)) (3 := Hdef).
        move=> t Hdef'; move/(_ t Hdef') in IHk.
        rewrite IHk /Rdiv Rmult_assoc Rinv_l ?Rmult_1_r //.
        exact: INR_fact_neq_0.
      clear IHk.
      rewrite PolR.horner_div_mixed_r.
      rewrite PolR.horner_add addn0.
      rewrite !PolR.horner_lift Derive_scal_l.
      rewrite Derive_comp; first last.
      * by eexists; apply: is_derive_tan.
      * exact: PolR.ex_derive_horner.
      rewrite !PolR.Derive_horner.
      rewrite (is_derive_unique _ _ _ (is_derive_tan _ Hdef)).
      rewrite /Rdiv Rmult_assoc.
      rewrite -simpl_fact Rinv_involutive.
      by ring_simplify.
      exact: INR_fact_neq_0.
    }
constructor.
- by move=> *; rewrite PolR.size_grec1 Pol.size_grec1.
- { move => {X0 X n Hsubset Hex E0} X0 xi0 n Hx.
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
                       apply: Pol.one_correct|
                       apply: R_tan_correct].
    + apply: Pol.lift_correct; exact: Pol.one_correct.
    + move=> [/=|k]; rewrite /PolR.nth ?nth_default //; exact: cont0.
  }
- { move => {X0 X n Hsubset Hex E0} X x Hx Dx n k Hk.
    apply/eqNaiP/Pol.grec1_propagate =>//.
      move=> q _; apply/eqNaiP.
      apply/Pol.horner_propagate/contains_Xnan.
      move/definedPn: Dx =><-.
      exact: I.tan_correct.
    by rewrite Pol.size_grec1.
  }
- move=> m x Hx; move/apart0_correct in E0.
  move/(_ (cos x) (R_cos_correct _ Hx)) in E0.
  eapply (@ex_derive_n_ext_loc tan); last first.
    exact: ex_derive_n_is_derive_n (is_derive_n_tan m x E0).
  eapply locally_open with
    (1 := open_comp cos (fun y => y <> 0%R)
      (fun y _ => continuous_cos y)
    (open_neq 0%R)) (3 := E0).
  by move=> *; rewrite toR_tan //; apply/def_tan.

simpl.
split =>//.
by move=> *; apply/eqNaiP; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_tan tt x0 n); last by rewrite I.nai_correct.
apply: Pol.grec1_correct;
  by repeat first [move=> *; apply: Pol.div_mixed_r_correct
                  |apply: Pol.add_correct
                  |apply: Pol.deriv_correct
                  |apply: Pol.lift_correct
                  |apply: Pol.deriv_correct
                  |apply: R_from_nat_correct
                  |move=> *; apply: Pol.horner_correct
                  |apply: R_tan_correct
                  |apply: Pol.lift_correct
                  |apply: Pol.one_correct
                  |move=> [|k]; rewrite /PolR.nth ?nth_default //; exact: cont0
                  ].
Qed.

(*
Definition Ztech_sqrt prec P X0 X :=
  let F := I.sqrt prec in
  let a := I.lower X in let b := I.upper X in
  let A := I.bnd a a in let B := I.bnd b b in
  (* If need be, we could replace Pol.horner with Bnd.ComputeBound *)
  let Da := I.sub prec (F A) (Pol.horner prec P (I.sub prec A X0)) in
  let Db := I.sub prec (F B) (Pol.horner prec P (I.sub prec B X0)) in
  let Dx0 := I.sub prec (F X0) (Pol.nth P 0) (* :-D *) in
  I.join (I.join Da Db) Dx0.
*)

Definition TM_sqrt X0 X (n : nat) : rpa :=
  (* assuming X0 \subset X *)
  let P := (T_sqrt prec X0 n) in
  if gt0 X
  then RPA P (Ztech (T_sqrt prec) P (I.sqrt prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_sqrt X0 X (n : nat) : Pol.size (approx (TM_sqrt X0 X n)) = n.+1.
Proof.
by rewrite /TM_sqrt;
  case: gt0; rewrite Pol.size_rec1.
Qed.

Lemma toR_sqrt x : (0 <= x)%R -> sqrt x = toR_fun Xsqrt x.
Proof. by move=> Hx; rewrite /toR_fun /proj_fun /Xsqrt /Xbind negativeF. Qed.

Lemma TM_sqrt_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_sqrt X0 X n) Xsqrt.
Proof.
move=> Hsubset Hex.
rewrite /TM_sqrt.
case E1: gt0.

apply i_validTM_Ztech with (TR.T_sqrt tt); last 2 first =>//.
exact: I.sqrt_correct.
constructor.
- by move=> *; rewrite PolR.size_rec1.
- { move=> {X0 n Hsubset Hex} x n k Hx Hkn.
    rewrite (Derive_n_ext_loc _ sqrt); last first.
      apply: (locally_open (fun t => 0 < t)%R);
        [exact: open_gt| |exact: gt0_correct E1].
      by move=> y Hy; rewrite toR_sqrt //; apply: Rlt_le.
      rewrite /PolR.nth; elim: k Hkn => [|k IHk] Hkn.
        by rewrite rec1up_co0 /= Rdiv_1.
      rewrite nth_rec1up ifF; last by apply: negbTE; rewrite ltnNge Hkn.
      move/(_ (ltnW Hkn)) in IHk.
      rewrite nth_rec1up ifF in IHk; last by apply: negbTE; rewrite ltnNge ltnW.
      rewrite iteriS IHk /TR.sqrt_rec.
      have gt0_x : (0 < x)%R by move/(gt0_correct Hx) in E1.
      rewrite !(is_derive_n_unique _ _ _ _ (is_derive_n_sqrt _ _ gt0_x)).
      rewrite big_ord_recr.
      set big := \big[Rmult/1%Re]_(i < k) _.
      simpl (Rmul_monoid _ _).
      rewrite fact_simpl mult_INR !addn1.
      have->: (/2 - INR k.+1 = /2 - INR k + (- 1))%R
        by rewrite -addn1 plus_INR /=; ring.
      rewrite Rpower_plus Rpower_Ropp Rpower_1 // /Rdiv.
      have->: ((/ 2 - INR k) = (INR 1 - INR 2 * INR k.+1.-1) / INR 2)%R
        by simpl; field.
      move/(gt0_correct Hx)/Rgt_not_eq in E1.
      field_simplify; done || (repeat split;
        repeat first [apply: INR_fact_neq_0 | by simpl; discrR | apply: not_0_INR ]).
  }
constructor.
- by move=> *; rewrite PolR.size_rec1 Pol.size_rec1.
- { move => {X0 X n Hsubset Hex E1} X0 xi0 n Hx.
    apply: Pol.rec1_correct =>//.
    by move=> *;
      repeat first [apply: R_div_correct
                   |apply: R_mul_correct
                   |apply: R_sub_correct
                   |apply: I.fromZ_correct
                   |apply: R_mul_correct
                   |apply: I.fromZ_correct
                   |apply: R_from_nat_correct
                   ].
    exact: R_sqrt_correct.
  }
- move=> I r Ir /definedPn /= {E1 Hex Hsubset X X0 n}.
  case: ifP=> // neg_r _ m k leqmk.
  apply/eqNaiP; apply: Pol.rec1_propagate; last by rewrite Pol.size_rec1.
  * move=> qi n Hq. rewrite /sqrt_rec. apply/eqNaiP.
    rewrite I.div_propagate_l // I.mul_propagate_r //; exact:eqNaiP.
  * apply/eqNaiP. apply/contains_Xnan.
    suff <- : Xsqrt (Xreal r) = Xnan by apply: I.sqrt_correct.
    by rewrite /= neg_r.
- { clear - E1.
    move=> n x Hx.
    move/(gt0_correct Hx) in E1.
    apply: (ex_derive_n_ext_loc sqrt).
      apply: locally_open E1; first exact: open_gt.
      simpl=> y Hy; rewrite /Xsqrt /Xbind /toR_fun /proj_fun negativeF //.
      exact: Rlt_le.
    exact: ex_derive_n_is_derive_n (is_derive_n_sqrt n x E1).
  }

simpl.
split =>//.
by move=> *; apply/eqNaiP; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_sqrt tt x0 n).
apply: Pol.rec1_correct.
by move=> *;
  repeat first [apply: R_div_correct
               |apply: R_mul_correct
               |apply: R_sub_correct
               |apply: I.fromZ_correct
               |apply: R_mul_correct
               |apply: I.fromZ_correct
               |apply: R_from_nat_correct
               ].
exact: R_sqrt_correct.
by rewrite I.nai_correct.
Qed.

Definition I_invsqrt prec x := I.inv prec (I.sqrt prec x).

Definition TM_invsqrt X0 X (n : nat) : rpa :=
  (* assuming X0 \subset X *)
  let P := (T_invsqrt prec X0 n) in
  if gt0 X
  then RPA P (Ztech (T_invsqrt prec) P (I_invsqrt prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_invsqrt X0 X (n : nat) :
  Pol.size (approx (TM_invsqrt X0 X n)) = n.+1.
Proof. by rewrite /TM_invsqrt; case: gt0; rewrite Pol.size_rec1. Qed.

Ltac Inc :=
  rewrite (*?*) INR_IZR_INZ -Z2R_IZR;
  apply: I.fromZ_correct.

Lemma toR_invsqrt x : (0 < x)%R -> / sqrt x = toR_fun (fun t => Xinv (Xsqrt t)) x.
Proof.
move=> Hx.
rewrite /toR_fun /proj_fun /Xinv /Xsqrt /Xbind negativeF; last exact: Rlt_le.
rewrite zeroF //.
exact/Rgt_not_eq/sqrt_lt_R0.
Qed.

Lemma TM_invsqrt_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_invsqrt X0 X n)
            (fun x => Xinv (Xsqrt x)).
Proof.
move=> Hsubset Hex.
rewrite /TM_invsqrt.
case E1: gt0.

apply i_validTM_Ztech with (TR.T_invsqrt tt); last 2 first =>//.
move=> Y y Hy; apply: I.inv_correct; exact: I.sqrt_correct.
constructor.
- by move=> *; rewrite PolR.size_rec1.
- { move=> {X0 n Hsubset Hex} x n k Hx Hkn.
    rewrite (Derive_n_ext_loc _ (fun t => / sqrt t)); last first.
      apply: (locally_open (fun t => 0 < t)%R);
        [exact: open_gt| |exact: gt0_correct E1].
      by move=> y Hy; rewrite toR_invsqrt //; apply: Rlt_le.
      rewrite /PolR.nth; elim: k Hkn => [|k IHk] Hkn.
        by rewrite rec1up_co0 /= Rdiv_1.
      rewrite nth_rec1up ifF; last by apply: negbTE; rewrite ltnNge Hkn.
      move/(_ (ltnW Hkn)) in IHk.
      rewrite nth_rec1up ifF in IHk; last by apply: negbTE; rewrite ltnNge ltnW.
      rewrite iteriS IHk /TR.invsqrt_rec.
      have gt0_x : (0 < x)%R by move/(gt0_correct Hx) in E1.
      rewrite !(is_derive_n_unique _ _ _ _ (is_derive_n_invsqrt _ _ gt0_x)).
      rewrite big_ord_recr.
      set big := \big[Rmult/1%Re]_(i < k) _.
      simpl (Rmul_monoid _ _).
      rewrite fact_simpl mult_INR !addn1.
      have->: (-/2 - INR k.+1 = -/2 - INR k + (- 1))%R
        by rewrite -addn1 plus_INR /=; ring.
      rewrite Rpower_plus Rpower_Ropp Rpower_1 // /Rdiv.
      have->: (-/ 2 - INR k = - (INR 1 + INR 2 * INR k.+1.-1) / INR 2)%R
        by simpl; field.
      move/(gt0_correct Hx)/Rgt_not_eq in E1.
      field_simplify; done || (repeat split;
        repeat first [apply: INR_fact_neq_0 | by simpl; discrR | apply: not_0_INR ]).
  }
constructor.
- by move=> *; rewrite PolR.size_rec1 Pol.size_rec1.
- { move => {X0 X n Hsubset Hex E1} X0 xi0 n Hx.
    apply: Pol.rec1_correct =>//.
by move=> *;
  repeat first [apply: R_div_correct
               |apply: R_mul_correct
               |apply: R_sub_correct
               |apply: I.fromZ_correct
               |apply: R_mul_correct
               |apply: I.fromZ_correct
               |apply/eqNaiPy: R_from_nat_correct
               |apply: R_add_correct
               |apply: R_neg_correct
               |Inc
               ].
    apply: R_inv_correct; exact: R_sqrt_correct.
  }
- move=> I r Ir /definedPn {X0 X n Hsubset Hex E1} Dx n k Hkn.
  apply/eqNaiP; apply: Pol.rec1_propagate.
  - move=> q m Hq; rewrite /invsqrt_rec.
    apply/eqNaiP; rewrite I.div_propagate_l //.
    rewrite I.mul_propagate_r //; exact:eqNaiP.
  - apply/eqNaiP/contains_Xnan; rewrite -Dx.
    exact/I.inv_correct/I.sqrt_correct.
    by rewrite Pol.size_rec1.
- { clear - E1.
    move=> n x Hx.
    move/(gt0_correct Hx) in E1.
    apply: (ex_derive_n_ext_loc (fun t => / sqrt t)).
      apply: locally_open E1; first exact: open_gt.
      simpl=> y Hy; rewrite /Xsqrt /Xinv /Xbind /toR_fun /proj_fun negativeF ?zeroF //.
      apply: Rgt_not_eq; exact: sqrt_lt_R0.
      exact: Rlt_le.
    exact: ex_derive_n_is_derive_n (is_derive_n_invsqrt n x E1).
  }

constructor =>//.
by move=> *; apply/eqNaiP; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_invsqrt tt x0 n).
apply: Pol.rec1_correct.
by move=> *;
  repeat first [apply: R_div_correct
               |apply: R_mul_correct
               |apply: R_sub_correct
               |apply: I.fromZ_correct
               |apply: R_mul_correct
               |apply: I.fromZ_correct
               |apply/eqNaiPy: R_from_nat_correct
               |apply: R_add_correct
               |apply: R_neg_correct
               |Inc
               ].
by apply: R_inv_correct; apply: R_sqrt_correct.
by rewrite I.nai_correct.
Qed.

Definition TM_power_int (p : Z) X0 X (n : nat) :=
  let P := (T_power_int prec p X0 n) in
  if p is Z.neg _ then
    if apart0 X then
      RPA P (Ztech (T_power_int prec p) P
                   (fun x => I.power_int prec x p) X0 X n)
    else RPA P I.nai
  else RPA P (Ztech (T_power_int prec p) P
                    (fun x => I.power_int prec x p) X0 X n).

Lemma size_TM_power_int (p : Z) X0 X (n : nat) :
  Pol.size (approx (TM_power_int p X0 X n)) = n.+1.
Proof.
rewrite /TM_power_int.
case: p => [|p|p]; last case: apart0;
  by rewrite (@Pol.size_dotmuldiv (n.+1)) ?(Pol.size_rec1, size_rec1up).
Qed.

Lemma toR_power_int p x : (0 <= p)%Z \/ x <> R0 ->
  powerRZ x p = toR_fun (Xpower_int^~ p) x.
Proof.
case => [Hp|Hx].
  rewrite /toR_fun /proj_fun /powerRZ /Xpower_int /defined /=.
  by case: p Hp =>// p [].
rewrite /toR_fun /proj_fun /powerRZ /Xpower_int /defined /=.
by case: p =>//; rewrite zeroF.
Qed.

Lemma toR_power_int_loc p x : (0 <= p)%Z \/ x <> R0 ->
  locally x (fun t => powerRZ t p = toR_fun (Xpower_int^~ p) t).
Proof.
case: p => [|p|p] Hx.
- eapply (locally_open (fun _ => True)) =>//; exact: open_true.
- eapply (locally_open (fun _ => True)) =>//; exact: open_true.
- eapply (@locally_open _ (fun x => x <> 0)%R) =>//; first exact: open_neq.
  by move=> {x Hx} x Hx; rewrite /toR_fun /Xpower_int /proj_fun /= zeroF //.
  move: Hx; rewrite /defined /Xpower_int /proj_fun /=; case =>//.
  by case.
Qed.

Lemma TM_power_int_correct_aux (p : Z) X0 X n :
  (0 <= p)%Z \/ apart0 X ->
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (let P := (T_power_int prec p X0 n) in
                                          RPA P (Ztech
                                                   (T_power_int prec p) P
                                                   (fun x => I.power_int prec x p)
                                                   X0 X n))
            (fun x => Xpower_int x p).
Proof.
move=> Hyp Hsubset Hex.
apply i_validTM_Ztech with (TR.T_power_int tt p); last 2 first =>//.
exact: I.power_int_correct.
constructor.
- by move=> {n} ? n;
    rewrite ?(@PolR.size_dotmuldiv n.+1, @Pol.size_dotmuldiv n.+1,
    Pol.size_rec1, size_rec1up, PolR.size_rec1) //.
- { move=> x m k Hx Hk.
    rewrite /TR.T_power_int PolR.nth_dotmuldiv ifF; last first.
      rewrite PolR.size_rec1.
      rewrite size_falling_seq size_fact_seq.
      by rewrite !orbb ltnNge Hk.
    case: k Hk => [|k] Hk.
      simpl Derive_n; simpl INR; rewrite Rdiv_1.
      rewrite falling_seq_correct // fact_seq_correct //.
      rewrite big_mkord big_ord0.
      rewrite [PolR.nth _ _]nth_rec1up /= Rdiv_1 Rmult_1_l.
      rewrite toR_power_int //.
      by case: Hyp => [Hyp|Hyp]; by [left|right; exact: apart0_correct Hyp].
    rewrite -(Derive_n_ext_loc _ _ k.+1 x (toR_power_int_loc _));
      last by case: Hyp => [Hyp|Hyp]; by [left|right; exact: apart0_correct Hyp].
    symmetry; apply: (Rmult_eq_reg_r (INR (fact k.+1))); last exact: INR_fact_neq_0.
    rewrite {1}/Rdiv Rmult_assoc Rinv_l ?Rmult_1_r; last exact: INR_fact_neq_0.
    clear - Hyp Hk Hx.
    rewrite /powerRZ.
    case: p Hyp Hx =>[|p|p] Hyp Hx.
    - rewrite Derive_n_const.
      rewrite /PolR.nth /PolR.rec1 nth_rec1up ifF; last first.
        by apply: negbTE; rewrite ltnNge Hk.
      rewrite iteriS /TR.pow_aux_rec ifF ?(Rmult_0_r, Rmult_0_l) //.
      apply: negbTE; rewrite negb_or /=; apply/negP; move/Z.geb_le.
      by change Z0 with (Z.of_nat O); move/Nat2Z.inj_le/leP; rewrite addn1.
    - rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_pow _ _ _ _)); last first.
        exact/ltP/Pos2Nat.is_pos.
      rewrite falling_seq_correct // fact_seq_correct //.
      have Hpow: PolR.nth (PolR.rec1
        (TR.pow_aux_rec tt (Z.pos p) x) (x ^ Pos.to_nat p) m)%R k.+1 =
        if (Z.of_nat (k + 1) <=? Z.pos p)%Z then (x ^ (Pos.to_nat p - k.+1))%R
        else 0%R.
        rewrite /PolR.nth /PolR.rec1 nth_rec1up.
        rewrite ifF; last first.
          by apply: negbTE; rewrite ltnNge Hk.
        case: Z.leb_spec.
          move=> /Zle_is_le_bool Hpk; rewrite iteriS /TR.pow_aux_rec Z.geb_leb Hpk.
          rewrite orbT pow_powerRZ; congr powerRZ.
          rewrite Nat2Z.inj_sub ?(positive_nat_Z, addn1) //.
          apply/Nat2Z.inj_le; rewrite positive_nat_Z -addn1.
          by move: Hpk; case: Z.leb_spec.
        move=> Hpk; rewrite iteriS /TR.pow_aux_rec Z.geb_leb ifF //.
        apply: negbTE; rewrite negb_or /=.
        by rewrite -Z.ltb_antisym; move/Zlt_is_lt_bool in Hpk.
      case: (Z.leb_spec (Z.of_nat (k + 1)) (Z.pos p)) => Hpk.
        move/Zle_is_le_bool in Hpk.
        rewrite Hpow Hpk.
        rewrite /Rdiv; ring_simplify (*!*).
        rewrite -INR_Z2R Rmult_assoc Rinv_l; last exact: INR_fact_neq_0.
        rewrite Rmult_1_r Rmult_comm; congr Rmult.
        rewrite (big_morph Z2R (id1 := R1) (op1 := Rmult)) //; last exact: Z2R_mult.
        rewrite big_mkord; apply: eq_bigr => [[i Hi] _].
        rewrite INR_Z2R.
        rewrite Nat2Z.inj_sub ?(positive_nat_Z, addn1) //=.
        apply/leP; rewrite ltnS in Hi.
        apply: leq_trans Hi _.
        move/Zle_is_le_bool in Hpk.
        rewrite -positive_nat_Z in Hpk; move/Nat2Z.inj_le/leP in Hpk.
        by apply: leq_trans _ Hpk; rewrite addn1.
      rewrite [in LHS]big_ord_recr big_mkord [in RHS]big_ord_recr.
      simpl (Rmul_monoid _ _).
      have->: Pos.to_nat p - k = 0.
        rewrite -positive_nat_Z addn1 in Hpk; move/Nat2Z.inj_lt/ltP in Hpk.
        rewrite ltnS in Hpk.
        by apply/eqP; rewrite subn_eq0.
      rewrite !Rsimpl Hpow ifF ?Rsimpl //.
      apply: negbTE.
      by move/Zlt_is_lt_bool: Hpk; rewrite Z.ltb_antisym =>->.
    - rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_inv_pow _ _ _ _ _)); first last.
        case: Hyp; first case =>//.
        by move/apart0_correct; apply.
        exact/ltP/Pos2Nat.is_pos.
      rewrite falling_seq_correct // fact_seq_correct //.
      have Hpow: PolR.nth (PolR.rec1
        (TR.pow_aux_rec tt (Z.neg p) x) (/ x ^ Pos.to_nat p) m)%R k.+1 =
        (/ x ^ (Pos.to_nat p + k.+1))%R.
        rewrite /PolR.nth /PolR.rec1 nth_rec1up.
        rewrite ifF; last first.
          by apply: negbTE; rewrite ltnNge Hk.
        rewrite iteriS /TR.pow_aux_rec addn1 /= Pos.of_nat_succ.
        by rewrite Pos2Nat.inj_add Nat2Pos.id.
      rewrite Hpow.
      rewrite /Rdiv; ring_simplify (*!*).
      rewrite -INR_Z2R Rmult_assoc Rinv_l; last exact: INR_fact_neq_0.
      rewrite Rmult_1_r Rmult_comm; congr Rmult.
      rewrite (big_morph Z2R (id1 := R1) (op1 := Rmult)) //; last exact: Z2R_mult.
      rewrite big_mkord; apply: eq_bigr => [[i Hi] _].
      rewrite INR_Z2R -Z2R_opp; congr Z2R.
      rewrite Nat2Z.inj_add positive_nat_Z.
      by rewrite Z.opp_add_distr.
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
- { move=> {X0 n Hsubset Hex} Y x Hx Dx n k Hk.
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
    move: Dx; rewrite /defined /Xpower_int /Xbind.
    by case Ep: p =>//; case: is_zero =>//; case: m.
    exact: I.power_int_correct.
    match goal with |- is_true ?a => rewrite -(negbK a) negb_or end.
    apply/negP; case/andP => /negbTE H0 /negbTE Hm.
    move: Dx; rewrite /defined /Xpower_int.
    by case: {Hyp} p H0 Hm.
    apply/eqNaiP/contains_Xnan.
    move/definedPn: Dx <-.
    exact: I.power_int_correct.
  }
- move=> k x Hx.
  have [Hp|/(apart0_correct Hx) Nx] := Hyp.
    apply: (ex_derive_n_ext_loc _ _ _ _ (@toR_power_int_loc p x _)).
    by left.
    by apply: ex_derive_n_powerRZ; left.
  apply: (ex_derive_n_ext_loc _ _ _ _ (@toR_power_int_loc p x _)).
  by right.
  by apply: ex_derive_n_powerRZ; right.
Qed.

Lemma TM_power_int_correct (p : Z) X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_power_int p X0 X n)
            (fun x => Xpower_int x p).
Proof.
move=> Hsubs Hnex.
rewrite /TM_power_int.
case Ep: p => [|p'|p']; last case E0: apart0;
  try apply: TM_power_int_correct_aux; intuition.
constructor =>//.
by move=> *; apply/eqNaiP; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_power_int tt (Z.neg p') x0 n).
apply: Pol.dotmuldiv_correct.
by rewrite size_falling_seq size_fact_seq.
apply: Pol.rec1_correct.
rewrite /pow_aux_rec /TR.pow_aux_rec -Ep.
move=> ai a m Ha.
case: ((p <? 0) || (p >=? Z.of_nat m))%Z.
exact: R_power_int_correct.
apply R_mask_correct with x0; done || exact: cont0.
exact: R_power_int_correct.
by move=> x Hx; rewrite I.nai_correct.
Qed.

Definition TM_inv X0 X (n : nat) :=
  let P := (T_inv prec X0 n) in
  if apart0 X then
    RPA P (Ztech (T_inv prec) P (I.inv prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_inv X0 X (n : nat) : Pol.size (approx (TM_inv X0 X n)) = n.+1.
Proof. by rewrite /TM_inv; case: apart0 =>/=; rewrite Pol.size_rec1. Qed.

Lemma toR_inv x : (x <> 0)%R -> Rinv x = toR_fun Xinv x.
Proof. by move=> Hx; rewrite /toR_fun /proj_fun /Xinv /Xbind zeroF. Qed.

Lemma TM_inv_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_inv X0 X n) Xinv.
Proof.
move=> Hsubset Hex.
rewrite /TM_inv /=.
case E0: apart0.

apply i_validTM_Ztech with (TR.T_inv tt); last 2 first =>//.
exact: I.inv_correct.
constructor.
- by move=> {n} ? n; rewrite PolR.size_rec1.
- { move=> {X0 n Hsubset Hex} x n k Hx Hkn.
    rewrite (Derive_n_ext_loc _ Rinv); last first.
      apply: (locally_open (fun t => t <> 0)%R);
        [exact: open_neq| |exact: apart0_correct E0].
      by move=> y Hy; rewrite toR_inv.
      rewrite /PolR.nth; elim: k Hkn => [|k IHk] Hkn.
        by rewrite rec1up_co0 /= Rdiv_1.
      rewrite nth_rec1up ifF; last by apply: negbTE; rewrite ltnNge Hkn.
      move/(_ (ltnW Hkn)) in IHk.
      rewrite nth_rec1up ifF in IHk; last by apply: negbTE; rewrite ltnNge ltnW.
      rewrite iteriS IHk /TR.inv_rec.
      have neq0_x : (x <> 0)%R by move/(apart0_correct Hx) in E0.
      rewrite !(is_derive_n_unique _ _ _ _ (is_derive_n_inv _ _ neq0_x)).
      rewrite big_ord_recr.
      set big := \big[Rmult/1%Re]_(i < k) _.
      simpl (Rmul_monoid _).
      rewrite /Rdiv !Rmult_assoc; congr Rmult.
      rewrite fact_simpl mult_INR.
      rewrite !add1n -[(x ^ k.+2)%R]/(x * x ^ k.+1)%R.
      set Xk1 := (x ^ k.+1)%R.
      set k_ := INR (fact k).
      set k1 := INR k.+1.
      rewrite Rinv_mult_distr //; last exact: pow_nonzero.
      rewrite Rinv_mult_distr; try solve [exact: INR_fact_neq_0|exact: not_0_INR].
      rewrite !Rmult_assoc -Ropp_inv_permute //.
      have->: (- k1 * (/ x * (/ Xk1 * (/ k1 * / k_))))%R =
        ((k1 * / k1) * - (/ x * (/ Xk1 * (/ k_))))%R by ring.
      rewrite Rinv_r; last exact: not_0_INR.
      ring.
  }
constructor.
- by move=> {n} ? ? n; rewrite PolR.size_rec1 Pol.size_rec1.
- { move=> {X0 n Hsubset Hex} X0 x0 n Hx0.
    apply: Pol.rec1_correct; last exact: R_inv_correct.
    move=> ai a m Ha; apply: R_div_correct =>//.
    exact: R_neg_correct.
  }
- { move=> {X0 n Hsubset Hex} Y x Hx Dx n k Hk.
    apply/eqNaiP/Pol.rec1_propagate =>//.
    - move=> q m /eqNaiP Hqm; apply/eqNaiP/contains_Xnan; rewrite /inv_rec.
      by rewrite I.div_propagate_l.
    - apply/eqNaiP/contains_Xnan; move/definedPn: Dx =><-.
      exact: I.inv_correct.
    - by rewrite Pol.size_rec1.
  }
- { move=> {X0 n Hsubset Hex} n x Hx.
    move/(apart0_correct Hx) in E0.
    apply: (ex_derive_n_ext_loc Rinv).
      apply: (locally_open (fun t => t <> 0)%R) =>//.
      exact: open_neq.
      by simpl=> y Hy; rewrite toR_inv.
    exact: ex_derive_n_is_derive_n (is_derive_n_inv n x E0).
  }

split =>//.
by move=> *; apply/eqNaiP; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_inv tt x0 n).
apply: Pol.rec1_correct.
by move=> *;
  repeat first [apply: R_div_correct
               |apply: R_inv_correct
               |apply: R_neg_correct
               ].
exact: R_inv_correct.
by rewrite I.nai_correct.
Qed.

Definition TM_ln X0 X (n : nat) : rpa :=
  let P := (T_ln prec X0 n) in
  if gt0 X then
    RPA P (Ztech (T_ln prec) P (I.ln prec) X0 X n)
  else RPA P I.nai.

Lemma size_TM_ln X0 X (n : nat) : Pol.size (approx (TM_ln X0 X n)) = n.+1.
Proof.
by rewrite /TM_ln; case: gt0; case: n => [|n] /=; rewrite !sizes
  ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1, size_rec1up, size_behead).
Qed.

Lemma toR_ln x : (0 < x)%R -> ln x = toR_fun Xln x.
Proof. by move=> Hx; rewrite /toR_fun /proj_fun /Xln /Xbind positiveT. Qed.

Lemma powerRZ_opp x n :
  x <> 0%R -> powerRZ x (- n) = / (powerRZ x n).
Proof.
move=> Hx.
case: n =>[|p|p] //; first by rewrite Rinv_1.
rewrite Rinv_involutive //.
exact: pow_nonzero.
Qed.

Lemma TM_ln_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_ln X0 X n) Xln.
Proof.
move=> Hsubset Hex.
rewrite /TM_ln.
case E0: gt0.

apply i_validTM_Ztech with (TR.T_ln tt); last 2 first =>//.
exact: I.ln_correct.
constructor.
- by move=> {n} x [|n]; rewrite /TR.T_ln // !sizes
    ?(@PolR.size_dotmuldiv n.+1, PolR.size_rec1, size_rec1up, size_behead).
- { move=> {X0 n Hsubset Hex} x n k Hx Hkn.
    rewrite (Derive_n_ext_loc _ ln); last first.
      apply: (locally_open (fun t => 0 < t)%R);
        [exact: open_gt| |exact: gt0_correct E0].
      by move=> y Hy; rewrite toR_ln.
      rewrite /PolR.nth; case: k Hkn => [|k] Hkn; first by rewrite Rdiv_1.
      case: n Hkn => [|n] Hkn //.
      rewrite [nth _ _ _]PolR.nth_dotmuldiv ifF; last first.
      rewrite PolR.size_rec1.
      rewrite size_falling_seq size_behead size_fact_seq.
      by rewrite !orbb ltnNge -ltnS Hkn.
    move/(gt0_correct Hx) in E0.
    case: k Hkn => [|k] Hkn.
      simpl Derive_n; simpl INR; rewrite Rdiv_1.
      rewrite falling_seq_correct // nth_behead fact_seq_correct //.
      rewrite big_mkord big_ord0.
      rewrite [PolR.nth _ _]nth_rec1up /= Rdiv_1 Rmult_1_l.
      by rewrite (is_derive_unique _ _ _ (is_derive_ln _ E0)) Rmult_1_r.
    symmetry; apply: (Rmult_eq_reg_r (INR (fact k.+2))); last exact: INR_fact_neq_0.
    rewrite {1}/Rdiv Rmult_assoc Rinv_l ?Rmult_1_r; last exact: INR_fact_neq_0.
    rewrite (is_derive_n_unique _ _ _ _ (is_derive_n_ln _ _ _)) //.
    rewrite falling_seq_correct // nth_behead fact_seq_correct //.
    have Hpow: (PolR.nth (PolR.rec1
      (TR.pow_aux_rec tt (-1) x) (powerRZ x (-1)) n)%R k.+1 =
      / x ^ (1 + k.+1))%R.
      rewrite /PolR.nth /PolR.rec1 nth_rec1up.
      rewrite ifF; last first.
        by apply: negbTE; rewrite ltnNge -ltnS Hkn.
      rewrite iteriS /TR.pow_aux_rec.
      suff->: powerRZ x (-1 - Z.of_nat (k + 1))%Z = / (x ^ (1 + k.+1))%R by done.
        rewrite pow_powerRZ -powerRZ_opp; last exact: Rgt_not_eq.
        congr powerRZ; change (-1)%Z with (- Z.of_nat 1)%Z.
        rewrite -Z.add_opp_r -Z.opp_sub_distr -Z.add_opp_r Z.opp_involutive.
        by f_equal; rewrite -Nat2Z.inj_add; f_equal; rewrite plusE addn1.
    rewrite Hpow big_mkord.
    rewrite -INR_Z2R /Rdiv Rmult_assoc.
    rewrite (big_morph Z2R (id1 := R1) (op1 := Rmult)) //; last exact: Z2R_mult.
    set bigRhs := \big[Rmult/1%R]_i Z2R _.
    set fk2 := INR (fact k.+2).
    have->: (bigRhs * / fk2 * (/ x ^ (1 + k.+1) * fk2) =
      (/ fk2 * fk2) * bigRhs * / (x ^ (1 + k.+1)))%R by ring.
    rewrite Rinv_l ?Rmult_1_l; last exact: INR_fact_neq_0.
    congr Rmult; rewrite {}/bigRhs.
    apply: eq_bigr => [[i Hi] _].
    rewrite INR_Z2R.
    rewrite Nat2Z.inj_add -Z2R_opp; congr Z2R.
    simpl Z.of_nat.
    by rewrite Z.opp_add_distr.
  }
constructor.
- by move=> {n X Hsubset E0} X x [|n]; rewrite /TR.T_ln !sizes //=
    ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1,
      @PolR.size_dotmuldiv n.+1, PolR.size_rec1, size_rec1up, size_behead).
- { move=> {X0 n Hsubset Hex} X0 x0 n Hx0.
    rewrite /T_ln /TR.T_ln.
    apply: Pol.polyCons_correct; last exact: R_ln_correct.
    case: n => [|n]; first exact: Pol.polyNil_correct.
    apply: Pol.dotmuldiv_correct;
      first by rewrite size_falling_seq size_behead size_fact_seq.
    apply: Pol.rec1_correct; first move=> *;
      repeat first [apply: R_div_correct
                   |apply: R_power_int_correct
                   |apply: R_ln_correct
                   ];
      exact: (R_mask_correct (ln x0) Hx0 (R_ln_correct prec Hx0)).
  }
- { move=> {X0 n Hsubset Hex} Y x Hx Dx n k Hk; apply/eqNaiP.
    apply: Pol.polyCons_propagate.
    - apply/eqNaiP/contains_Xnan.
      move/definedPn: Dx =><-.
      exact: I.ln_correct.
    - case: n Hk => [|n] Hk m; first by rewrite Pol.size_polyNil.
      rewrite ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1,
               size_falling_seq, size_behead, size_fact_seq) //.
      move=> Hm.
      apply: Pol.dotmuldiv_propagate;
      rewrite ?(size_falling_seq, size_behead, size_fact_seq) ?Pol.size_rec1 //.
      apply: Pol.rec1_propagate.
      move=> q l Hq; apply/eqNaiP; rewrite I.power_int_propagate //.
      rewrite I.mask_propagate_r //.
      by apply/contains_Xnan; move/definedPn: Dx <-; apply: I.ln_correct.
      apply/eqNaiP; rewrite I.power_int_propagate //.
      rewrite I.mask_propagate_r //.
      by apply/contains_Xnan; move/definedPn: Dx <-; apply: I.ln_correct.
      by rewrite ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1,
               size_falling_seq, size_behead, size_fact_seq).
    - rewrite Pol.size_polyCons.
      case: n Hk => [|n] Hk; first by rewrite ltnS Pol.size_polyNil.
      by rewrite ?(@Pol.size_dotmuldiv n.+1, Pol.size_rec1,
               size_falling_seq, size_behead, size_fact_seq).
  }
- { clear - E0.
    move=> n x Hx.
    move/(gt0_correct Hx) in E0.
    apply: (ex_derive_n_ext_loc ln).
      apply: locally_open E0; first exact: open_gt.
      simpl=> t Ht; exact: toR_ln.
    exact: ex_derive_n_is_derive_n (is_derive_n_ln n x E0).
  }
split =>//.
by move=> *; apply/eqNaiP; rewrite I.nai_correct.
by move=> Hx; rewrite /= I.nai_correct.
by rewrite I.nai_correct.
move=> x0 Hx0.
exists (TR.T_ln tt x0 n).
apply: Pol.polyCons_correct; case: n =>[|n]/=; first exact: Pol.polyNil_correct.
- apply: Pol.dotmuldiv_correct;
    first by rewrite size_falling_seq size_behead size_fact_seq.
  apply: Pol.rec1_correct; first move=> *;
    repeat first [apply: R_div_correct
                 |apply: R_power_int_correct
                 |apply: R_ln_correct
                 ];
    exact: (R_mask_correct (ln x0) Hx0 (R_ln_correct prec Hx0)).
- exact: R_ln_correct.
- exact: R_ln_correct.
by rewrite I.nai_correct.
Qed.

(******************************************************************************)
(** The rest of the file is devoted to arithmetic operations on Taylor models *)
(******************************************************************************)

Local Notation "a + b" := (Xadd a b).
Local Notation "a - b" := (Xsub a b).

Lemma TM_add_correct_gen
  (smallX0 : interval) (X : I.type) (TMf TMg : rpa) f g :
  I.subset_ smallX0 (I.convert X) ->
  i_validTM smallX0 (I.convert X) TMf f ->
  i_validTM smallX0 (I.convert X) TMg g ->
  i_validTM smallX0 (I.convert X) (TM_add TMf TMg)
  (fun xr => Xadd (f xr) (g xr)).
Proof.
move=> HinX [Fdef Fnai Fzero Fsubs Fmain] [Gdef Gnai Gzero Gsubs Gmain].
have HL :
   forall x : R,
   X >: x ->
   ~~ defined (fun xr : ExtendedR => f xr + g xr) x -> eqNai (I.add prec (error TMf) (error TMg)).
  move=> x Hx Dx; apply/eqNaiP.
  have [//|Df|Dg] := definedPn2V Dx.
  by move/(_ x Hx Df)/eqNaiP in Fdef; rewrite I.add_propagate_l.
  by move/(_ x Hx Dg)/eqNaiP in Gdef; rewrite I.add_propagate_r.
split=>//=.
by move=> H; move/(_ H) in Fnai; rewrite I.add_propagate_l.
step_xr (Xreal 0 + Xreal 0); by [apply: I.add_correct|rewrite /= Rplus_0_l].
move=> x0 Hx0 /=; move: (Fmain x0 Hx0) (Gmain x0 Hx0) => [pf Hf1 Hf2] [pg Hg1 Hg2].
exists (PolR.add tt pf pg); first exact: Pol.add_correct.
move=> x Hx /=.
rewrite PolR.horner_add Xreal_sub.
(* rewrite Xreal_toR. *)
case E0: (eqNai (I.add prec (error TMf) (error TMg))); first by move/eqNaiP: E0 =>->.
rewrite E0 in HL.
rewrite Xreal_toR // ?Xreal_add; last by apply: contraT; apply: HL.
set fx := f _; set gx := g _; set pfx := _ (pf.[_]); set pgx := _ (pg.[_]).
have->: (fx + gx - (pfx + pgx) = (fx - pfx) + (gx - pgx))%XR.
  rewrite /fx /gx /pfx /pgx.
  case: (f); case: (g); done || move=> * /=; congr Xreal; ring.
rewrite /fx /gx /pfx /pgx.
have Df : defined f x by apply: contraT=> K; exact: HL _ Hx (definedPn2l _ K _).
have Dg : defined g x. apply: contraT=> K; apply: HL _ Hx (definedPn2r _ K _).
  by move=> ?; rewrite Xadd_comm.
rewrite -(Xreal_toR Df) -(Xreal_toR Dg) /=.
apply: R_add_correct.
by have := Hf2 x Hx.
by have := Hg2 x Hx.
Qed.

Lemma TM_add_correct (X0 X : I.type) (TMf TMg : rpa) f g :
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X) (TM_add TMf TMg)
  (fun xr => Xadd (f xr) (g xr)).
Proof.
move=> Hf Hg.
case Hf => [Hdef Hnai Hzero Hsubs Hmain].
exact: TM_add_correct_gen.
Qed.

Lemma TM_opp_correct (X0 X : interval) (TMf : rpa) f :
  i_validTM X0 X TMf f ->
  i_validTM X0 X (TM_opp TMf)
  (fun xr => Xneg (f xr)).
Proof.
move=> [Hdef Hnai Hzero Hsubset /= Hmain].
have HL :
   forall x : R,
   contains X (Xreal x) ->
   ~~ defined (fun xr : ExtendedR => - f xr)%XR x -> eqNai (I.neg (error TMf)).
  move=> x Hx Dx; apply/eqNaiP.
  have Df : ~~ defined f x by apply: (definedPn1T Dx).
  by move/(_ x Hx Df)/eqNaiP in Hdef; rewrite I.neg_propagate.
split=>//.
  by move=> HX; rewrite I.neg_propagate // Hnai.
  rewrite -Ropp_0 Xreal_neg.
  exact: I.neg_correct.
simpl=> x0 Hx0.
move/(_ x0 Hx0) in Hmain.
have [Q H1 H2] := Hmain.
exists (PolR.opp Q); first exact: Pol.opp_correct.
move=> x Hx.
move/(_ x Hx) in H2.
rewrite PolR.horner_opp.
set g := Xreal (toR_fun _ _ - - _)%R.
case E0: (eqNai (I.neg (error TMf))); first by move/eqNaiP: E0 =>->.
rewrite E0 in HL.
suff->: g = Xreal (Ropp ((toR_fun f x) - (Q.[(x - x0)%Re]))%R) by exact: R_neg_correct.
rewrite /g !(Xreal_sub, Xreal_toR, Xreal_neg) //.
by rewrite !(Xsub_split, Xneg_involutive, Xneg_Xadd).
by apply: contraT => K; apply: HL _ Hx (definedPn1TE K _).
by apply: contraT => K; apply: HL _ Hx K.
Qed.

Lemma TM_sub_correct (X0 X : interval (*I.type?*)) (TMf TMg : rpa) f g :
  i_validTM X0 X TMf f ->
  i_validTM X0 X TMg g ->
  i_validTM X0 X (TM_sub TMf TMg)
  (fun xr => Xsub (f xr) (g xr)).
Proof.
move=> [Fdef Fnai Fzero Hsubset /= Fmain] [Gdef Gnai Gzero _ /= Gmain].
have HL :
   forall x : R,
   contains X (Xreal x) ->
   ~~ defined (fun xr : ExtendedR => f xr - g xr) x -> eqNai (I.sub prec (error TMf) (error TMg)).
  move=> x Hx Dx; apply/eqNaiP.
  have [//|Df|Dg] := definedPn2V Dx.
  by move/(_ x Hx Df)/eqNaiP in Fdef; rewrite I.sub_propagate_l.
  by move/(_ x Hx Dg)/eqNaiP in Gdef; rewrite I.sub_propagate_r.
split=>//=.
  by move=> HX; rewrite I.sub_propagate_l // Fnai.
  suff->: Xreal 0 = (Xreal 0 - Xreal 0)%XR by apply: I.sub_correct.
  by rewrite /= Rminus_0_r.
move=> x0 Hx0 /=.
move: (Fmain x0 Hx0) (Gmain x0 Hx0) => [pf Hf1 Hf2] [pg Hg1 Hg2].
exists (PolR.sub tt pf pg); first exact: Pol.sub_correct.
move=> x Hx /=.
rewrite PolR.horner_sub.
case E0: (eqNai (I.sub prec (error TMf) (error TMg))); first by move/eqNaiP: E0 =>->.
rewrite E0 in HL.
rewrite Xreal_sub Xreal_toR ?(Xreal_add, Xreal_neg) //; last by apply: contraT; apply: HL.
set fx := f _; set gx := g _; set pfx := _ (pf.[_]); set pgx := _ (pg.[_]).
have->: (fx - gx - (pfx + (- pgx)) = (fx - pfx) - (gx - pgx))%XR.
  rewrite /fx /gx /pfx /pgx.
  case: (f); case: (g); done || move=> * /=; congr Xreal; ring.
rewrite /fx /gx /pfx /pgx.
have Df : defined f x by apply: contraT=> K; exact: HL _ Hx (definedPn2l _ K _).
have Dg : defined g x. apply: contraT=> K; apply: HL _ Hx (definedPn2r _ K _).
  by move=> ?; rewrite Xsub_Xnan_r.
rewrite -(Xreal_toR Df) -(Xreal_toR Dg) /=.
apply: R_sub_correct.
by have := Hf2 x Hx.
by have := Hg2 x Hx.
Qed.

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

Lemma TM_mul_mixed_correct a M X0 X f (y : R) :
  contains (I.convert a) (Xreal y) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul_mixed a M)
  (fun x => Xmul (Xreal y) (f x)).
Proof.
move=> Hy [Hdef Hnai Hzero Hsubs Hmain].
split=>//.
  move=> x Hx Dx; apply/eqNaiP/contains_Xnan.
  rewrite I.mul_propagate_r //.
  move/definedPn2V: Dx; case=>// H.
  by apply/eqNaiP/(Hdef _ _ H).
  by move=> HX; rewrite I.mul_propagate_r // Hnai.
  have->: (Xreal 0) = (Xmul (Xreal y) (Xreal 0)) by simpl; congr Xreal; ring.
  exact: I.mul_correct.
move=> x0 Hx0.
move/(_ x0 Hx0) in Hmain.
have [q H1 H2] := Hmain.
exists (PolR.map (Rmult y) q).
- apply: Pol.map_correct =>//.
  by rewrite Rmult_0_r.
  by move=> *; apply: R_mul_correct.
- move=> x Hx.
  move/(_ x Hx) in H2.
  rewrite PolR.horner_mul_mixed.
  case Dx : (defined f x).
  set g := Xreal (toR_fun _ _ - _)%R.
  suff->: g = Xreal (Rmult y (toR_fun f x - (q.[(x - x0)]))%R).
    exact: R_mul_correct =>//.
  rewrite /g !(Xreal_mul, Xreal_sub, Xreal_toR, Xreal_neg) //.
  case: (f) =>[//|r] /=; congr Xreal; ring.
  by move: Dx; tac_def1 f.
  rewrite I.mul_propagate_r //.
  exact/eqNaiP/(Hdef _ Hx)/negbT.
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
move=> tHt [[|y] Hy1 Hy2] Hg; move: (Hg) => [Hdef Hnai Hnan Hsubset Hmain].
split=>//.
- move=> x Hx Dx; apply/eqNaiP.
  rewrite I.mul_propagate_l; exact/contains_Xnan.
- by rewrite (TM_mul_mixed_nai Hy1 Hg).
- by rewrite (TM_mul_mixed_nai Hy1 Hg).
- move=> /= x0 Hx0.
  move/(_ x0 Hx0) in Hmain.
  have [q H1 H2] := Hmain.
  exists (PolR.map (Rmult (* dummy *) R0) q).
    apply: Pol.map_correct =>//.
      by rewrite Rmult_0_r.
    move=> *; apply: R_mul_correct =>//.
    by move/contains_Xnan: Hy1 =>->.
  move=> x Hx /=.
  move/(_ x Hx) in H2.
  rewrite I.mul_propagate_l //.
  exact/contains_Xnan.
- apply: TM_fun_eq; last exact: TM_mul_mixed_correct Hy1 Hg.
  move=> x Hx /=.
  by rewrite Hy2.
Qed.

Lemma TM_div_mixed_r_aux0 M b X0 X f :
  contains (I.convert b) (Xreal R0) ->
  i_validTM (I.convert X0) (I.convert X) M f (* hyp maybe too strong *) ->
  i_validTM (I.convert X0) (I.convert X) (TM_div_mixed_r M b)
  (fun x => Xdiv (f x) (Xreal R0)).
Proof.
move=> Hb0 [Hdef Hnai Hzero Hsubs /= Hmain].
have Lem : contains (I.convert (error (TM_div_mixed_r M b))) Xnan.
  rewrite /TM_div_mixed_r.
  simpl.
  rewrite -(Xdiv_0_r (Xreal R0)).
  exact: I.div_correct.
split=>//.
  by move=> x Hx Dx; apply/eqNaiP/contains_Xnan.
  by rewrite (proj1 (contains_Xnan _) Lem).
  by rewrite (proj1 (contains_Xnan _) Lem).
move=> x0 Hx0; have [Q Happrox Herr] := Hmain x0 Hx0.
exists (PolR.map (Rdiv^~ 0)%R Q) =>/=.
apply: Pol.map_correct =>//; first by rewrite /Rdiv Rmult_0_l.
move=> *; exact: R_div_correct.
by move=> x Hx; move/contains_Xnan: Lem ->.
Qed.

Lemma TM_div_mixed_r_correct M b X0 X f (y : R) :
  contains (I.convert b) (Xreal y) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  i_validTM (I.convert X0) (I.convert X) (TM_div_mixed_r M b)
  (fun x => Xdiv (f x) (Xreal y)).
Proof.
have [->|Hy0] := Req_dec y R0.
  exact: TM_div_mixed_r_aux0.
move=> Hy [Hdef Hnai Hzero Hsubs Hmain].
split=>//.
  move=> x Hx Dx; apply/eqNaiP; rewrite /TM_div_mixed_r /=.
  rewrite I.div_propagate_l //; apply/eqNaiP/(Hdef x Hx).
  by move: Dx; tac_def1 f =>//= r; rewrite zeroF.
  by move=> HX; rewrite I.div_propagate_l // Hnai.
  have->: (Xreal 0) = (Xdiv (Xreal 0) (Xreal y)).
  by rewrite /=zeroF //; congr Xreal; rewrite /Rdiv Rmult_0_l.
  exact: I.div_correct.
move=> /= x0 Hx0.
have [q H1 H2] := Hmain x0 Hx0.
exists (PolR.map (Rdiv ^~ y) q).
- apply: Pol.map_correct =>//.
  by rewrite /Rdiv Rmult_0_l.
  by move=> *; apply: R_div_correct.
- move=> x Hx /=.
  move/(_ x Hx) in H2.
  case Df : (defined f x).
    clear - H2 Hy Hy0 Df Hdef Hx.
    set sub2 := Xreal (Rminus _ _).
    set sub1 := Xreal (Rminus _ _) in H2.
    suff->: sub2 = Xdiv sub1 (Xreal y) by exact: I.div_correct.
    rewrite /sub1 /sub2 !(Xreal_sub, Xreal_toR) //.
    rewrite !(Xsub_split, Xdiv_split) Xmul_Xadd_distr_r; congr Xadd.
    by rewrite PolR.horner_div_mixed_r Xreal_div // Xdiv_split Xmul_Xneg_distr_l.
    by move: Df; tac_def1 f =>//= r _; rewrite zeroF.
  move/negbT in Df.
  by rewrite I.div_propagate_l //; apply/eqNaiP/(Hdef x Hx).
Qed.

Lemma TM_div_mixed_r_nai M b f X0 X :
  contains (I.convert b) Xnan ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  I.convert (error (TM_div_mixed_r M b)) = IInan.
Proof.
move/contains_Xnan => Ha /=.
case=>[Hdef Hnai Hnan Hsubst Hmain].
exact: I.div_propagate_r.
Qed.

Corollary TM_div_mixed_r_correct_strong M b X0 X f g :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  is_const g X b ->
  i_validTM (I.convert X0) (I.convert X) (TM_div_mixed_r M b)
  (fun x => Xdiv (f x) (g x)).
Proof.
move=> tHt Hf [[|y] Hy1 Hy2]; move: (Hf) => [Hdef Hnai Hzero Hsubs Hmain].
split=>//=.
- move=> x Hx Dx.
  apply/eqNaiP; rewrite I.div_propagate_r //; exact/contains_Xnan.
- by rewrite (TM_div_mixed_r_nai Hy1 Hf).
- by rewrite (TM_div_mixed_r_nai Hy1 Hf).
- move=> /= x0 Hx0.
  have [q H1 H2] := Hmain x0 Hx0.
  exists (PolR.map (Rdiv ^~ R0) q).
    apply: Pol.map_correct =>//.
    by rewrite /Rdiv Rmult_0_l.
    move=> *; apply: R_div_correct =>//.
    by move/contains_Xnan: Hy1 =>->.
  move=> x Hx /=.
  move/(_ x Hx) in H2.
  rewrite I.div_propagate_r //.
  exact/contains_Xnan.
apply: (@TM_fun_eq (fun x => f x / Xreal y)%XR).
- by move=> x Hx /=; rewrite Hy2.
- exact: TM_div_mixed_r_correct.
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

Lemma Xreal_inj : injective Xreal.
Proof. by move=> x y []. Qed.

Lemma TM_mul_correct_gen
  (smallX0 : interval) (TMf TMg : rpa) f g (X0 X : I.type) n :
  I.subset_ smallX0 (I.convert X0) ->
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty smallX0 ->
  i_validTM smallX0 (I.convert X) TMf f ->
  i_validTM smallX0 (I.convert X) TMg g ->
  i_validTM smallX0 (I.convert X) (TM_mul TMf TMg X0 X n)
  (fun xr => Xmul (f xr) (g xr)).
Proof.
move=> HinX0 HinX [t Ht']
  [Fdef Fnai Fzero Fsubs Fmain] [Gdef Gnai Gzero _ Gmain].
have Ht0 : X0 >: t by apply: (subset_contains smallX0).
have Ht : X >: t by apply: subset_contains Ht'.
have Hf0 := Fmain t Ht'.
have Hg0 := Gmain t Ht'.
split =>//.
- move=> x Hx /definedPn2V [//|Df|Dg].
    apply/eqNaiP; rewrite /= /mul_error.
    do 3![rewrite I.add_propagate_r //].
    by rewrite I.mul_propagate_l //; apply/eqNaiP/(Fdef _ Hx Df).
  apply/eqNaiP; rewrite /= /mul_error.
  do 3![rewrite I.add_propagate_r //].
  by rewrite I.mul_propagate_r //; apply/eqNaiP/(Gdef _ Hx Dg).
- move=> HX; rewrite /TM_mul /= /mul_error.
  rewrite I.add_propagate_r // I.add_propagate_r // I.add_propagate_r //.
  by rewrite I.mul_propagate_l // Fnai.
- have [qf Hf1 Hf2] := Hf0.
  have [qg Hg1 Hg2] := Hg0.
  step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
  apply: R_add_correct.
    apply: (mul_0_contains_0_r _
      (y := (Xreal (PolR.horner tt (PolR.mul_tail tt n qf qg) (t - t)%R))));
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

move=> x0 Hx0 {Hf0 Hg0} /=.
have Hf0 := Fmain x0 Hx0; have Hg0 := Gmain x0 Hx0.
have [pf Hf1 Hf2] := Hf0.
have [pg Hg1 Hg2] := Hg0.
exists (PolR.mul_trunc tt n pf pg); first exact: Pol.mul_trunc_correct.

move=> x Hx.
case Dx : (defined (fun xr : ExtendedR => (f xr * g xr)%XR) x); last first.
  step_xi IInan =>//; rewrite /mul_error; do 3![rewrite I.add_propagate_r //].
  case/negbT/definedPn2V: Dx =>//.
  by move/(Fdef _ Hx)/eqNaiP => H; rewrite I.mul_propagate_l //.
  by move/(Gdef _ Hx)/eqNaiP => H; rewrite I.mul_propagate_r //.
move/(_ x Hx) in Hf2; move/(_ x Hx) in Hg2.
step_r ((PolR.mul_tail tt n pf pg).[x - x0] * (x - x0)^n.+1 +
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
clear - Fdef Gdef Dx Hx.
have Hdfx := Fdef x Hx.
have Hdgx := Gdef x Hx.
set sf := pf.[x - x0]%R.
set sg := pg.[x - x0]%R.

rewrite !PolR.hornerE PolR.size_mul_trunc PolR.size_mul_tail.
rewrite (big_endo (fun r => r * (x-x0) ^ n.+1)%R); first last.
  by rewrite Rmult_0_l.
  by move=> a b /=; rewrite Rmult_plus_distr_r.
rewrite (eq_big_nat _ _ (F2 := fun i =>
  PolR.mul_coeff tt pf pg (i + n.+1) * (x - x0) ^ (i + n.+1))%R);
  last first.
  move=> i Hi; rewrite Rmult_assoc; congr Rmult; last by rewrite pow_add.
  rewrite PolR.nth_mul_tail ifF; first by rewrite addnC.
  by case/andP: Hi; case: leqP.
rewrite -(big_addn 0 _ n.+1 predT (fun i =>
  PolR.mul_coeff tt pf pg i * (x - x0) ^ i)%R).
set e := ((_ f x - sf) * sg + ((_ g x - sg) * sf + (_ f x - sf) * (_ g x - sg)))%R.
rewrite Rplus_comm.
have->: e = ((toR_fun (fun xr => (f xr * g xr))%XR x) - sf * sg)%R.
(* begin flip-flop *)
apply/Xreal_inj.
rewrite ![in RHS](Xreal_sub, Xreal_mul, Xreal_toR) //.
rewrite -![in RHS](Xreal_sub, Xreal_mul, Xreal_toR) // /e.
congr Xreal; ring.
by apply: contraT => /(@definedPn2r Xmul f g) K; rewrite Dx in K;
  apply: K => *; rewrite Xmul_comm.
by apply: contraT => /(@definedPn2l Xmul f g) K; rewrite Dx in K; apply: K.
(* end flip-flop *)
rewrite Rplus_assoc; congr Rplus.
rewrite {}/e {}/sf {}/sg.
rewrite !PolR.hornerE.

apply: (Rplus_eq_reg_r (toR_fun (fun xr => (f xr * g xr))%XR x)).
congr Rplus.
rewrite -!PolR.hornerE /=.
rewrite -PolR.horner_mul PolR.hornerE.
set bign1 := \big[Rplus/0%Re]_(0 <= i < n.+1) _.
apply: (Rplus_eq_reg_r bign1); rewrite Rplus_opp_l /bign1.
set big := \big[Rplus/0%Re]_(0 <= i < _) _.
apply: (Rplus_eq_reg_l big); rewrite -!Rplus_assoc Rplus_opp_r /big Rplus_0_l.
rewrite PolR.size_mul add0n Rplus_0_r.
case: (ltnP n ((PolR.size pf + PolR.size pg).-1)) => Hn.
  rewrite [RHS](big_cat_nat _ _ (n := n.+1)) //=.
  rewrite Rplus_comm; congr Rplus.
  rewrite !big_mkord; apply: eq_bigr.
    move=> [i Hi] _ /=; rewrite PolR.nth_mul_trunc ifF;
      last by apply: negbTE; rewrite -leqNgt.
    rewrite PolR.nth_mul ifF //.
    apply: negbTE; rewrite -ltnNge; rewrite ltnS in Hi.
    exact: leq_ltn_trans Hi Hn.
  rewrite -(add0n n.+1) !big_addn !big_mkord; apply: eq_bigr.
  move=> [i Hi] _ /=; rewrite PolR.nth_mul ifF //.
  apply: negbTE; rewrite -ltnNge.
  by rewrite -addSn leq_addLR.
rewrite -{1}(add0n n.+1) big_addn big_mkord big1; last first.
  move=> [i Hi] _ /=.
  rewrite -subn_eq0 in Hn.
  by rewrite -subn_gt0 subnS (eqP Hn) in Hi.
rewrite Rplus_0_l.
set np := (PolR.size pf + PolR.size pg).-1.
rewrite [in LHS](big_cat_nat _ _ (n := np)) //=;
  last exact: leqW.
set big0 := \big[Rplus/0%R]_(_.-1 <= i < n.+1) _.
have->: big0 = 0%R.
rewrite /big0.
  rewrite /big0 -/np -(add0n np) big_addn big_mkord.
  rewrite big1 // => [[i Hi] _] /=.
  rewrite PolR.nth_mul_trunc ifF; last first.
  rewrite ltn_subRL addnC in Hi.
  by rewrite -ltnS ltnNge Hi.
  rewrite PolR.mul_coeffE PolR.mul_coeff_eq0 ?Rmult_0_l //.
  move=> k Hk.
  case: (leqP (PolR.size pf) k) => Hk0.
    left; rewrite PolR.nth_default //.
  right; rewrite PolR.nth_default //.
  rewrite -leq_addLR //.
  rewrite -(ltn_add2l (PolR.size pg)) [addn (_ pg) (_ pf)]addnC in Hk0.
  move/ltn_leq_pred in Hk0.
  apply: leq_trans Hk0 _.
  by rewrite leq_addl.
rewrite Rplus_0_r !big_mkord; apply: eq_bigr.
move=> [i Hi] _ /=.
rewrite PolR.nth_mul_trunc PolR.nth_mul' ifF ?PolR.mul_coeffE //.
apply: negbTE; rewrite -ltnNge ltnS.
exact: leq_trans (ltnW Hi) Hn.
Qed.

Lemma TM_mul_correct (X0 X : I.type) (TMf TMg : rpa) f g n :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul TMf TMg X0 X n)
  (fun xr => Xmul (f xr) (g xr)).
Proof.
move=> Ht [Hdf Hef H0 Hf] Hg.
apply: TM_mul_correct_gen => //.
exact: subset_refl.
Qed.

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

Definition TM_horner n p (Mf : rpa) (X0 X : I.type) : rpa :=
  @Pol.fold rpa
  (fun a b => (TM_add (TM_cst X a) (TM_mul b Mf X0 X n)))
  (TM_cst X I.zero) p.

Lemma size_TM_horner n p Mf X0 X :
  Pol.size (approx (TM_horner n p Mf X0 X)) = (if 0 < Pol.size p then n else 0).+1.
Proof.
rewrite /TM_horner.
elim/Pol.poly_ind: p =>[|a p IHp].
  by rewrite Pol.fold_polyNil Pol.size_polyNil size_TM_cst.
by rewrite Pol.fold_polyCons Pol.size_polyCons size_TM_add size_TM_mul
  size_TM_cst max1n.
Qed.

(** A padding function to change the size of a polynomial over R while
    keeping the same coefficients. *)
Definition pad pi pr : PolR.T :=
  take (Pol.size pi) (PolR.set_nth pr (Pol.size pi) 0%R).

Lemma size_pad pi pr : eq_size pi (pad pi pr).
Proof.
rewrite /PolR.size size_take size_set_nth ifT //.
exact: leq_maxl.
Qed.

Lemma pad_correct pi pr : pi >:: pr -> pi >:: pad pi pr.
Proof.
move=> Hp k.
rewrite /PolR.nth nth_take_dflt.
case: ifP => Hk.
rewrite Pol.nth_default //; exact: cont0.
rewrite nth_set_nth /= ifF; first exact: Hp.
by apply/negP => /eqP K; rewrite K leqnn in Hk.
Qed.

Lemma horner_pad pi pr x : pi >:: pr -> pr.[x] = (pad pi pr).[x].
Proof.
move=> Hp.
rewrite !(@PolR.hornerE_wide (maxn (Pol.size pi) (PolR.size pr))) -?size_pad;
  rewrite ?(leq_maxl, leq_maxr) //.
apply: eq_bigr => i _.
congr Rmult.
rewrite /pad /PolR.nth nth_take_dflt /PolR.nth nth_set_nth.
case: ifP => [Hi| /negbT Hi].
  by rewrite [LHS](Pol.nth_default_alt Hp).
rewrite -ltnNge in Hi; rewrite /= ifF //.
by apply/negbTE; rewrite neq_ltn Hi.
Qed.

Lemma TM_horner_correct (X0 X : I.type) Mf f pi pr n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  f Xnan = Xnan ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  pi >:: pr ->
  i_validTM (I.convert X0) (I.convert X) (TM_horner n pi Mf X0 X)
  (Xlift (fun x : R => pr.[(toR_fun f x)%Re])).
Proof.
move=> Hsubs0 /= Hne Hnan [Fdef Fnai Fzero Fsubs Fmain] Hp.
have Ht : not_empty (I.convert X0).
  case Hne => t Hts'.
  by exists t.
wlog Hsize : pi pr Hp / Pol.size pi = PolR.size pr => [Hwlog|].
  apply: (@TM_fun_eq (Xlift (fun x : R => (pad pi pr).[toR_fun f x]))).
  by move=> x Hx; rewrite /= [in RHS](@horner_pad pi).
  apply: Hwlog.
  exact: pad_correct.
  exact: size_pad.
elim/PolR.poly_ind: pr pi Hp Hsize => [|ar pr IHpr] pi Hp Hsize;
  elim/Pol.poly_ind: pi Hp Hsize =>[|ai pi _] Hp Hsize.
+ rewrite /TM_horner Pol.fold_polyNil.
  apply: (@TM_fun_eq (Xmask (Xreal 0))) =>//.
  apply: TM_cst_correct =>//.
  exact: cont0.
+ by rewrite sizes in Hsize.
+ by rewrite sizes in Hsize.
+ rewrite /= /TM_horner Pol.fold_polyCons.
  apply: (@TM_fun_eq (fun x : ExtendedR => Xmask (Xreal ar) x +
    Xlift (fun r : R => pr.[toR_fun f r]) x * Xlift (toR_fun f) x)%XR).
    move=> x Hx /=.
    congr Xreal; ring.
  apply: TM_add_correct.
  apply: TM_cst_correct=>//.
  by have := Hp 0; rewrite Pol.nth_polyCons PolR.nth_polyCons.
  apply: TM_mul_correct =>//.
  apply: IHpr.
  by move=> k; have := Hp k.+1; rewrite Pol.nth_polyCons PolR.nth_polyCons.
  by move: Hsize; rewrite !sizes; case.
Qed.

Definition TM_type := I.type -> I.type -> nat -> rpa.

Definition TMset0 (Mf : rpa) t :=
  RPA (Pol.set_nth (approx Mf) 0 t) (error Mf).

Definition TM_comp (TMg : TM_type) (Mf : rpa) X0 X n :=
  let Bf := Bnd.ComputeBound prec (approx Mf) (I.sub prec X X0) in
  let A0 := Pol.nth (approx Mf) 0 in
  let a0 := Imid A0 in
  let Mg := TMg a0 (I.add prec Bf (error Mf)) n in
  let M1 := TMset0 Mf (I.sub prec A0 a0) in
  let M0 := TM_horner n (approx Mg) M1 X0 X in
  RPA (approx M0) (I.add prec (error M0) (error Mg)).

Lemma TMset0_correct (X0 X c0 : I.type) Mf f :
  let: A0 := Pol.nth (approx Mf) 0 in
  forall a0 alpha0,
  not_empty (I.convert A0) ->
  a0 >: alpha0 ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  i_validTM (I.convert X0) (I.convert X) (TMset0 Mf (I.sub prec A0 a0))
  (fun x : ExtendedR => f x - Xreal alpha0).
Proof.
  move=> a0 alpha0 ne_A0 in_a0 Hf.
  rewrite /TMset0.
  have [Mfdef Mfnai Mfzero Mfsubs Mfmain] := Hf.
  split ; try easy.
  intros x Hx Hfx.
  apply (Mfdef x Hx).
  revert Hfx ; clear.
  by unfold defined ; case f.
  intros x1 Hx1.
  destruct (Mfmain x1 Hx1) as [Q H1 H2].
  exists (PolR.set_nth Q 0 (PolR.nth Q 0 - alpha0)%R).
  intros k.
  specialize (H1 k).
  clear - H1 ne_A0 in_a0.
  rewrite Pol.nth_set_nth PolR.nth_set_nth.
  destruct k as [|k] ; simpl.
  by apply (I.sub_correct _ _ _ _ (Xreal _) H1).
  exact H1.
  intros x Hx.
  specialize (H2 x Hx).
  move: (Mfdef x Hx).
  clear -H2.
  case: definedP.
  intros Hf _.
  replace (toR_fun (fun x2 => f x2 - Xreal alpha0) x) with (toR_fun f x - alpha0)%R.
  replace (PolR.set_nth Q 0 (PolR.nth Q 0 - alpha0)%R).[(x - x1)%R]
    with (Q.[(x - x1)%Re] - alpha0)%R.
  replace (toR_fun f x - alpha0 - (Q.[x - x1] - alpha0))%R
    with (toR_fun f x - Q.[x - x1])%R by ring.
  exact H2.
  destruct Q as [|q0 Q].
  by rewrite /= Rmult_0_l Rplus_0_l.
  by rewrite /= /Rminus Rplus_assoc.
  unfold toR_fun, proj_fun.
  destruct (f (Xreal x)).
  now elim Hf.
  easy.
  intros _.
  unfold eqNai.
  simpl.
  case I.convert.
  easy.
  intros l u H.
  now specialize (H (eq_refl true)).
Qed.

Lemma TM_comp_correct (X0 X : I.type) (TMg : TM_type) (Mf : rpa) g f :
  f Xnan = Xnan ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  (forall Y0 Y k, I.subset_ (I.convert Y0) (I.convert Y) ->
    not_empty (I.convert Y0) ->
    i_validTM (I.convert Y0) (I.convert Y) (TMg Y0 Y k) g) ->
  forall n,
  i_validTM (I.convert X0) (I.convert X)
  (TM_comp TMg Mf X0 X n) (fun xr => (g (f xr))).
Proof.
move=> Hnan Hne Hf Hg n; rewrite /TM_comp.
set A0 := Pol.nth (approx Mf) 0.
set a0 := Imid A0.
set Bf := Bnd.ComputeBound prec (approx Mf) (I.sub prec X X0).
set BfMf := I.add prec Bf (error Mf).
set Mg := TMg a0 (I.add prec Bf (error Mf)) n.
set M1 := TMset0 Mf (I.sub prec A0 a0).
set M0 := TM_horner n (approx Mg) M1 X0 X.

(* Preliminary facts *)
have [Fdef Fnai Fzero Hsubs Fmain] := Hf.
have ne_A0 : not_empty (I.convert A0).
  have [t Ht] := Hne.
  have [q hq1 hq2] := Fmain t Ht.
  by eexists; eapply hq1.
pose alpha0 := proj_val (I.convert_bound (I.midpoint A0)).
have in_a0 : a0 >: alpha0.
  exact: Xreal_Imid_contains.
have ne_a0 : not_empty (I.convert a0).
  by exists alpha0.
have subs_a0 : Interval_interval.subset (I.convert a0) (I.convert BfMf).
  rewrite /a0 /BfMf.
  apply: contains_subset.
  exact: not_empty'E.
  move=> [|v] Hv.
    apply/contains_Xnan; rewrite I.add_propagate_r //.
    rewrite /A0 in Hv.
    apply/contains_Xnan.
    by rewrite /Imid I.bnd_correct in Hv.
  rewrite /Bf.
  step_xr (Xadd (Xreal v) (Xreal 0)); last by rewrite Xadd_0_r.
  apply: I.add_correct =>//.
  rewrite /Bf.
  have [t Ht] := Hne.
  have [qf hq1 hq2] := Fmain t Ht.
  apply: (ComputeBound_nth0 qf) =>//.
  exact: (subset_sub_contains_0 _ Ht Hsubs).
  fold A0.
  eapply subset_contains =>//; by [exact: Imid_subset|].
have [Gdef Gnai Gzero Gsubs Gmain] := Hg a0 BfMf n subs_a0 ne_a0.
have inBfMf : forall x : R, X >: x -> contains (I.convert BfMf) (f (Xreal x)).
  move=> x Hx; rewrite /BfMf /Bf.
  have [t Ht] := Hne.
  have [qf hq1 hq2] := Fmain t Ht.
  move/(_ x Hx) in hq2.
  step_xr (Xreal (qf.[(x - t)%R]) + (f (Xreal x) - Xreal (qf.[(x - t)%R])))%XR =>//.
  apply: I.add_correct.
  apply: Bnd.ComputeBound_correct =>//.
  exact: R_sub_correct.
  case Ef: (eqNai (error Mf)).
    by move/eqNaiP: Ef->.
  have Df : defined f x. by apply: contraT => K; rewrite -Ef; apply: Fdef K.
  by rewrite -(Xreal_toR Df).
  case: (f) =>// r; simpl; congr Xreal; ring.
have HM1 : i_validTM (I.convert X0) (I.convert X) M1 (fun x => f x - Xreal (alpha0)).
  exact: TMset0_correct.

split=>//=.
(* Def *)
- move=> x Hx /definedPn Dx.
  apply/eqNaiP; rewrite I.add_propagate_r //.
  case Efx: (f (Xreal x)) => [|r].
    rewrite Gnai // /Bf.
    rewrite I.add_propagate_r //; apply/eqNaiP.
    move/(_ x): Fdef; apply =>//.
    exact/definedPn.
  rewrite Efx in Dx.
  apply/eqNaiP; apply: (@Gdef r); last by apply/definedPn.
  rewrite -Efx //.
  exact: inBfMf.

(* Nai *)
- move=> HX; rewrite I.add_propagate_r // Gnai //.
  by rewrite I.add_propagate_r // Fnai.

(* Zero *)
rewrite /M0 /Mg /Bf.
step_xr (Xreal 0 + Xreal 0)%XR; last by rewrite /= Rplus_0_l.
have [t Ht] := Hne.
have [a Ha] := ne_a0.
have [Q HQ1 HQ2] := Gmain a Ha.
have [F HF1 HF2] := Fmain t Ht.
apply: I.add_correct =>//.
have HH := @TM_horner_correct X0 X M1 _ (approx Mg) Q n Hsubs Hne _ HM1 HQ1.
rewrite Hnan /= in HH; move/(_ erefl) in HH.
by have [_ _ Hzero _ _] := HH.

(* Main *)
move=> x0 Hx0.
have HMg : i_validTM (I.convert a0) (I.convert BfMf) Mg g by exact: Hg.
(* now we need not [pose smallX0 := IIbnd (Xreal x0) (Xreal x0).] anymore... *)
have [M1def M1nai M1zero M1subs M1main] := HM1.
have [Ga0 HGa0 HGa0'] := Gmain alpha0 in_a0.
pose f0 := (fun x : ExtendedR => f x - Xreal alpha0).
have HM0 : i_validTM (I.convert X0) (I.convert X) M0 (Xlift (fun r => Ga0.[(toR_fun f0 r)%R])).
  rewrite /M0.
  apply: TM_horner_correct =>//.
  by rewrite /f0 Hnan.
have [M0def M0nai M0zero M0subs M0main] := HM0.
have [Q0 HQ0 HQ0'] := M0main x0 Hx0.
exists Q0 =>//.
move=> x Hx.
case Enai: (eqNai (I.add prec (error M0) (error Mg))).
  by move/eqNaiP: Enai ->.
rewrite Xreal_sub.
have DefOKgf : defined (fun xr : ExtendedR => g (f xr)) x.
  apply: contraT => /definedPn K.
  case Efx: (f (Xreal x)) => [|r]; last first.
    rewrite -Enai.
    apply/eqNaiP; rewrite I.add_propagate_r //; apply/eqNaiP.
    apply: (Gdef r); first by rewrite -Efx; apply: inBfMf.
    by apply/definedPn; rewrite -Efx K.
  rewrite -Enai.
  apply/eqNaiP; rewrite I.add_propagate_r //.
  apply/Gnai/contains_Xnan.
  rewrite -Efx; exact: inBfMf.
pose intermed := Xreal (toR_fun (Xlift (fun x1 : R => Ga0.[(toR_fun f0 x1)%R])) x).
step_xr ((intermed - Xreal Q0.[(x - x0)%R]) + (g (f (Xreal x)) - intermed))%XR;
  last by rewrite /intermed -(Xreal_toR DefOKgf) /=; congr Xreal; ring.
apply: I.add_correct; rewrite /intermed. exact: HQ0'.
case Efx: (f (Xreal x)) => [|r].
  step_xi IInan =>//.
  rewrite Gnai //.
  apply/contains_Xnan; rewrite -Efx; exact: inBfMf.
have DefOKg : defined g r.
  apply/definedP; move/definedP in DefOKgf.
  by rewrite Efx in DefOKgf.
have DefOKf : defined f x.
  apply/definedP; by rewrite Efx.
have DefOKf0 : defined f0 x.
  apply/definedP; move/definedP in DefOKf.
  by rewrite /f0; case: (f) DefOKf.
rewrite -(Xreal_toR DefOKg) -Xreal_sub toR_toXreal /Mg.
have->: toR_fun f0 x = (r - alpha0)%R.
  apply: Xreal_inj.
  rewrite (Xreal_toR DefOKf0) /f0 Efx.
  by simpl; congr Xreal; ring.
apply: HGa0'.
rewrite -Efx; exact: inBfMf.
Qed.

Definition TM_inv_comp Mf X0 X (n : nat) := TM_comp TM_inv Mf X0 X n.

Lemma TM_inv_comp_correct (X0 X : I.type) (TMf : rpa) f :
  f Xnan = Xnan ->
  not_empty (I.convert X0) ->
  forall n,
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X)
  (TM_inv_comp TMf X0 X n) (fun xr => Xinv (f xr)).
Proof.
move=> Hnan Ht n Hf.
apply: TM_comp_correct=> //.
have {Hf} [Hdef Hnai Hzero Hsubs Hmain] := Hf.
move=> Y0 Y k HY HY0.
exact: TM_inv_correct.
Qed.

Definition TM_div Mf Mg X0 X n :=
   TM_mul Mf (TM_inv_comp Mg X0 X n) X0 X n.

Lemma TM_div_correct (X0 X : I.type) (TMf TMg : rpa) f g n :
  g Xnan = Xnan->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X)
  (TM_div TMf TMg X0 X n) (fun xr => Xdiv (f xr) (g xr)).
Proof.
move=> Hnan Hne Hf Hg.
apply: (TM_fun_eq (f := fun xr => Xmul (f xr) (Xinv (g xr)))).
  by move=> x; rewrite Xdiv_split.
rewrite /TM_div.
apply: TM_mul_correct =>//.
exact: TM_inv_comp_correct.
Qed.

Lemma size_TM_comp (X0 X : I.type) (Tyg : TM_type) (TMf : rpa) (n : nat) :
  (forall Y0 Y k, 0 < Pol.size (approx (Tyg Y0 Y k))) ->
  Pol.size (approx (TM_comp Tyg TMf X0 X n)) = n.+1.
Proof. by move=> Hsize; rewrite size_TM_horner ifT // Hsize. Qed.

End PrecArgument.

End TaylorModel.


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

(* TODO: Coquelicot proof *)

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

(* TODO: midpoint *)

apply: I.atan_correct.
split =>//.

(* TODO: to see later *)

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
