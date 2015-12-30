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

Require Import ZArith Psatz reals_tac.
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
Require Import Rstruct Classical Coquelicot.
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

Module PolyMap (A : PowDivOps) (PolA : PolyOps A) (B : PowDivOps) (PolB : PolyOps B).

Definition polymap (f : A.T -> B.T) : PolA.T -> PolB.T :=
  @PolA.fold _ (fun x (*acc*) => PolB.polyCons (f x) (*acc*)) PolB.polyNil.

Lemma size_polymap (f : A.T -> B.T) (p : PolA.T) :
  PolB.size (polymap f p) = PolA.size p.
Proof.
elim/PolA.poly_ind: p; first rewrite /polymap.
  by rewrite PolA.size_polyNil PolA.fold_polyNil PolB.size_polyNil.
move=> a p IH; rewrite /polymap.
by rewrite PolA.fold_polyCons PolB.size_polyCons PolA.size_polyCons IH.
Qed.

Lemma nth_polymap (f : A.T -> B.T) (i : nat) (p : PolA.T) :
  i < PolA.size p -> PolB.nth (polymap f p) i = f (PolA.nth p i).
Proof.
elim/PolA.poly_ind: p i =>[|a p IH i H]; first by rewrite PolA.size_polyNil.
rewrite PolA.nth_polyCons.
rewrite /polymap PolA.fold_polyCons PolB.nth_polyCons; last first.
case: i IH H =>[//|i IH H]; rewrite IH //.
by rewrite PolA.size_polyCons ltnS in H.
Qed.

Definition polymap_polyCons (f : A.T -> B.T) a p :
  polymap f (PolA.polyCons a p) =
  PolB.polyCons (f a) (polymap f p).
Proof @PolA.fold_polyCons _ _ _ _ _.

Definition tpolymap_polyNil (f : A.T -> B.T) :
  polymap f PolA.polyNil = PolB.polyNil.
Proof @PolA.fold_polyNil _ _ _.

End PolyMap.

Module TaylorModel (I : IntervalOps) (Pol : PolyIntOps I) (Bnd : PolyBound I Pol).
Import Pol.Notations.
Import PolR.Notations.
Local Open Scope ipoly_scope.
Module Export Aux := IntervalAux I.
Module Import TI := TaylorPoly Pol.Int Pol.
Module TR := TaylorPoly FullR PolR.
(* TODO: the following 2 modules could be removed, using MonomPolyOps instead *)
Module MapI := PolyMap Pol.Int Pol Pol.Int Pol.
Module Import BndThm := PolyBoundThm I Pol Bnd.

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

(* Erik: Some lemmas could be generalized from [I.type] to [interval]. *)

(** Rigorous Polynomial Approximation structure *)
Record rpa : Type := RPA { approx : Pol.T; error : I.type }.

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

(** The following predicate, involved in [Ztech] below, will contribute to the
conciseness of the Coq goals, notably when issuing tactic [rewrite /Ztech]. *)
Definition isNNegOrNPos (X : I.type) : bool :=
  if I.sign_large X is Xund then false else true.

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
Definition TM_cst c (X0 X : I.type) (n : nat) : rpa :=
  RPA (T_cst c X0 n) (TLrem prec (T_cst c) X0 X n).

Definition TM_var X0 X (n : nat) :=
  RPA (T_var X0 n) (TLrem prec T_var X0 X n).

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
  (M : rpa) (xF : ExtendedR -> ExtendedR) :=
  let f := toR_fun xF in
  let dom := defined xF in
  [/\ contains (I.convert (error M)) (Xreal 0),
    I.subset_ X0 X &
    forall x0,
      contains X0 (Xreal x0) ->
      exists2 Q,
        approx M >:: Q
        & forall x, contains X (Xreal x) ->
                    contains (I.convert (error M))
                    (if dom x then
                       (Xreal (f x - (PolR.horner tt Q (x - x0))))%R
                     else Xnan)].

Lemma TM_fun_eq f g X0 X TMf :
  (forall x, contains X (Xreal x) -> f (Xreal x) = g (Xreal x)) ->
  i_validTM X0 X TMf f -> i_validTM X0 X TMf g.
Proof.
move=> Hfg [H0 H1 H2].
split=>// x0 Hx0.
have [Q HQ Hmain] := H2 x0 Hx0.
exists Q=>//.
move=> x Hx.
have Def := defined_ext (Hfg x Hx).
case G: (defined g x) (Hmain x Hx).
  have F : defined f x by rewrite Def.
  by rewrite F Xreal_sub Xreal_toR // Hfg // -[g _]Xreal_toR.
by rewrite Def G.
Qed.

(*
Lemma i_validTM_nan (v w : ExtendedR) (X0 X : interval) (tm : rpa)
  (f : ExtendedR -> ExtendedR) :
  i_validTM X0 X tm (fun x => if x is Xnan then v else f x) ->
  i_validTM X0 X tm (fun x => if x is Xnan then w else f x).
Proof.
move=> /= [Hzero Hsubset Hmain].
split=>//=.
move=> xi0 Hxi0.
move/(_ xi0 Hxi0) in Hmain.
have [a [Hsize Hcont Hdelta]] := Hmain.
exists a.
split=>//.
move=> x Hx.
move/(_ x Hx) in Hdelta.
case: x Hx Hdelta => [|r] Hx Hdelta //.
simpl in Hdelta |- *.
rewrite horner_in_nan in Hdelta.
rewrite Xsub_Xnan_r in Hdelta.
by move/contains_Xnan: Hdelta ->.
Qed.

Lemma i_validTM_mask (X0 X : interval) (tm : RPA.rpa)
  (f : ExtendedR -> ExtendedR) :
  i_validTM X0 X tm f -> i_validTM X0 X tm (fun x => Xmask (f x) x).
Proof.
move=> Hf.
apply: (i_validTM_nan (v := f Xnan) Xnan).
apply: TM_fun_eq Hf.
by case.
Qed.

Corollary TM_fun_eq_eta X0 X TMf f :
  i_validTM X0 X TMf
  (fun x => match x with Xnan => f Xnan | Xreal _ => f x end) ->
  i_validTM X0 X TMf f.
Proof. apply: TM_fun_eq; case; done. Qed.

Corollary TM_fun_eq_real f g X0 X TMf :
  (forall x : R, contains X (Xreal x) -> f (Xreal x) = g (Xreal x)) ->
  i_validTM X0 X TMf f -> i_validTM X0 X TMf g.
Proof.
move=> Hfg Hf.
apply: TM_fun_eq_eta.
eapply i_validTM_nan.
eapply TM_fun_eq; last exact Hf.
case; by [|exact Hfg].
Qed.
*)

Local Notation Ibnd2 x := (I.bnd x x) (only parsing).

(** * Some support lemmas about ExtendedR, I.bound_type, or I.type *)

Lemma le_upper_or (x y : ExtendedR) : le_upper x y \/ le_upper y x.
Proof.
case: x; case: y; [left|right|left|idtac]=>//.
by move=> r s; rewrite /le_lower /=; psatzl R.
Qed.

Lemma le_lower_or (x y : ExtendedR) : le_lower x y \/ le_lower y x.
Proof. by rewrite /le_lower; apply: le_upper_or. Qed.

Lemma Ilower_bnd (l u : I.bound_type) :
  I.convert_bound (I.lower (I.bnd l u)) = I.convert_bound l.
Proof. by rewrite I.lower_correct I.bnd_correct. Qed.

Lemma Iupper_bnd (l u : I.bound_type) :
  I.convert_bound (I.upper (I.bnd l u)) = I.convert_bound u.
Proof. by rewrite I.upper_correct I.bnd_correct. Qed.

Lemma Iupper_Xreal (X : I.type) (r : R) :
  I.convert_bound (I.upper X) = Xreal r -> I.convert X <> IInan.
Proof. by rewrite I.upper_correct; case: (I.convert X). Qed.

Lemma Ilower_Xreal (X : I.type) (r : R) :
  I.convert_bound (I.lower X) = Xreal r -> I.convert X <> IInan.
Proof. by rewrite I.lower_correct; case: (I.convert X). Qed.

Lemma upper_le (X : I.type) (x : ExtendedR (*sic*)) :
  contains (I.convert X) x -> le_upper x (I.convert_bound (I.upper X)).
Proof.
rewrite /le_upper; case E : I.convert_bound => [//|r] H.
have E' := Iupper_Xreal E.
case: x H => [|r'] H.
  by apply: E'; apply -> contains_Xnan.
case E2: (I.convert X) E' =>[//|l u] _.
rewrite E2 in H.
rewrite I.upper_correct E2 /= in E.
by move: H; rewrite /contains; case=> _; rewrite E.
Qed.

Lemma lower_le (X : I.type) (x : ExtendedR (*sic*)) :
  contains (I.convert X) x -> le_lower (I.convert_bound (I.lower X)) x.
Proof.
rewrite /le_lower; case E : I.convert_bound => [//|r] H.
have E' := Ilower_Xreal E.
case: x H => [|r'] H.
  by apply: E'; apply -> contains_Xnan.
case E2: (I.convert X) E' =>[//|l u] _.
rewrite E2 in H.
rewrite I.lower_correct E2 /= in E.
move: H; rewrite /contains; case=> H _; rewrite E in H.
by simpl; psatzl R.
Qed.

Lemma contains_lower_le_upper (X : interval) x :
  contains X x ->
  match (Xlower X), (Xupper X) with
  | Xreal r, Xreal s => (r <= s)%Re
  | _, _ => True
  end.
Proof.
case: X =>[//|l u]; case: l=>[//|l]; case: u=>[//|u] /=.
by case: x; intuition psatzl R.
Qed.

Lemma contains_IIbnd_Xreal (a b x : ExtendedR) :
  contains (IIbnd a b) x ->
  x = Xreal (proj_val x).
Proof. by case: x. Qed.

Lemma contains_lower_or_upper_Xreal (X : I.type) (xi0 : ExtendedR) (r : R) :
  contains (I.convert X) (Xreal r) -> contains (I.convert X) xi0 ->
  contains (IIbnd (I.convert_bound (I.lower X)) xi0) (Xreal r) \/
  contains (IIbnd xi0 (I.convert_bound (I.upper X))) (Xreal r).
Proof.
set x := Xreal r => Hx Hxi0.
have HL0 := lower_le Hx.
have HU0 := upper_le Hx.
have [HL|HL] := le_lower_or x xi0; have [HU|HU] := le_upper_or x xi0.
- by left; apply: le_contains.
- rewrite /le_lower in HL.
  rewrite /le_upper /= in HU HL.
  case E : xi0 Hxi0 HU HL =>[//|s /=].
  move=> Hs rs1 rs2.
  case L: (I.convert_bound (I.lower X)) => [|l];
    case U: (I.convert_bound (I.upper X)) => [|u];
    have H := contains_lower_le_upper Hx;
    intuition.
  by rewrite -I.lower_correct -I.upper_correct L U in H; psatzl R.
- by left; apply: le_contains.
by right; apply: le_contains.
Qed.

Lemma contains_lower_or_upper (X : I.type) (xi0 : ExtendedR) (x : ExtendedR) :
  I.convert X <> IInan ->
  contains (I.convert X) x -> contains (I.convert X) xi0 ->
  contains (IIbnd (I.convert_bound (I.lower X)) xi0) x \/
  contains (IIbnd xi0 (I.convert_bound (I.upper X))) x.
Proof.
move=> HX Hx Hxi0.
case: x Hx; first by move/contains_Xnan.
move=> r Hr; exact: contains_lower_or_upper_Xreal.
Qed.

(** * Material about I.midpoint and not_empty *)

Definition Imid i : I.type := I.bnd (I.midpoint i) (I.midpoint i).

Definition not_empty' (xi : interval) := exists v : ExtendedR, contains xi v.

Lemma not_emptyE xi : not_empty' xi -> not_empty xi.
Proof.
case: xi =>[|l u] [v Hv]; first by exists R0.
case: v Hv =>[//|r] Hr.
by exists r.
Qed.

Lemma not_empty'E xi : not_empty xi -> not_empty' xi.
case=>[r Hr]; by exists (Xreal r).
Qed.

Lemma contains_Xreal (xi : interval) (x : ExtendedR) :
  contains xi x -> contains xi (Xreal (proj_val x)).
Proof. by case: x =>//; case: xi. Qed.

Lemma not_empty_Imid (X : I.type) :
  not_empty (I.convert X) -> not_empty (I.convert (Imid X)).
Proof.
case=>[v Hv].
rewrite /Imid I.bnd_correct.
apply: not_emptyE.
exists (I.convert_bound (I.midpoint X)).
red.
have e : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> _] := I.midpoint_correct X e.
by auto with real.
Qed.

Lemma Imid_subset (X : I.type) :
  not_empty (I.convert X) ->
  I.subset_ (I.convert (Imid X)) (I.convert X).
Proof.
case=>[v Hv].
rewrite /Imid I.bnd_correct.
have HX : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> Hreal] := I.midpoint_correct X HX.
case E: I.convert =>[//|l u].
split.
- have := lower_le Hreal.
  have->: l = Xlower (I.convert X) by rewrite E.
  by rewrite I.lower_correct.
- have := upper_le Hreal.
  have->: u = Xupper (I.convert X) by rewrite E.
  by rewrite I.upper_correct.
Qed.

Lemma Imid_contains (X : I.type) :
  not_empty (I.convert X) ->
  contains (I.convert (Imid X)) (I.convert_bound (I.midpoint X)).
Proof.
move=>[v Hv].
rewrite /Imid I.bnd_correct.
have HX : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> Hreal] := I.midpoint_correct X HX.
by red; auto with real.
Qed.

(** Some auxiliary lemmas related to polynomials. *)

(*
Lemma is_horner_pos (p : PolR.T) (x : R) :
  0 < PolR.tsize p ->
  PolR.horner tt p x =
  \big[Rplus/0]_(i < PolR.tsize p)
    Rmult (PolR.tnth p i) (FullR.tpow tt x i).
Proof.
move=> Hy.
rewrite PolR.is_horner.
case: x => [| rx] //.
case cn : (PolR.tsize p) Hy => [|k]; first by rewrite ltn0.
by rewrite 2!big_ord_recl Xmul_comm.
Qed.

Lemma tpolyNil_size0 p :
  PolR.tsize p = 0 -> p = PolR.tpolyNil.
Proof.
by elim/PolR.tpoly_ind: p =>[//|p0 p IH]; rewrite PolR.tsize_polyCons.
Qed.

Lemma is_horner_mask (p : PolR.T) (x : FullXR.T) :
  PolR.horner tt p x =
  Xmask (\big[Xadd/Xreal 0]_(i < PolR.tsize p)
    Xmul (PolR.tnth p i) (FullXR.tpow tt x i)) x.
Proof.
case E : (PolR.tsize p) =>[|n].
  rewrite big_ord0.
  move/(tpolyNil_size0): E =>->.
  by rewrite PolR.horner_polyNil.
rewrite is_horner_pos ?{}E //.
elim: n => [|n IHn].
  rewrite !big_ord_recl !big_ord0.
  case: x => [|x] //=.
    by rewrite Xmul_comm.
by rewrite big_ord_recr {}IHn /=; case: x.
Qed.
*)

(** Another lemma that will be useful to prove the correctness of [TM_comp]. *)

Lemma i_validTM_subset_X0 (X0 : I.type) (SX0 : interval) (X : I.type) f Mf :
  I.subset_ SX0 (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) Mf f ->
  i_validTM (SX0) (I.convert X) Mf f.
Proof.
move=> Hsub [Hf0 Hf1 Hf2].
split=>//.
exact: (subset_subset _ (I.convert X0)).
move=> x0 Hx0.
have [|Q H1 H2] := Hf2 x0; first exact: (subset_contains SX0).
by exists Q.
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
  I.add prec (Imul (Isub X X0) (error Mf)) ((Iadd (Bnd.ComputeBound (*Pol.horner?*) prec R (Isub X0 X0)))
    (Imul (Isub X0 X0) (error Mf))).

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
PolR.size p = Pol.size (approx Mf) ->
(forall k : nat,
(k < Pol.size (approx Mf))%N ->
contains (I.convert (Pol.nth (approx Mf) k)) (Xreal (PolR.nth p k))) ->
forall k : nat,
(k < Pol.size TM_integral_poly)%N ->
contains (I.convert (Pol.nth TM_integral_poly k))
(Xreal (PolR.nth (PolR.primitive tt 0%R p) k)).
Proof.
move => Hsizep Hcontains k /=.
rewrite Pol.size_primitive (* addn1 *) => HkN.
rewrite Pol.primitive_correct // PolR.primitive_correct ?Hsizep //.
case: k HkN => [H0N | k HSkN].
+ by rewrite I.zero_correct; red; auto with real (* lemma to do *).
+ have -> : Xreal (PolR.nth p k / INR k.+1) =
           Xdiv (Xreal (PolR.nth p k)) (Xreal (INR k.+1)).
   rewrite /= zeroF; first by [].
   case: k HSkN.
     * by move => _; apply: R1_neq_R0.
     * move => n _.
        apply: tech_Rplus; first by exact: pos_INR.
        by exact: Rlt_0_1.
   apply: I.div_correct; first by apply: Hcontains.
by rewrite INR_IZR_INZ -Z2R_IZR (*!!! *); apply: I.fromZ_correct.
Qed.

Lemma TM_integral_error_0 (x0 : R):
  contains iX0 (Xreal x0) ->
  i_validTM (I.convert X0) iX Mf xF ->
  contains (I.convert (TM_integral_error TM_integral_poly)) (Xreal 0).
Proof.
move => Hx0X0 [] ErrMf0 HX0X HPol /=.
case: (HPol (x0) Hx0X0) => p Hcontains _.
have -> : Xreal 0 = Xadd (Xreal 0) (Xadd (Xreal 0) (Xreal 0)).
by rewrite /= 2!Rplus_0_l.
apply: I.add_correct; last apply: I.add_correct.
- apply: (@Aux.mul_0_contains_0_r _ (Xreal (x0 - x0))) => // .
have -> : Xreal (x0 - x0) = Xsub (Xreal x0) (Xreal x0) by [].
by apply: I.sub_correct => //; apply: (subset_contains (I.convert X0) _).
- apply (BndThm.ComputeBound_nth0 (PolR.primitive tt 0%R p)).
move=> k.
+ rewrite /TM_integral_poly Pol.primitive_correct //. (* I.zero_correct /= . *)
  admit. (* archi to revise *)
  admit. (* size *)
(** rewrite /TM_integral_poly Pol.size_primitive PolR.size_primitive.
by congr (_.+1); exact: Hsizep.*)
(* * by apply: contains_interval_float_integral. *)
* by apply: (IsubXX Hx0X0).
suff->: 0%R = PolR.nth (PolR.primitive tt 0%Re p) 0.
  apply: contains_interval_float_integral.
  admit. (* size *)
  by move=> k Hsize.
  admit. (* size *)
  by rewrite PolR.primitive_correct.
- apply: (@Aux.mul_0_contains_0_r _ (Xreal (x0 - x0))) => // .
have -> : Xreal (x0 - x0) = Xsub (Xreal x0) (Xreal x0) by [].
by apply: I.sub_correct.
Qed.

Definition TM_integral :=
let R := TM_integral_poly in RPA R (TM_integral_error TM_integral_poly).

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

Section MinMax. (* Lemmas which are missing but useful *)
Lemma Rmin_refl x1 : Rmin x1 x1 = x1. (* !!! *)
Proof.
rewrite /Rmin.
case: (Rle_dec x1 x1); lra.
Qed.

Lemma Rmax_refl x1 : Rmax x1 x1 = x1. (* !!! *)
Proof.
rewrite /Rmax.
case: (Rle_dec x1 x1); lra.
Qed.

Local Open Scope R_scope.

Lemma Rmin_leq x1 x2 : x1 <= x2 -> Rmin x1 x2 = x1.
Proof.
move => H12.
rewrite /Rmin.
case: (Rle_dec x1 x2); lra.
Qed.

Lemma Rmax_leq x1 x2 : x1 <= x2 -> Rmax x1 x2 = x2.
Proof.
move => H12.
rewrite /Rmax.
case: (Rle_dec x1 x2); lra.
Qed.

Lemma Rmin_lt x1 x2 : x1 < x2 -> Rmin x1 x2 = x1.
move => H12.
rewrite /Rmin.
case: (Rle_dec x1 x2); lra.
Qed.

Lemma Rmax_lt x1 x2 : x1 < x2 -> Rmax x1 x2 = x2.
Proof.
move => H12.
rewrite /Rmax.
case: (Rle_dec x1 x2); lra.
Qed.

Lemma Rmin_swap x1 x2 : Rmin x1 x2 = Rmin x2 x1.
Proof.
rewrite /Rmin.
case: (Rle_dec x1 x2); case: (Rle_dec x2 x1); lra.
Qed.

Lemma Rmax_swap x1 x2 : Rmax x1 x2 = Rmax x2 x1.
Proof.
rewrite /Rmax.
case: (Rle_dec x1 x2); case: (Rle_dec x2 x1); lra.
Qed.

End MinMax.

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

(* Definition Xint (f : ExtendedR -> ExtendedR) x0 x1 :=
  let f := toXreal_fun f in
  *)

Lemma TM_integral_correct (x0 : Rdefinitions.R) :
contains iX0 (Xreal x0) ->
i_validTM (I.convert X0) iX Mf xF ->
i_validTM (I.convert X0) iX TM_integral (toXreal_fun (RInt f x0)).
Proof.
move => Hx0X0 [] ErrMf0 HX0X HPol /=; split => //.
  by apply: (TM_integral_error_0 Hx0X0) => //.
move=> /= x1 HX0x1 {ErrMf0}.
case: (HPol (x0) Hx0X0) => p Hcontains H3.
case: (HPol (x1) HX0x1) => p1 Hcontains1 H31 {HPol}.
exists (PolR.primitive tt 0 p1).
(* split.
- by rewrite PolR.psize_primitive Hsizep1 /= psize_primitive. *)
- move=> k; apply: (contains_interval_float_integral).
  admit. (* size *)
  move=> k' _.
  apply: Hcontains1.
  admit. (* size *)
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
        have -> : t0 = 0; last by rewrite Rminus_0_r.
        (* rewrite /t0 PolR.horner_seq -nth0 PolR.pnth_toSeq.
         by rewrite PolR.primitive_correct. *) admit. (* OK with concrete PolR *)
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
  rewrite PolR.toSeq_horner0. rewrite -nth0 -PolR.nth_toSeq PolR.primitive_correct // Rminus_0_r.
  apply: Bnd.ComputeBound_correct; last by rewrite Xreal_sub; exact: I.sub_correct.
  (* + by rewrite psize_primitive PolR.psize_primitive Hsizep. *)
  + move => i. rewrite Pol.primitive_correct ?PolR.primitive_correct.
      * case: i; first by move => *; exact: cont0.
        move => n .
        rewrite Xreal_div; last first.
          case: n ; first by move => *; apply: R1_neq_R0.
          by move => n; apply: not_0_INR.
        apply: I.div_correct.
          by apply: Hcontains ; rewrite psize_primitive in Hn.
      * by rewrite INR_IZR_INZ -Z2R_IZR; apply: I.fromZ_correct.
      (* * by rewrite size_primitive -Hsizep in Hi. *)
      (* by rewrite psize_primitive in Hi. *)
        admit. admit. (* size *)
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
      move/(_ x2 hx2) in H3.
      by rewrite x_Def in H3.
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
      move/(_ x2 hx2) in H31.
      by rewrite x_Def in H31.
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

Section ProofOfRec.

Section GenericProof.
(** Generic proof for [TLrem]/[Ztech]. *)

Variable xf : ExtendedR -> ExtendedR.
Variable F : I.type -> I.type.
Variables X0 X : I.type.
Variable P : R -> nat -> PolR.T.
Variable IP : I.type -> nat -> Pol.T.

Let f0 := toR_fun xf.
Let def := defined xf.
Let dom r := contains (I.convert X) (Xreal r).
Let Dn n := Derive_n f0 n.

Hypothesis xf_Xnan : xf Xnan = Xnan.
Hypothesis F_contains : I.extension xf F.
Hypothesis Hdef : forall r, dom r -> def r.
Hypothesis Hder : forall n r, dom r -> ex_derive_n f0 n r.

Class validPoly : Prop := ValidPoly {
  Poly_size : forall (x0 : R) n, PolR.size (P x0 n) = n.+1;
  Poly_nth :
    forall (x0 : R) n k, k < n.+1 ->
    PolR.nth (P x0 n) k = Rdiv (Dn k x0) (INR (fact k)) }.

Class validIPoly : Prop := ValidIPoly {
  IPoly_size :
    forall (X0 : I.type) xi0 n, eq_size (IP X0 n) (P xi0 n);
  IPoly_nth : forall (X0 : I.type) xi0 n, X0 >: xi0 -> IP X0 n >:: P xi0 n;
  IPoly_nan : forall X, (exists2 x, X >: x & ~ def x) ->
              forall n, contains (I.convert (Pol.nth (IP X n.+1) n.+1)) Xnan
}.

Context { validPoly_ : validPoly }.
Context { validIPoly_ : validIPoly }.

Lemma Poly_nth0 x n : PolR.nth (P x n) 0 = f0 x.
Proof. by rewrite Poly_nth // Rcomplements.Rdiv_1. Qed.

Lemma Poly_size' n : Pol.size (IP X0 n) = n.+1.
Proof. by rewrite (IPoly_size X0 (*dummy*)0) Poly_size. Qed.

(*
Lemma not_and_impl : forall P Q : Prop, ~ (P /\ Q) -> P -> ~ Q.
Proof. now intuition. Qed.

(** Note that we define the following predicate using [exists] quantifiers, to
    be able to use [not_ex_all_not] later on, rather than [not_all_ex_not]. *)
Definition Xnan_ex (D : nat -> ExtendedR -> ExtendedR)
  (n : nat) (X : interval) : Prop :=
  exists k : 'I_n.+1,
(* FIXME: Use exists2 *)
  exists x : R, contains X (Xreal x) /\ D k (Xreal x) = Xnan.

Lemma Xnan_ex_or D n X : Xnan_ex D n X \/ ~ Xnan_ex D n X.
Proof. by apply: classic. Qed.

Lemma Xnan_ex_not D n X : ~ Xnan_ex D n X ->
  forall k : nat, forall x : R, k <= n ->
  contains X (Xreal x) ->
  D k (Xreal x) = Xreal (proj_val (D k (Xreal x))).
Proof.
move=> Hnot k x Hk Hx; have H'k : k < n.+1 by rewrite ltnS.
move:(not_ex_all_not _ _ Hnot).
move/(_ (Ordinal H'k)) => Hnot'.
move: (not_ex_all_not _ _ Hnot').
move/(_ x)=> Hnot''.
move: (not_and_impl Hnot'' Hx).
by case: (D k (Xreal x)).
Qed.

(* exists x, i, XDn i x = Xnan ~~> have Hn1 := XDn_Xnan (n.+1-i) Hi *)
*)

Theorem i_validTM_TLrem n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (IP X0 n) (TLrem prec IP X0 X n)) xf.
Proof.
move=> Hsub [t Ht].
pose err := TLrem prec IP X0 X n.
(* have XDn_0_Xnan : Dn 0 Xnan = Xnan by rewrite XDn_0. *)
split=>//=.
  (* |- 0 \in err *)
  set V := (I.power_int prec (I.sub prec X X0) (Z_of_nat n.+1)).
  apply (mul_0_contains_0_r _ (y := Xreal (PolR.nth (P t n.+1) n.+1))).
    apply: IPoly_nth =>//.
    exact: subset_contains (I.convert X0) _ _ _ _ =>//.
  apply: pow_contains_0 =>//.
  exact: subset_sub_contains_0 Ht _.
(* |- Main condition for i_validTM *)
move=> xi0 Hxi0; exists (P xi0 n); first by apply: IPoly_nth.
move=> x Hx.
case Def: defined.
rewrite PolR.hornerE Poly_size //.
have Hbig :
  \big[Rplus/R0]_(0 <= i < n.+1) (PolR.nth (P xi0 n) i * (x - xi0) ^ i)%R =
  \big[Rplus/R0]_(0 <= i < n.+1) (Dn i xi0 / INR (fact i) * (x - xi0)^i)%R.
apply: eq_big_nat => i Hi; rewrite Poly_nth //.
rewrite Hbig.
  (* forall i <= n.+1, XDn i x <> Xnan *)
  have H1 : contains (I.convert X) (Xreal xi0).
    exact: (subset_contains (I.convert X0)).
  have [c [Hcin [Hc Hc']]] := (@ITaylor_Lagrange xf (I.convert X) n Hder xi0 x H1 Hx).
  rewrite Hc {Hc t Ht} /TLrem.
  apply: R_mul_correct.
    rewrite -(@Poly_nth _ c n.+1 n.+1); last done.
    by apply: IPoly_nth.
  rewrite pow_powerRZ.
  apply: R_power_int_correct.
  exact: R_sub_correct.
(* ~ def x *)
rewrite /TLrem.
rewrite I.mul_propagate_l //.
apply/contains_Xnan/IPoly_nan.
exists x =>//.
by rewrite /def Def.
Qed.

Lemma isNNegOrNPos_false :
  I.convert X = IInan -> isNNegOrNPos X = false.
Proof.
move=> H; rewrite /isNNegOrNPos; have := I.sign_large_correct X.
by case: I.sign_large =>//; rewrite H; move/(_ Xnan I) =>//; case.
Qed.

Lemma bounded_singleton_contains_lower_upper :
  I.bounded X = true ->
  contains (I.convert (Ibnd2 (I.lower X))) (I.convert_bound (I.lower X)) /\
  contains (I.convert (Ibnd2 (I.upper X))) (I.convert_bound (I.upper X)).
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [H1a H1b] := I.lower_bounded_correct X H1.
have [H2a H2b] := I.upper_bounded_correct X H2.
by rewrite !I.bnd_correct /contains H1a H2a; psatzl R.
Qed.

Lemma bounded_IInan :
  I.bounded X = true -> I.convert X <> IInan.
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [] := I.lower_bounded_correct X H1.
by rewrite /I.bounded_prop; case I.convert.
Qed.

Lemma bounded_IIbnd :
  I.bounded X = true -> I.convert X =
  IIbnd (I.convert_bound (I.lower X)) (I.convert_bound (I.upper X)).
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [] := I.lower_bounded_correct X H1.
by rewrite /I.bounded_prop; case I.convert.
Qed.

Lemma bounded_Ilower :
  I.bounded X = true -> I.convert_bound (I.lower X) =
  Xreal (proj_val (I.convert_bound (I.lower X))).
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [] := I.lower_bounded_correct X H1.
by rewrite /I.bounded_prop; case I.convert.
Qed.

Lemma bounded_Iupper :
  I.bounded X = true -> I.convert_bound (I.upper X) =
  Xreal (proj_val (I.convert_bound (I.upper X))).
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [] := I.upper_bounded_correct X H2.
by rewrite /I.bounded_prop; case I.convert.
Qed.

(* TODO: Weaken the hyp in lemmas below *)
Lemma bounded_lower_Xnan :
  I.bounded X = true -> I.convert_bound (I.lower X) <> Xnan.
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
by have [-> _] := I.lower_bounded_correct X H1.
Qed.

Lemma bounded_upper_Xnan :
  I.bounded X = true -> I.convert_bound (I.upper X) <> Xnan.
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
by have [-> _] := I.upper_bounded_correct X H2.
Qed.

Lemma bounded_contains_lower (x : ExtendedR) :
  I.bounded X = true -> contains (I.convert X) x ->
  contains (I.convert X) (I.convert_bound (I.lower X)).
Proof.
move=> HX Hx.
have [H1 H2] := I.bounded_correct X HX.
have [H3 H4] := I.lower_bounded_correct X H1.
move: H4 Hx; rewrite /I.bounded_prop =>->.
rewrite /contains H3.
by case Er : x =>[//|r]; case Es: (I.convert_bound (I.upper X))=>[|s]; psatzl R.
Qed.

(* Erik: May also prove lower/upper-related lemmas involving subset *)

Lemma bounded_contains_upper (x : ExtendedR) :
  I.bounded X = true -> contains (I.convert X) x ->
  contains (I.convert X) (I.convert_bound (I.upper X)).
Proof.
move=> HX Hx.
have [H1 H2] := I.bounded_correct X HX.
have [H3 H4] := I.upper_bounded_correct X H2.
move: H4 Hx; rewrite /I.bounded_prop =>->.
rewrite /contains H3.
by case Er : x =>[//|r]; case Es : (I.convert_bound (I.lower X)) =>[|s]; psatzl R.
Qed.

(* Check (contains_subset, subset_contains). *)

Lemma contains_Xgt (a b : ExtendedR) :
  not_empty (IIbnd a b) ->
  Xcmp a b <> Xgt.
Proof.
move=> [x Hx].
case E : (Xcmp a b) =>//.
move=> _.
rewrite /contains in Hx.
case: a b E Hx => [//|ra [//|rb /=]].
by case: Rcompare_spec =>//; psatzl R.
Qed.

Lemma Xund_imp (a b : ExtendedR) :
  Xcmp a b = Xund -> a = Xnan \/ b = Xnan.
Proof.
case: a =>[|a]; first by left.
case: b =>[|b]; first by right.
by rewrite /=; case: Rcompare_spec.
Qed.

Lemma Xund_contra (a b : ExtendedR) :
  a <> Xnan -> b <> Xnan -> Xcmp a b <> Xund.
Proof.
move=> Ha Hb K.
by case: (Xund_imp K).
Qed.

Lemma Xeq_imp (a b : ExtendedR) :
  Xcmp a b = Xeq -> a = b.
Proof.
rewrite /Xcmp.
case: a =>[|r]; case: b =>[|s] //.
by case: Rcompare_spec =>//->.
Qed.

Definition Xincr (f : ExtendedR -> ExtendedR) (a b : ExtendedR) :=
  forall x y : R,
  contains (IIbnd a b) (Xreal x) -> contains (IIbnd a b) (Xreal y) ->
  (x <= y -> forall vx (vy := vx), proj_fun vx f x <= proj_fun vy f y)%Re.

Definition Xdecr (f : ExtendedR -> ExtendedR) (a b : ExtendedR) :=
  forall x y : R,
  contains (IIbnd a b) (Xreal x) -> contains (IIbnd a b) (Xreal y) ->
  (x <= y -> forall vx (vy := vx), proj_fun vy f y <= proj_fun vx f x)%Re.

Definition Xmonot (f : ExtendedR -> ExtendedR) (a b : ExtendedR) :=
  Xincr f a b \/ Xdecr f a b.

Definition Xpos_over (g : ExtendedR -> ExtendedR) (a b : ExtendedR) :=
  forall x : R, contains (IIbnd a b) (Xreal x) ->
  forall v : R, (0 <= proj_fun v g x)%Re.

Definition Xneg_over (g : ExtendedR -> ExtendedR) (a b : ExtendedR) :=
  forall x : R, contains (IIbnd a b) (Xreal x) ->
  forall v : R, (proj_fun v g x <= 0)%Re.

Definition Xcst_sign (g : ExtendedR -> ExtendedR) (a b : ExtendedR) :=
  Xpos_over g a b \/ Xneg_over g a b.

(*
Lemma eq_Xcst_sign (f g : ExtendedR -> ExtendedR) (a b : ExtendedR) :
  f =1 g -> Xcst_sign g a b -> Xcst_sign f a b.
Proof.
move=> H; rewrite /Xcst_sign /Xpos_over /Xneg_over.
by case=> Hf; [left|right] => x Hx v; rewrite /proj_fun H; apply: Hf.
Qed.

Lemma eq'_Xcst_sign (f g : ExtendedR -> ExtendedR) (a b : ExtendedR) :
  (forall x, contains (IIbnd a b) x -> f x = g x) ->
  Xcst_sign g a b -> Xcst_sign f a b.
Proof.
move=> H; rewrite /Xcst_sign /Xpos_over /Xneg_over.
by case=> Hf; [left|right] => x Hx v; rewrite /proj_fun H //; apply: Hf.
Qed.

Definition Xderive_over (X : interval) (f f' : ExtendedR -> ExtendedR) :=
  Xderive_pt f Xnan (f' Xnan) /\
  forall x : ExtendedR, contains X x -> Xderive_pt f x (f' x).

Lemma Xderive_over_propagate
  (f f' : ExtendedR -> ExtendedR) (X : interval) (x : ExtendedR) :
  contains X x ->
  Xderive_over X f f' -> f x = Xnan -> f' x = Xnan.
Proof.
move=> Hcont.
rewrite /Xderive_over /Xderive_pt; case => Hnan Hmain.
case: x Hcont => [|r] Hcont.
  by move: Hnan; case: (f' Xnan).
move/(_ _ Hcont): Hmain.
case: (f' (Xreal r)) =>// Hmain.
by case: (f (Xreal r)).
Qed.

Lemma Xderive_over_propagate' (f f' : ExtendedR -> ExtendedR) (X : interval) :
  Xderive_over X f f' -> f' Xnan = Xnan.
Proof.
rewrite /Xderive_over /Xderive_pt; case => Hnan _.
by case: (f' Xnan) Hnan.
Qed.
*)

Lemma Xcmp_same (x : ExtendedR) :
  match Xcmp x x with
  | Xeq | Xund => True
  | _ => False
  end.
Proof.
case: x => [//|r /=]; case: (Rcompare_spec r) =>//; exact: Rlt_irrefl.
Qed.

(*
Lemma Xcmp_gt_imp_fun (f g : ExtendedR -> ExtendedR) (a b v : R) :
  (Xcmp (f(Xreal a)) (g(Xreal b)) = Xgt -> proj_fun v f a > proj_fun v g b)%Re.
Proof.
rewrite /Xcmp /proj_fun.
case: (f (Xreal a)) =>[|r]; case: (g (Xreal b)) =>[|s] //.
by case: Rcompare_spec.
Qed.

Lemma Xcmp_lt_imp_fun (f g : ExtendedR -> ExtendedR) (a b v : R) :
  (Xcmp (f(Xreal a)) (g(Xreal b)) = Xlt -> proj_fun v f a < proj_fun v g b)%Re.
Proof.
rewrite /Xcmp /proj_fun.
case: (f (Xreal a)) =>[|r]; case: (g (Xreal b)) =>[|s] //.
by case: Rcompare_spec.
Qed.
*)

Lemma proj_fun_id (v x : R) : proj_fun v (@id ExtendedR) x = x.
Proof. done. Qed.

(*
Definition Xreal_over (f' : ExtendedR -> ExtendedR) (a b : ExtendedR) : Prop :=
  forall x : R, contains (IIbnd a b) (Xreal x) ->
  f' (Xreal x) = Xreal (proj_val (f' (Xreal x))).

Definition Xreal_over' (f' : ExtendedR -> ExtendedR) (a b : ExtendedR) : Prop :=
  forall x : R, contains (IIbnd a b) (Xreal x) ->
  forall v : R, f' (Xreal x) = Xreal (proj_fun v f' x).

Lemma Xreal_over_imp (f' : ExtendedR -> ExtendedR) (a b : ExtendedR) :
  Xreal_over f' a b -> Xreal_over' f' a b.
Proof.
rewrite /Xreal_over /Xreal_over' => H x Hx.
rewrite /proj_fun.
by move/(_ _ Hx): H ->.
Qed.

Lemma Xderive_pos_imp_incr
  (f f' : ExtendedR -> ExtendedR) (X : interval) (a b : ExtendedR) :
  Xreal_over f' a b ->
  contains X a -> contains X b ->
  Xderive_over X f f' -> Xpos_over f' a b -> Xincr f a b.
Proof.
(* Erik: We could think about how to improve this statement (X vs. [a, b]) *)
move=> Hreal Ha Hb.
rewrite /Xpos_over /Xincr.
move=> [Hnan Hder] H0 x y Hx Hy Hxy; rewrite //=.
have H'x : contains X (Xreal x) by exact: (@contains_IIbnd a b (Xreal x) X).
have H'y : contains X (Xreal y) by exact: (@contains_IIbnd a b (Xreal y) X).
move=> v; eapply (derivable_pos_imp_increasing _ (proj_fun v f'));
  [exact (contains_connected (IIbnd a b))|..|now auto with real]=>//.
move=> r Hr.
rewrite [_ r]/= in Hr.
have H'r : contains X (Xreal r) by exact: (@contains_IIbnd a b (Xreal r) X).
move/(_ _ H'r) in Hder.
move/(_ _ Hr v) in H0.
split; last by auto with real.
move: Hder; rewrite /Xderive_pt.
case E' : (f' (Xreal r)) H0 => [//|r'].
  by rewrite Hreal in E'.
case: (f (Xreal r)) => [//|_].
by have->: r' = proj_fun v f' r by rewrite /proj_fun E'.
Qed.

Lemma Xderive_neg_imp_decr
  (f f' : ExtendedR -> ExtendedR) (X : interval) (a b : ExtendedR) :
  Xreal_over f' a b ->
  contains X a -> contains X b ->
  Xderive_over X f f' -> Xneg_over f' a b -> Xdecr f a b.
Proof.
move=> Hreal Ha Hb.
rewrite /Xpos_over /Xincr.
move=> [Hnan Hder] H0 x y Hx Hy Hxy; rewrite //=.
have H'x : contains X (Xreal x) by exact: (@contains_IIbnd a b (Xreal x) X).
have H'y : contains X (Xreal y) by exact: (@contains_IIbnd a b (Xreal y) X).
move=> v; eapply (derivable_neg_imp_decreasing _ (proj_fun v f'));
  [exact (contains_connected (IIbnd a b))|..|now auto with real]=>//.
move=> r; rewrite [_ r]/= => Hr.
have H'r : contains X (Xreal r) by exact: (@contains_IIbnd a b (Xreal r) X).
move/(_ _ H'r): Hder; move/(_ _ Hr v): H0=> H0 Hder.
split; last by auto with real.
move: Hder; rewrite /Xderive_pt.
case E' : (f' (Xreal r)) H0 => [|r']; first by rewrite Hreal in E'.
case: (f (Xreal r)) => [//|_].
by have->: r' = proj_fun v f' r by rewrite /proj_fun E'.
Qed.

Lemma Xderive_cst_sign
  (f f' : ExtendedR -> ExtendedR) (X : interval) (a b : ExtendedR) :
  Xreal_over f' a b ->
  contains X a -> contains X b ->
  Xderive_over X f f' -> Xcst_sign f' a b -> Xmonot f a b.
Proof.
move=> Hreal Ha Hb Hder [H|H].
left; exact: (@Xderive_pos_imp_incr _ f' X).
right; exact: (@Xderive_neg_imp_decr _ f' X).
Qed.
*)

Definition delta (n : nat) (xi0 x : R) :=
  (f0 x - PolR.horner tt (P xi0 n) (x - xi0))%R.
(* TODO: Notations for PolR.horner, etc., would be convenient *)

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

(** Now let's define the derivative of (Xdelta n xi0) *)
Definition delta'_big (n : nat) (xi0 x : R) :=
  (Dn 1 x - \big[Rplus/R0]_(i < n) (PolR.nth (P xi0 n) i.+1 *
  (INR i.+1) * (x - xi0) ^ i))%R.

(*
Lemma Xderive_pt_sub' f g f' g' x :
  Xderive_pt f x f' ->
  (f x - g x <> Xnan \/ f' - g' <> Xnan -> Xderive_pt g x g')%XR ->
  Xderive_pt (fun x => Xsub (f x) (g x)) x (Xsub f' g').
Proof.
case E : (f x - g x)%XR =>[|r]; case E' : (f' - g')%XR =>[|r'] Hf Hg //.
- by case: x {E Hf Hg}.
- rewrite -E'.
  by apply: Xderive_pt_sub Hf (Hg _); right.
- rewrite -E'.
  by apply: Xderive_pt_sub Hf (Hg _); left.
rewrite -E'.
by apply: Xderive_pt_sub Hf (Hg _); left.
Qed.

Lemma Xderive_pt_sub_r f g f' g' x :
  Xderive_pt f x f' ->
  (g x <> Xnan \/ g' <> Xnan -> Xderive_pt g x g') ->
  Xderive_pt (fun x => Xsub (f x) (g x)) x (Xsub f' g').
Proof.
move=> Hf Hg.
case E : (g x) =>[|r]; case E' : g' =>[|r'].
- by rewrite !Xsub_Xnan_r; case: x {E Hf Hg}.
- by rewrite -E'; apply: Xderive_pt_sub Hf (Hg _); right; rewrite E'.
- by rewrite !Xsub_Xnan_r; case: x {E Hf Hg}.
by rewrite -E'; apply: Xderive_pt_sub Hf (Hg _); left; rewrite E.
Qed.

Lemma Xnan_ex_S D n X : Xnan_ex D n X -> Xnan_ex D n.+1 X.
Proof.
move=> [i [y [h1 h2]]].
by exists (widen_ord (leqnSn n.+1) i); exists y; split.
Qed.
*)

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

(*
Lemma bigXadd_nS (n : nat) (xi0 : ExtendedR) (r : R) :
  \big[Xadd/Xreal 0]_(i < n) (PolR.tnth (XP xi0 n.+1) i.+1 * (Xreal (INR i.+1) * Xreal r ^ i))%XR =
  \big[Xadd/Xreal 0]_(i < n) (PolR.tnth (XP xi0 n) i.+1 * (Xreal (INR i.+1) * Xreal r ^ i))%XR.
Proof.
apply: eq_bigr => i _; rewrite !XPoly_nth //; case: i =>//= *; exact: ltnW.
Qed.

Lemma bigXadd_ni (n : nat) (xi0 : ExtendedR) (r : R) :
  \big[Xadd/Xreal 0]_(i < n) (PolR.tnth (XP xi0 n.+1) i * Xreal r ^ i)%XR =
  \big[Xadd/Xreal 0]_(i < n) (PolR.tnth (XP xi0 n) i * Xreal r ^ i)%XR.
Proof.
apply: eq_bigr => i _; rewrite !XPoly_nth; case: i =>// *; apply: ltnW=>//.
exact: ltnW.
Qed.

Lemma bigXadd_Si (n : nat) (xi0 : ExtendedR) (r : R) :
  \big[Xadd/Xreal 0]_(i < n.+1) (PolR.tnth (XP xi0 n.+1) i * Xreal r ^ i)%XR =
  \big[Xadd/Xreal 0]_(i < n.+1) (PolR.tnth (XP xi0 n) i * Xreal r ^ i)%XR.
Proof.
apply: eq_bigr => i _; rewrite !XPoly_nth; case: i =>//= *; exact: ltnW.
Qed.

(* Check (not_Xnan_Xreal_fun, bigXadd_Xreal,bigXadd_Xreal1, bigXadd_Xreal_i). *)

Lemma bigXadd_XP (n : nat) (X : interval) (r s : R) (xi0 := Xreal r) :
  contains X xi0 ->
  \big[Xadd/Xreal 0]_(i < n.+1)
    (PolR.tnth (XP xi0 n) i * Xreal s ^ i)%XR =
  \big[Xadd/Xreal 0]_(i < n.+1)
    ((XDn i xi0) / Xreal (INR (fact i)) * Xreal s ^ i)%XR.
Proof.
move=> Hxi0.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 Hx Hy|i _]; first by rewrite Hx // Hy.
by rewrite XPoly_nth.
Qed.

Lemma bigXadd_real (n : nat) (X : interval) (r s : R) (xi0 := Xreal r) :
  contains X xi0 ->
  ~ Xnan_ex XDn n X ->
  \big[Xadd/Xreal 0]_(i < n.+1)
    ((XDn i xi0) / Xreal (INR (fact i)) * Xreal s ^ i)%XR =
  Xreal (\big[Rplus/R0]_(i < n.+1)
    (proj_val (XDn i xi0) / (INR (fact i)) * s ^ i)%Re).
Proof.
move=> Hxi0 Hnot.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 -> -> //|i _].
rewrite (@Xnan_ex_not XDn n X) =>//; last by case: i.
rewrite [Xdiv _ _]/= zeroF; last exact: INR_fact_neq_0.
by rewrite Xpow_idem Xpow_Xreal.
Qed.

Lemma bigXadd'_XP_S (n : nat) (X : interval) (r s : R) (xi0 := Xreal r) :
  contains X xi0 ->
  \big[Xadd/Xreal 0]_(i < n)
    (PolR.tnth (XP xi0 n) i.+1 * (Xreal (INR i.+1) * Xreal s ^ i))%XR =
  \big[Xadd/Xreal 0]_(i < n)
    ((XDn i.+1 xi0) / Xreal (INR (fact i.+1)) * (Xreal (INR i.+1) * Xreal s ^ i))%XR.
Proof.
move=> Hxi0.
case: n =>[|n]; first by rewrite !big_ord0.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 -> ->// |i _].
by rewrite XPoly_nth // ltnS; case: i.
Qed.

Lemma bigXadd'_real_S (n : nat) (X : interval) (r s : R) (xi0 := Xreal r) :
  contains X xi0 ->
  ~ Xnan_ex XDn n X ->
  \big[Xadd/Xreal 0]_(i < n)
    ((XDn i.+1 xi0) / Xreal (INR (fact i.+1)) * (Xreal (INR i.+1) *
     Xreal s ^ i))%XR =
  Xreal (\big[Rplus/R0]_(i < n)
    (proj_val (XDn i.+1 xi0) / (INR (fact i.+1)) * ((INR i.+1) * s ^ i)))%Re.
Proof.
move=> Hxi0 Hnot.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 -> -> //|i _].
rewrite (@Xnan_ex_not XDn n X) //.
rewrite Xpow_idem Xpow_Xreal /= zeroF // plusE multE.
have->: fact i + (i * fact i) = fact i.+1 by done.
exact: INR_fact_neq_0.
Qed.

Lemma bigXadd'_XP (n : nat) (X : interval) (r s : R) (xi0 := Xreal r) :
  contains X xi0 ->
  \big[Xadd/Xreal 0]_(i < n)
    (PolR.tnth (XP xi0 n) i.+1 * (Xreal (INR i.+1) * Xreal s ^ i))%XR =
  \big[Xadd/Xreal 0]_(i < n)
    ((XDn i.+1 xi0) / Xreal (INR (fact i)) * Xreal s ^ i)%XR.
Proof.
move=> Hxi0.
case: n =>[|n]; first by rewrite !big_ord0.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 -> ->//|i _].
rewrite XPoly_nth //; last by case: i.
rewrite -Xmul_assoc; congr Xmul.
rewrite fact_simpl mult_INR !Xdiv_split Xmul_assoc; congr Xmul.
have->: (Xreal (INR i.+1 * INR (fact i)) = Xreal (INR i.+1)
             * Xreal (INR (fact i)))%XR by done.
rewrite Xinv_Xmul_distr.
set xi := Xinv (Xreal (INR (fact i))).
rewrite Xmul_comm -Xmul_assoc -Xdiv_split.
set div := Xdiv _ _.
suff->: div = Xreal 1 by rewrite Xmul_1_l.
rewrite /div /= zeroF.
  congr Xreal; field.
  by rewrite -/(INR i.+1); change R0 with (INR 0); move/(INR_eq _).
by rewrite -/(INR i.+1); change R0 with (INR 0); move/(INR_eq _).
Qed.

Lemma bigXadd'_real (n : nat) (X : interval) (r s : R) (xi0 := Xreal r) :
  contains X xi0 ->
  ~ Xnan_ex XDn n X ->
  \big[Xadd/Xreal 0]_(i < n)
    ((XDn i.+1 xi0) / Xreal (INR (fact i)) * Xreal s ^ i)%XR =
  Xreal (\big[Rplus/R0]_(i < n)
    (proj_val (XDn i.+1 xi0) / INR (fact i) * s ^ i))%Re.
Proof.
move=> Hxi0 Hnot.
elim/big_ind2: _ =>[//|x1 x2 y1 y2 -> -> //|i _].
rewrite (@Xnan_ex_not XDn n X) // Xpow_idem Xpow_Xreal /= zeroF //.
exact: INR_fact_neq_0.
Qed.

Lemma Xderive_delta (n : nat) (xi0 : ExtendedR) (X : interval) :
  ~ Xnan_ex XDn n X ->
  contains X xi0 ->
  Xderive_over X (Xdelta n xi0) (Xdelta'_big n xi0).
Proof.
move=> Hnot Hxi0; split=>[|x Hx]; first by rewrite /Xdelta'_big /= Xsub_Xnan_r.
apply: Xderive_pt_eq_fun (Xdelta_idem' _ _) _ _.
apply: Xderive_pt_sub.
  have Heq : forall x : ExtendedR, XF0 x = XDn 0 x.
    by move: XDn_;rewrite /nth_Xderive /nth_Xderive_pt; case/(_ (*dummy*)Xnan).
  apply: Xderive_pt_eq_fun Heq _ _.
  by move: XDn_; rewrite /nth_Xderive /nth_Xderive_pt; case/(_ x).
case: x Hx =>[|r]; case: xi0 Hxi0 =>[|r0] // Hxi0 Hx.
have->: (Xreal r - Xreal r0 = Xreal (r - r0))%XR by done.
rewrite (bigXadd'_XP_S _(X:=X)) // (bigXadd'_real_S _(X:=X)) //.
red; rewrite (bigXadd_XP _(X:=X)) // (bigXadd_real _(X:=X)) //=.
move=> v.
elim: n Hnot =>[|n IHn] Hnot; have Hnot' := Xnan_ex_not Hnot.
  rewrite big_ord0 /=.
  apply: (derivable_pt_lim_eq (fun (_: R) => proj_val (XDn 0 (Xreal r0)))); last first.
     by apply: derivable_pt_lim_const.
  move=> x; rewrite /proj_fun.
  rewrite big_ord_recl big_ord0 Xadd_0_r XPoly_nth // (Hnot' 0 r0) //.
  rewrite /= zeroF /=; last exact: R1_neq_R0.
  by rewrite Rmult_1_r // /Rdiv Rinv_1 Rmult_1_r.
have HnotS : ~ Xnan_ex XDn n X by have := @Xnan_ex_S XDn n X; intuition.
move/(_ HnotS) in IHn.
rewrite big_ord_recr.
(* LR version without metavars. *)
apply: (derivable_pt_lim_eq
    (fun (x:R) =>
    (\big[Rplus/0]_(i < n.+1) (proj_val (XDn i (Xreal r0)) / INR (fact i) *
    (x - r0) ^ i) +
    proj_val (XDn n.+1 (Xreal r0)) /
    INR (fact n.+1)%coq_nat * ((x - r0) * (x - r0) ^ n))%Re)).
  move=> x; rewrite /proj_fun.
  rewrite [in RHS]big_ord_recr XPoly_nth // bigXadd_Si.
  rewrite (bigXadd_XP _(X:=X)) ?(bigXadd_real _(X:=X)) // (Hnot' n.+1 r0)//.
  rewrite !Xpow_idem !Xpow_Xreal /=.
  rewrite zeroF // plusE multE.
  have->: fact n + (n * fact n) = fact n.+1 by done.
  exact: INR_fact_neq_0.
apply: derivable_pt_lim_plus.
  move: IHn; apply: derivable_pt_lim_eq=> x.
  by rewrite /proj_fun (bigXadd_XP _(X:=X)) // (bigXadd_real _(X:=X)).
apply: derivable_pt_lim_scal.
have := (derivable_pt_lim_pow_sub r r0 n.+1); rewrite succnK.
exact: derivable_pt_lim_eq.
Qed.

Lemma Xdelta_real (n : nat) (X : interval) (r0 : R) (xi0 := Xreal r0) :
  contains X xi0 ->
  ~ Xnan_ex XDn n X ->
  forall a b : ExtendedR,
  contains X a -> contains X b ->
  Xreal_over (Xdelta n xi0) a b.
Proof.
move=> Hxi0 Hnot a b Ha Hb. hnf.
move=> x Hx.
rewrite Xdelta_idem /Xdelta_big -XDn_0.
have Hnot' := Xnan_ex_not Hnot.
have->: (Xreal x - xi0 = Xreal (x - r0))%XR by done.
rewrite (bigXadd_XP _(X:=X)) ?(bigXadd_real _(X:=X)) 1?Hnot' //.
exact: contains_trans Ha Hb _.
Qed.

Lemma Xdelta'_real (n : nat) (X : interval) (r0 : R) (xi0 := Xreal r0) :
  contains X xi0 ->
  ~ Xnan_ex XDn n.+1 X ->
  forall a b : ExtendedR,
  contains X a -> contains X b ->
  Xreal_over (Xdelta'_big n xi0) a b.
Proof.
move=> Hxi0 Hnot a b Ha Hb. hnf.
move=> x Hx; rewrite /Xdelta'_big.
have Hnot' := Xnan_ex_not Hnot.
have->: (Xreal x - xi0 = Xreal (x - r0))%XR by done.
rewrite (bigXadd'_XP _(X:=X)) // (bigXadd'_real _(X:=X)) //;
  last by move/(Xnan_ex_S).
rewrite Hnot' //.
exact: contains_trans Ha Hb _.
Qed.

Lemma notIInan_IIbnd (X : interval) :
  X <> IInan -> exists a : ExtendedR, exists b : ExtendedR, X = IIbnd a b.
Proof. by case: X =>[//|a b]; exists a; exists b. Qed.

Lemma Xmonot_contains
  (g : ExtendedR -> ExtendedR) (ra rb : R) (a := Xreal ra) (b := Xreal rb) :
  Xreal_over g a b ->
  Xmonot g a b ->
  forall (r s t : R) (x := Xreal r) (y := Xreal s) (z := Xreal t),
  contains (IIbnd a b) x -> contains (IIbnd a b) y ->
  contains (IIbnd x y) z ->
  contains (IIbnd (g x) (g y)) (g z) \/ contains (IIbnd (g y) (g x)) (g z).
Proof.
move=> Hreal.
have Hreal' := Xreal_over_imp Hreal.
move=> Hmonot rx ry rz x y z Hx Hy Hz.
have Habz : contains (IIbnd a b) z by exact: contains_trans Hx Hy Hz.
by case: Hmonot; rewrite /Xincr /Xdecr =>H; [left|right];
  rewrite (Hreal' rx _ R0) ?(Hreal' ry _ R0) ?(Hreal' rz _ R0)//;
   split; apply: H =>//; move: Hz; rewrite /contains /=; psatzl R.
Qed.

Corollary Xmonot_contains_weak (g : ExtendedR -> ExtendedR) (a b : ExtendedR) :
  Xreal_over g a b ->
  Xmonot g a b ->
  a <> Xnan -> b <> Xnan ->
  forall x : ExtendedR, contains (IIbnd a b) x ->
  contains (IIbnd (g a) (g b)) (g x) \/ contains (IIbnd (g b) (g a)) (g x).
Proof.
case: a =>[//|ra]; case: b =>[//|rb]=> Hreal Hmonot _ _.
case =>[//|rx Hx].
apply: (Xmonot_contains Hreal Hmonot) =>//.
  exact: contains_lower Hx.
exact: contains_upper Hx.
Qed.
*)

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

(*
Lemma upper_Xpos_over
  (X : I.type) (l := Xlower (I.convert X)) (u := Xupper (I.convert X))
  (c r0 : R) (xi0 := Xreal r0) (nm1 : nat) (n := nm1.+1) :
  I.bounded X = true ->
  contains (I.convert X) xi0 ->
  Xpos_over (XDn n.+1) l u ->
  forall x : R, contains (IIbnd xi0 u) (Xreal x) ->
  contains (IIbnd (Xreal x) xi0) (Xreal c) \/
    contains (IIbnd xi0 (Xreal x)) (Xreal c) ->
  (0 <= proj_val (XDn n.+1 (Xreal c)) / INR (fact n) * (x - r0) ^ n)%Re.
Proof.
move=> Hbnd Hxi0 Hsign x Hx [Hc|Hc]. (* REMARK: Hbnd may be unnecessary *)
  have ->: x = r0.
    by move: Hx Hc; rewrite /contains; case: {Hsign} u =>[|u]=> //=; psatzl R.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: (0 <= (x - r0))%Re.
  by move: Hx Hc; rewrite /contains; case: {Hsign} u =>[|u]=> //=; psatzl R.
have Hle_pow := pow_le _ n Hle.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : contains (I.convert X) l.
  rewrite /l -I.lower_correct.
  exact: bounded_contains_lower Hxi0.
have contains_u : contains (I.convert X) u.
  rewrite /u -I.upper_correct.
  exact: bounded_contains_upper Hxi0.
have contains_c : contains (IIbnd l u) (Xreal c).
  move: Hxi0 Hx Hc contains_l contains_u.
  rewrite /contains /= bounded_IIbnd //.
  rewrite I.upper_correct I.lower_correct -/l -/u.
  by case: {Hsign} u =>[|u]; case: l =>[|l]; psatzl R.
move/(_ c contains_c R0) in Hsign.
rewrite /proj_fun -/(proj_val _) in Hsign.
by apply: Rmult_le_pos_pos=>//; apply: Rdiv_pos_compat.
Qed.

Lemma upper_Xneg_over
  (X : I.type) (l := Xlower (I.convert X)) (u := Xupper (I.convert X))
  (c r0 : R) (xi0 := Xreal r0) (nm1 : nat) (n := nm1.+1) :
  I.bounded X = true ->
  contains (I.convert X) xi0 ->
  Xneg_over (XDn n.+1) l u ->
  forall x : R, contains (IIbnd xi0 u) (Xreal x) ->
  contains (IIbnd (Xreal x) xi0) (Xreal c) \/
    contains (IIbnd xi0 (Xreal x)) (Xreal c) ->
  (proj_val (XDn n.+1 (Xreal c)) / INR (fact n) * (x - r0) ^ n <= 0)%Re.
Proof.
move=> Hbnd Hxi0 Hsign x Hx [Hc|Hc]. (* REMARK: Hbnd may be unnecessary *)
  have ->: x = r0.
    by move: Hx Hc; rewrite /contains; case: {Hsign} u =>[|u]=> //=; psatzl R.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: (0 <= (x - r0))%Re.
  by move: Hx Hc; rewrite /contains; case: {Hsign} u =>[|u]=> //=; psatzl R.
have Hle_pow := pow_le _ n Hle.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : contains (I.convert X) l.
  rewrite /l -I.lower_correct.
  exact: bounded_contains_lower Hxi0.
have contains_u : contains (I.convert X) u.
  rewrite /u -I.upper_correct.
  exact: bounded_contains_upper Hxi0.
have contains_c : contains (IIbnd l u) (Xreal c).
  move: Hxi0 Hx Hc contains_l contains_u.
  rewrite /contains /= bounded_IIbnd //.
  rewrite I.upper_correct I.lower_correct -/l -/u.
  by case: {Hsign} u =>[|u]; case: l =>[|l]; psatzl R.
move:(Hsign c contains_c R0); rewrite /proj_fun -/(proj_val _)=> Hsignc.
by apply:Rmult_le_neg_pos=>//; apply:Rdiv_neg_compat.
Qed.
*)

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

(*
Lemma lower_even_Xpos_over
  (X : I.type) (l := Xlower (I.convert X)) (u := Xupper (I.convert X))
  (c r0 : R) (xi0 := Xreal r0) (nm1 : nat) (n := nm1.+1) :
  Z.Even (Z_of_nat n) ->
  I.bounded X = true ->
  contains (I.convert X) xi0 ->
  Xpos_over (XDn n.+1) l u ->
  forall x : R, contains (IIbnd l xi0) (Xreal x) ->
  contains (IIbnd (Xreal x) xi0) (Xreal c) \/
    contains (IIbnd xi0 (Xreal x)) (Xreal c) ->
  (0 <= proj_val (XDn n.+1 (Xreal c)) / INR (fact n) * (x - r0) ^ n)%Re.
Proof.
move=> Hev Hbnd Hxi0 Hsign x Hx [Hc|Hc]; last first.
  have ->: x = r0.
    by move: Hx Hc; rewrite /contains; case: {Hsign} l =>[|l]=> //=; psatzl R.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: ((x - r0) <= 0)%Re.
  by move: Hx Hc; rewrite /contains; case: {Hsign} l =>[|l]=> //=; psatzl R.
have Hle_pow := @ZEven_pow_le (x - r0)%Re n Hev.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : contains (I.convert X) l.
  rewrite /l -I.lower_correct.
  exact: bounded_contains_lower Hxi0.
have contains_u : contains (I.convert X) u.
  rewrite /u -I.upper_correct.
  exact: bounded_contains_upper Hxi0.
have contains_c : contains (IIbnd l u) (Xreal c).
  move: Hxi0 Hx Hc contains_l contains_u.
  rewrite /contains /= bounded_IIbnd // I.upper_correct I.lower_correct -/l -/u.
  by case: {Hsign} u =>[|u]; case: l =>[|l]; psatzl R.
move:{Hsign} (Hsign c contains_c R0); rewrite /proj_fun -/(proj_val _)=> Hsign.
by apply: Rmult_le_pos_pos=>//; apply: Rdiv_pos_compat.
Qed.

Lemma lower_even_Xneg_over
  (X : I.type) (l := Xlower (I.convert X)) (u := Xupper (I.convert X))
  (c r0 : R) (xi0 := Xreal r0) (nm1 : nat) (n := nm1.+1) :
  Z.Even (Z_of_nat n) ->
  I.bounded X = true ->
  contains (I.convert X) xi0 ->
  Xneg_over (XDn n.+1) l u ->
  forall x : R, contains (IIbnd l xi0) (Xreal x) ->
  contains (IIbnd (Xreal x) xi0) (Xreal c) \/
    contains (IIbnd xi0 (Xreal x)) (Xreal c) ->
  (proj_val (XDn n.+1 (Xreal c)) / INR (fact n) * (x - r0) ^ n <= 0)%Re.
Proof.
move=> Hev Hbnd Hxi0 Hsign x Hx [Hc|Hc]; last first.
  have ->: x = r0.
    by move: Hx Hc; rewrite /contains; case: {Hsign} l =>[|l]=> //=; psatzl R.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: ((x - r0) <= 0)%Re.
  by move: Hx Hc; rewrite /contains; case: {Hsign} l =>[|l]=> //=; psatzl R.
have Hle_pow := @ZEven_pow_le (x - r0)%Re n Hev.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : contains (I.convert X) l.
  rewrite /l -I.lower_correct.
  exact: bounded_contains_lower Hxi0.
have contains_u : contains (I.convert X) u.
  rewrite /u -I.upper_correct.
  exact: bounded_contains_upper Hxi0.
have contains_c : contains (IIbnd l u) (Xreal c).
  move: Hxi0 Hx Hc contains_l contains_u.
  rewrite /contains /= bounded_IIbnd //.
  rewrite I.upper_correct I.lower_correct -/l -/u.
  by case: {Hsign} u =>[|u]; case: l =>[|l]; psatzl R.
move/(_ c contains_c R0): Hsign; rewrite /proj_fun -/(proj_val _)=> Hsign.
by apply: Rmult_le_neg_pos=>//; apply: Rdiv_neg_compat.
Qed.

Lemma lower_odd_Xpos_over
  (X : I.type) (l := Xlower (I.convert X)) (u := Xupper (I.convert X))
  (c r0 : R) (xi0 := Xreal r0) (nm1 : nat) (n := nm1.+1) :
  Z.Odd (Z_of_nat n) ->
  I.bounded X = true ->
  contains (I.convert X) xi0 ->
  Xpos_over (XDn n.+1) l u ->
  forall x : R, contains (IIbnd l xi0) (Xreal x) ->
  contains (IIbnd (Xreal x) xi0) (Xreal c) \/
    contains (IIbnd xi0 (Xreal x)) (Xreal c) ->
  (proj_val (XDn n.+1 (Xreal c)) / INR (fact n) * (x - r0) ^ n <= 0)%Re.
Proof.
move=> Hev Hbnd Hxi0 Hsign x Hx [Hc|Hc]; last first.
  have -> : x = r0.
    by move: Hx Hc; rewrite /contains; case: {Hsign} l =>[|l]=> //=; psatzl R.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: ((x - r0) <= 0)%Re.
  by move: Hx Hc; rewrite /contains; case: {Hsign} l =>[|l]=> //=; psatzl R.
have Hle_pow := @ZOdd_pow_le (x - r0)%Re n Hev Hle.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : contains (I.convert X) l.
  rewrite /l -I.lower_correct.
  exact: bounded_contains_lower Hxi0.
have contains_u : contains (I.convert X) u.
  rewrite /u -I.upper_correct.
  exact: bounded_contains_upper Hxi0.
have contains_c : contains (IIbnd l u) (Xreal c).
  move: Hxi0 Hx Hc contains_l contains_u.
  rewrite /contains /= bounded_IIbnd //.
  rewrite I.upper_correct I.lower_correct -/l -/u.
  by case: {Hsign} u =>[|u]; case: l =>[|l]; psatzl R.
move/(_ c contains_c R0) in Hsign.
rewrite /proj_fun -/(proj_val _) in Hsign.
set r := (_ / _)%Re.
rewrite -(@Rmult_0_r r); apply: Rge_le; apply: Rmult_ge_compat_l.
  by apply: Rle_ge; apply: Rdiv_pos_compat.
by auto with real.
Qed.

Lemma lower_odd_Xneg_over
  (X : I.type) (l := Xlower (I.convert X)) (u := Xupper (I.convert X))
  (c r0 : R) (xi0 := Xreal r0) (nm1 : nat) (n := nm1.+1) :
  Z.Odd (Z_of_nat n) ->
  I.bounded X = true ->
  contains (I.convert X) xi0 ->
  Xneg_over (XDn n.+1) l u ->
  forall x : R, contains (IIbnd l xi0) (Xreal x) ->
  contains (IIbnd (Xreal x) xi0) (Xreal c) \/
    contains (IIbnd xi0 (Xreal x)) (Xreal c) ->
  (0 <= proj_val (XDn n.+1 (Xreal c)) / INR (fact n) * (x - r0) ^ n)%Re.
Proof.
move=> Hev Hbnd Hxi0 Hsign x Hx [Hc|Hc]; last first.
  have -> : x = r0.
    by move: Hx Hc; rewrite /contains; case: {Hsign} l =>[|l]=> //=; psatzl R.
  by rewrite Rminus_diag_eq // pow_ne_zero // Rmult_0_r; auto with real.
have Hle: ((x - r0) <= 0)%Re.
  by move: Hx Hc; rewrite /contains; case: {Hsign} l =>[|l]=> //=; psatzl R.
have Hle_pow := @ZOdd_pow_le (x - r0)%Re n Hev Hle.
have Hle_fact := INR_fact_lt_0 n.
have contains_l : contains (I.convert X) l.
  rewrite /l -I.lower_correct.
  exact: bounded_contains_lower Hxi0.
have contains_u : contains (I.convert X) u.
  rewrite /u -I.upper_correct.
  exact: bounded_contains_upper Hxi0.
have contains_c : contains (IIbnd l u) (Xreal c).
  move: Hxi0 Hx Hc contains_l contains_u.
  rewrite /contains /= bounded_IIbnd //.
  rewrite I.upper_correct I.lower_correct -/l -/u.
  by case: {Hsign} u =>[|u]; case: l =>[|l]; psatzl R.
move/(_ c contains_c R0) in Hsign.
rewrite /proj_fun -/(proj_val _) in Hsign.
set r := ((x - r0) ^ n)%Re.
rewrite -(@Rmult_0_l r); apply: Rmult_le_compat_neg_r.
  by auto with real.
exact: Rdiv_neg_compat.
Qed.
*)

Lemma Xsub_0_r (x : ExtendedR) : Xsub x (Xreal 0) = x.
Proof. by case: x =>//= r; rewrite Rminus_0_r. Qed.

Lemma Rdiv_1_r (x : R) : (x / 1 = x)%Re.
Proof. by rewrite /Rdiv Rinv_1 Rmult_1_r. Qed.

Lemma Xdiv_1_r (x : ExtendedR) : (x / Xreal 1 = x)%XR.
Proof.
by case: x; f_equal =>//= r; rewrite zeroF; discrR; rewrite Rdiv_1_r.
Qed.

(*
(** Proposition 2.2.1 in Mioara Joldes' thesis,
    adapted from Lemma 5.12 in Roland Zumkeller's thesis *)
Theorem Zumkeller_monot_rem (X : I.type) (r0 : R) (xi0 := Xreal r0) (n : nat)
  (l := I.convert_bound (I.lower X)) (u := I.convert_bound (I.upper X)) :
  I.bounded X = true ->
  contains (I.convert X) xi0 ->
  ~ Xnan_ex XDn n.+1 (I.convert X) ->
  Xcst_sign (XDn n.+1) l u ->
  Xmonot (Xdelta n xi0) l xi0 /\
  Xmonot (Xdelta n xi0) xi0 u.
Proof.
move=> Hbnd Hxi0 Hnot.
have Hnot' := Xnan_ex_not Hnot.
have XDn_1_Xnan : XDn 1 Xnan = Xnan by rewrite XDn_Xnan'.
have contains_l : contains (I.convert X) (I.convert_bound (I.lower X)).
  exact: bounded_contains_lower Hxi0.
have contains_u : contains (I.convert X) (I.convert_bound (I.upper X)).
  exact: bounded_contains_upper Hxi0.
case: n Hnot Hnot' =>[|nm1] Hnot Hnot'; last set n := nm1.+1.
  move=> Hsign; split; apply: (@Xderive_cst_sign _ (XDn 1) (I.convert X)) =>//.
  - move=> x Hx.
    rewrite (Hnot' 1 x) =>//.
    by apply: contains_trans Hx; [apply: bounded_contains_lower Hxi0|].
  - split; rewrite /= ?XDn_1_Xnan //.
    move=> x Hx.
    rewrite /Xdelta.
    have->: (XDn 1 x = XDn 1 x - Xmask (Xreal 0) x)%XR.
      case: (x) =>//=; by [rewrite XDn_Xnan'|move=>?; rewrite Xsub_0_r].
    apply: Xderive_pt_sub.
      case: (XDn_ x) =>_ /(_ 0).
      apply: Xderive_pt_eq_fun.
      by move=> y; rewrite XDn_0.
    have := (Xderive_pt_mulXmask (proj_val (PolR.tnth (XP xi0 0) 0)) x).
    apply: Xderive_pt_eq_fun.
    move=> y; rewrite is_horner_mask XPoly_size.
    case: y =>[//|r /=].
    rewrite (bigXadd_XP _(X:=I.convert X))// (bigXadd_real _(X:=I.convert X))//.
      rewrite XPoly_nth // big_ord_recl big_ord0; f_equal.
      by rewrite /= Rdiv_1_r !Rmult_1_r Rplus_0_r Xdiv_1_r.
    by move/(Xnan_ex_S).
  - case: Hsign => Hsign; [left|right]; move: Hsign; rewrite /Xpos_over /Xneg_over.
    + move=> Htop x Hx v; apply: Htop.
      move: Hxi0 Hx; rewrite /contains bounded_IIbnd //.
      rewrite /l /u {l u} !(I.lower_correct,I.upper_correct).
      by case: Xlower=> [|l]; case: Xupper =>[|u] //=; psatzl R.
    + move=> Htop x Hx v; apply: Htop.
      move: Hxi0 Hx; rewrite /contains bounded_IIbnd //.
      rewrite /l /u {l u} !(I.lower_correct,I.upper_correct).
      by case: Xlower=> [|l]; case: Xupper =>[|u] //=; psatzl R.
  - move=> x Hx.
    rewrite (Hnot' 1 x) =>//.
    by apply: contains_trans Hx; [|apply: bounded_contains_upper Hxi0].
  - split; rewrite /= ?XDn_1_Xnan //.
    move=> x Hx.
    rewrite /Xdelta.
    have->: (XDn 1 x = XDn 1 x - Xmask (Xreal 0) x)%XR.
      by case: (x) =>//=; [rewrite XDn_Xnan'|move=>?; rewrite Xsub_0_r].
    apply: Xderive_pt_sub.
      case: (XDn_ x) =>_ /(_ 0).
      apply: Xderive_pt_eq_fun.
      by move=> y; rewrite XDn_0.
    have := (Xderive_pt_mulXmask (proj_val (PolR.tnth (XP xi0 0) 0)) x).
    apply: Xderive_pt_eq_fun.
    move=> y; rewrite is_horner_mask XPoly_size.
    case: y =>[//|r /=].
    rewrite (bigXadd_XP _(X:=I.convert X))// (bigXadd_real _(X:=I.convert X))//.
      rewrite XPoly_nth // big_ord_recl big_ord0; f_equal.
      by rewrite /= Rdiv_1_r !Rmult_1_r Rplus_0_r Xdiv_1_r.
    by move/(Xnan_ex_S).
  case: Hsign => Hsign; [left|right]; move: Hsign; rewrite /Xpos_over /Xneg_over.
    move=> Htop x Hx v; apply: Htop.
    move: Hxi0 Hx; rewrite /contains bounded_IIbnd //.
    rewrite /l /u {l u} !(I.lower_correct,I.upper_correct).
    by case: Xlower=> [|l]; case: Xupper =>[|u] //=; psatzl R.
  move=> Htop x Hx v; apply: Htop.
  move: Hxi0 Hx; rewrite /contains bounded_IIbnd //.
  rewrite /l /u {l u} !(I.lower_correct,I.upper_correct).
  by case: Xlower=> [|l]; case: Xupper =>[|u] //=; psatzl R.
have Hreal := Xdelta_real _ Hnot.
have HnotSS : ~ Xnan_ex XDn n (I.convert X) by move/(Xnan_ex_S).
have Hlower : contains (I.convert X) (I.convert_bound (I.lower X))
  by exact: bounded_contains_lower @xi0 _ _.
have Hupper : contains (I.convert X) (I.convert_bound (I.upper X))
  by exact: bounded_contains_upper @xi0 _ _.
case=>[Hpos|Hneg].
  split.
    apply: Xderive_cst_sign (Xdelta'_big n xi0)(I.convert X) _ _ _ _ _ _ _ =>//.
    * exact: (Xdelta'_real _(X:=I.convert X)).
    * exact: Xderive_delta.
    { have [Heven|Hodd] := (Z.Even_or_Odd (Z_of_nat nm1.+1)).
      - left.
        move=> x Hx v.
        have H'x : contains (I.convert X) (Xreal x).
        apply: contains_trans Hx; by [apply: bounded_contains_lower Hxi0|].
        have TL := @XTaylor_Lagrange (fun n => XDn n.+1) (I.convert X) n.-1
          (fun n => @Xder XDn_ n.+1) _
           XDn_1_Xnan xi0 (Xreal x) Hxi0 H'x.
        have [|c [H1 [H2 H3]]] := TL.
          by move=> y k Hk Hy; rewrite Hnot' // ltnS; apply/leP.
        rewrite /Xdelta'_big /proj_fun.
        rewrite (bigXadd'_XP _(X:=I.convert X)) //.
        rewrite H2.
        rewrite (Hnot' n.+1 c) //.
        rewrite [Xsub _ _]/= Xpow_idem Xpow_Xreal /= zeroF /=; last first.
          by change (fact nm1 + _)%coq_nat with (fact nm1.+1);
            apply: INR_fact_neq_0.
        change (fact nm1 + _)%coq_nat with (fact n).
         change((x - r0) * _)%Re with ((x - r0) ^ n)%Re.
        apply: (@lower_even_Xpos_over X c r0 nm1 _ _ _ _ x) =>//.
          by rewrite /l /u I.lower_correct I.upper_correct in Hpos.
        by rewrite /l I.lower_correct in Hx.
      - right.
        move=> x Hx v.
        have H'x : contains (I.convert X) (Xreal x).
        apply: contains_trans Hx; by [apply: bounded_contains_lower Hxi0|].
        have TL := @XTaylor_Lagrange
          (fun n => XDn n.+1) (I.convert X) n.-1 (fun n => @Xder XDn_ n.+1) _
           XDn_1_Xnan xi0 (Xreal x) Hxi0 H'x.
        have [|c [H1 [H2 H3]]] := TL.
          by move=> y k Hk Hy; rewrite Hnot' // ltnS; apply/leP.
        rewrite /Xdelta'_big /proj_fun.
        rewrite (bigXadd'_XP _(X:=I.convert X)) //.
        rewrite H2.
        rewrite (Hnot' n.+1 c) //.
        rewrite [Xsub _ _]/= Xpow_idem Xpow_Xreal /= zeroF /=; last first.
          by change (fact nm1 + _)%coq_nat with (fact nm1.+1);
            apply: INR_fact_neq_0.
        change (fact nm1 + _)%coq_nat with (fact n).
         change((x - r0) * _)%Re with ((x - r0) ^ n)%Re.
        apply: (@lower_odd_Xpos_over X c r0 nm1 _ _ _ _ x) =>//.
          by rewrite /l /u I.lower_correct I.upper_correct in Hpos.
        by rewrite /l I.lower_correct in Hx.
      }
  apply: Xderive_cst_sign (Xdelta'_big n xi0)(I.convert X) _ _ _ _ _ _ _ =>//.
  * exact: (Xdelta'_real _(X:=I.convert X)).
  * exact: Xderive_delta.
  left.
  move=> x Hx v.
  have H'x : contains (I.convert X) (Xreal x).
    by apply: contains_trans Hx; by [apply: bounded_contains_lower Hxi0|].
  have TL := @XTaylor_Lagrange
        (fun n => XDn n.+1) (I.convert X) n.-1 (fun n => @Xder XDn_ n.+1) _
        XDn_1_Xnan xi0 (Xreal x) Hxi0 H'x.
  have [|c [H1 [H2 H3]]] := TL.
    by move=> y k Hk Hy; rewrite Hnot' // ltnS; apply/leP.
  rewrite /Xdelta'_big /proj_fun.
  rewrite (bigXadd'_XP _(X:=I.convert X)) //.
  rewrite H2.
  rewrite (Hnot' n.+1 c) //.
  rewrite [Xsub _ _]/= Xpow_idem Xpow_Xreal /= zeroF /=; last first.
    by change (fact nm1 + _)%coq_nat with (fact nm1.+1); apply: INR_fact_neq_0.
  change (fact nm1 + _)%coq_nat with (fact n).
  change((x - r0) * _)%Re with ((x - r0) ^ n)%Re.
  apply: (@upper_Xpos_over X c r0 nm1 _ _ _ x) =>//.
    by rewrite /l /u I.lower_correct I.upper_correct in Hpos.
  by rewrite /u I.upper_correct in Hx.
split.
  apply: Xderive_cst_sign (Xdelta'_big n xi0)(I.convert X) _ _ _ _ _ _ _ =>//.
  * exact: (Xdelta'_real _(X:=I.convert X)).
  * exact: Xderive_delta.
  { have [Heven|Hodd] := (Z.Even_or_Odd (Z_of_nat nm1.+1)).
      - right.
        move=> x Hx v.
        have H'x : contains (I.convert X) (Xreal x).
        apply: contains_trans Hx; by [apply: bounded_contains_lower Hxi0|].
        have TL := @XTaylor_Lagrange
          (fun n => XDn n.+1) (I.convert X) n.-1 (fun n => @Xder XDn_ n.+1) _
           XDn_1_Xnan xi0 (Xreal x) Hxi0 H'x.
        have [|c [H1 [H2 H3]]] := TL.
          by move=> y k Hk Hy; rewrite Hnot' // ltnS; apply/leP.
        rewrite /Xdelta'_big /proj_fun.
        rewrite (bigXadd'_XP _(X:=I.convert X)) //.
        rewrite H2.
        rewrite (Hnot' n.+1 c) //.
        rewrite [Xsub _ _]/= Xpow_idem Xpow_Xreal /= zeroF /=; last first.
          by change (fact nm1 + _)%coq_nat with (fact nm1.+1);
            apply: INR_fact_neq_0.
        change (fact nm1 + _)%coq_nat with (fact n).
         change((x - r0) * _)%Re with ((x - r0) ^ n)%Re.
        apply: (@lower_even_Xneg_over X c r0 nm1 _ _ _ _ x) =>//.
          by rewrite /l /u I.lower_correct I.upper_correct in Hneg.
        by rewrite /l I.lower_correct in Hx.
      - left.
        move=> x Hx v.
        have H'x : contains (I.convert X) (Xreal x).
        apply: contains_trans Hx; by [apply: bounded_contains_lower Hxi0|].
        have TL := @XTaylor_Lagrange
          (fun n => XDn n.+1) (I.convert X) n.-1 (fun n => @Xder XDn_ n.+1) _
           XDn_1_Xnan xi0 (Xreal x) Hxi0 H'x.
        have [|c [H1 [H2 H3]]] := TL.
          by move=> y k Hk Hy; rewrite Hnot' // ltnS; apply/leP.
        rewrite /Xdelta'_big /proj_fun.
        rewrite (bigXadd'_XP _(X:=I.convert X)) //.
        rewrite H2.
        rewrite (Hnot' n.+1 c) //.
        rewrite [Xsub _ _]/= Xpow_idem Xpow_Xreal /= zeroF /=; last first.
          by change (fact nm1 + _)%coq_nat with (fact nm1.+1);
            apply: INR_fact_neq_0.
        change (fact nm1 + _)%coq_nat with (fact n).
         change((x - r0) * _)%Re with ((x - r0) ^ n)%Re.
        apply: (@lower_odd_Xneg_over X c r0 nm1 _ _ _ _ x) =>//.
          by rewrite /l /u I.lower_correct I.upper_correct in Hneg.
        by rewrite /l I.lower_correct in Hx.
      }
apply: Xderive_cst_sign (Xdelta'_big n xi0)(I.convert X) _ _ _ _ _ _ _ =>//.
* exact: (Xdelta'_real _(X:=I.convert X)).
* exact: Xderive_delta.
right.
move=> x Hx v.
have H'x : contains (I.convert X) (Xreal x).
  by apply: contains_trans Hx=> //; apply: bounded_contains_lower Hxi0.
have TL := @XTaylor_Lagrange
        (fun n => XDn n.+1) (I.convert X) n.-1 (fun n => @Xder XDn_ n.+1) _
        XDn_1_Xnan xi0 (Xreal x) Hxi0 H'x.
have [|c [H1 [H2 H3]]] := TL.
  by move=> y k Hk Hy; rewrite Hnot' // ltnS; apply/leP.
rewrite /Xdelta'_big /proj_fun (bigXadd'_XP _(X:=I.convert X)) //.
rewrite H2 (Hnot' n.+1 c) //.
rewrite [Xsub _ _]/= Xpow_idem Xpow_Xreal /= zeroF /=; last first.
  by change (fact nm1 + _)%coq_nat with (fact nm1.+1); apply: INR_fact_neq_0.
change (fact nm1 + _)%coq_nat with (fact n).
change((x - r0) * _)%Re with ((x - r0) ^ n)%Re.
rewrite /u I.upper_correct in Hx.
apply: (@upper_Xneg_over X c r0 nm1 _ _ _ x) =>//.
by rewrite /l /u I.lower_correct I.upper_correct in Hneg.
Qed.

Lemma Ztech_derive_sign (X : I.type) (n : nat) :
  not_empty (I.convert X) ->
  ~ Xnan_ex XDn n.+1 (I.convert X) ->
  I.bounded X = true ->
  isNNegOrNPos (tnth (IP X n.+1) n.+1) = true ->
  Xcst_sign (XDn n.+1) (I.convert_bound (I.lower X)) (I.convert_bound (I.upper X)).
Proof.
move=> [t Ht] Hnot Hbnd Hsign.
have Hnot' := Xnan_ex_not Hnot.
have Hstep : Xcst_sign
  (fun x => (XDn n.+1 x) / Xreal (INR (fact n.+1)))%XR
  (I.convert_bound (I.lower X)) (I.convert_bound (I.upper X)).
  move: Hsign; set Gamma := tnth _ _.
  set g := fun x => ((XDn n.+1 x) / Xreal (INR (fact n.+1)))%XR.
  rewrite /isNNegOrNPos.
  case E : I.sign_large =>// _;
    have := I.sign_large_correct Gamma; rewrite E => Hmain.
  - left; move=> x Hx v.
    have inGamma : contains (I.convert Gamma) (g (Xreal x)).
      rewrite /g -(XPoly_nth _ (n:=n.+1)) //.
      apply: Poly_nth =>//.
      apply: contains_trans Hx;
        by [apply: bounded_contains_lower Ht|apply: bounded_contains_upper Ht].
      move/(_ _ inGamma) in Hmain.
      rewrite /proj_fun.
      by rewrite Hmain; auto with real.
  - right; move=> x Hx v.
    have inGamma : contains (I.convert Gamma) (g (Xreal x)).
      rewrite /g -(XPoly_nth _ (n:=n.+1)) //.
      apply: Poly_nth =>//.
      apply: contains_trans Hx;
        by [apply: bounded_contains_lower Ht|apply: bounded_contains_upper Ht].
      move/(_ _ inGamma) in Hmain.
      rewrite /proj_fun.
      rewrite (proj1 Hmain).
      exact: proj2 Hmain.
  - left; move=> x Hx v.
    have inGamma : contains (I.convert Gamma) (g (Xreal x)).
      rewrite /g -(XPoly_nth _ (n:=n.+1)) //.
      apply: Poly_nth =>//.
      apply: contains_trans Hx;
        by [apply: bounded_contains_lower Ht|apply: bounded_contains_upper Ht].
      move/(_ _ inGamma) in Hmain.
      rewrite /proj_fun.
      rewrite (proj1 Hmain).
      exact: proj2 Hmain.
have: Xcst_sign
  (fun x : ExtendedR => (Xreal (proj_val (XDn n.+1 x)) / Xreal (INR (fact n.+1)))%XR)
  (I.convert_bound (I.lower X)) (I.convert_bound (I.upper X)).
  apply: eq'_Xcst_sign Hstep.
  case=> [//|x] Hx.
  rewrite (Hnot' n.+1) //.
  apply: contains_trans Hx;
  by [apply: bounded_contains_lower Ht|apply: bounded_contains_upper Ht].
case=>[Hpos|Hneg]; [left|right].
- move=> x Hx v.
  move/(_ x Hx v): Hpos.
  rewrite /= zeroF /proj_fun.
  rewrite (Hnot' n.+1 _) //=.
  move=> Htop; apply: Rdiv_pos_compat_rev Htop _.
  change R0 with (INR O).
  apply: lt_INR.
  change (fact n + _)%coq_nat with (fact n.+1).
  apply: lt_O_fact.
  apply: contains_trans Hx;
    by [apply: bounded_contains_lower Ht|apply: bounded_contains_upper Ht].
  by change (fact n + _)%coq_nat with (fact n.+1); apply: INR_fact_neq_0.
move=> x Hx v.
move/(_ x Hx v): Hneg.
rewrite /= zeroF /proj_fun.
  rewrite (Hnot' n.+1 _) //=.
     move=> Htop; apply: Rdiv_neg_compat_rev Htop _.
     change R0 with (INR O).
     apply: lt_INR.
     change (fact n + _)%coq_nat with (fact n.+1).
     exact: lt_O_fact.
  by apply: contains_trans Hx;
    [apply: bounded_contains_lower Ht|apply: bounded_contains_upper Ht].
by change (fact n + _)%coq_nat with (fact n.+1); apply: INR_fact_neq_0.
Qed.
*)

Theorem i_validTM_Ztech n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (IP X0 n) (Ztech prec IP (IP X0 n) F X0 X n)) xf.
Proof using validPoly_ validIPoly_ xf F prec X0 X Hder def dom.
move=> Hsub tHt.
case E1 : (isNNegOrNPos (Pol.nth (IP X n.+1) n.+1)); last first.
  rewrite (ZtechE1 _ _ _ _ E1).
  exact: i_validTM_TLrem.
case E2 : (I.bounded X); last first.
  rewrite (ZtechE2 _ _ _ _ _ _ E2).
  exact: i_validTM_TLrem.
have [t Ht] := tHt.
admit.
(*
have XDn_0_Xnan : Dn 0 Xnan = Xnan by rewrite XDn_0.
set err := Ztech prec IP (IP X0 n) F0 X0 X n.
have [r' Hr'0] : not_empty (I.convert X0).
  exact: contains_not_empty Ht.
have Hr' : contains (I.convert X) (Xreal r').
  exact: subset_contains Hsub _ Hr'0.
pose x' := Xreal r'.
have XNNan : I.convert X <> IInan.
  move=> HX.
  rewrite isNNegOrNPos_false // in E1.
  move: (@Poly_nth validPoly_ X Xnan n.+1 n.+1).
  have XL := @XPoly_nth validXPoly_ Xnan n.+1 n.+1 (leqnn _).
  rewrite HX {}XL; move/(_ I (leqnn _)); rewrite XDn_Xnan'.
  by move/(contains_Xnan).
split=>//.
  rewrite /= /err /Ztech E1 E2 /=.
  apply: I.join_correct; right.
  have C1 : contains (I.convert (F0 X0)) (XF0 (Xreal r')) by exact: F0_contains.
  case E0 : (XF0 (Xreal r')) => [|r'0].
    set J := I.convert (I.sub prec _ _).
    suff->: J = Interval_interval.Inan by done.
    rewrite E0 in C1.
    have {C1} C1 := contains_Xnan C1.
    rewrite {}/J.
    have L := @Poly_nth validPoly_ X0 x' n 0 Hr'0 erefl.
    exact: (Isub_Inan_propagate_l _ L).
  have->: Xreal 0 = Xsub (Xreal r'0) (Xreal r'0) by simpl; f_equal; ring.
  apply: I.sub_correct; rewrite E0 // in C1.
  rewrite -{}E0 in C1 *.
  have HK := @Poly_nth validPoly_ X0 (Xreal r') n 0 Hr'0 erefl.
  by rewrite XPoly_nth0 in HK.
move=> /= xi0 Hxi0; exists (XP xi0 n); split; first exact: Poly_size.
  by move=> k Hk; apply: Poly_nth; rewrite // Poly_size' in Hk.
pose Idelta := fun X => I.sub prec (F0 X) (horner prec (IP X0 n) (I.sub prec X X0)).
pose Xdelta0 := Xdelta n xi0.
move=> x Hx.
have [Hex|Hnot] := Xnan_ex_or XDn n.+1 (I.convert X).
  have [i [y [H1 H2]]] := Hex.
  rewrite isNNegOrNPos_false // in E1.
  have HK := @Poly_nth validPoly_ X (Xreal y) n.+1 n.+1 H1 (ltnSn n.+1).
  rewrite XPoly_nth in HK =>//.
  have Hn1 := @XDn_Xnan XDn_ (n.+1-i) i (Xreal y) H2.
  rewrite subnK in Hn1; last by case: i {H2}.
  rewrite Hn1 /= in HK.
  exact: contains_Xnan.
rewrite /err /Ztech E1 E2 /=.
set Delta := I.join (I.join _ _) _; rewrite -/(Xdelta n xi0 x) -/(Xdelta0 x).
have [Hlower Hupper] := bounded_singleton_contains_lower_upper E2.
have {Hlower} Hlower: contains
  (I.convert (Idelta (Ibnd2 (I.lower X))))
  (Xdelta0 (I.convert_bound (I.lower X))).
  apply: I.sub_correct; first exact: F0_contains.
  apply: convert_horner; [by rewrite (Poly_size X0)|..|exact: I.sub_correct].
  move=> k Hk; apply: Poly_nth =>//.
  by rewrite Poly_size' in Hk.
have {Hupper} Hupper : contains
  (I.convert (Idelta (Ibnd2 (I.upper X))))
  (Xdelta0 (I.convert_bound (I.upper X))).
  apply: I.sub_correct; first exact: F0_contains.
  apply: convert_horner; [by rewrite (Poly_size X0)|..|exact: I.sub_correct].
  move=> k Hk; apply: Poly_nth =>//.
  by rewrite Poly_size' in Hk.
have HX0 : contains (I.convert (Idelta X0)) (Xdelta0 xi0).
  apply: I.sub_correct; first exact: F0_contains.
  apply: convert_horner; [by rewrite (Poly_size X0)|..|exact: I.sub_correct].
  move=> k Hk; apply: Poly_nth =>//.
  by rewrite Poly_size' in Hk.
have {Hlower} Hlower: contains
  (I.convert Delta)
  (Xdelta0 (I.convert_bound (I.lower X))).
  by apply: I.join_correct; left; apply: I.join_correct; left.
have {Hupper} Hupper : contains
  (I.convert Delta)
  (Xdelta0 (I.convert_bound (I.upper X))).
  by apply: I.join_correct; left; apply: I.join_correct; right.
have H'xi0 : contains (I.convert X) xi0 by
  exact: (subset_contains (I.convert X0)).
have {HX0} HX0 : contains (I.convert Delta) (Xdelta0 xi0).
  apply: I.join_correct; right.
  apply: I.sub_correct; first exact: F0_contains.
  case: xi0 Hxi0 H'xi0 {Xdelta0 HX0 Hlower Hupper} =>[|xi0] Hxi0 H'xi0.
    move/contains_Xnan in Hxi0.
    rewrite Hxi0 /= in Hsub.
    by case: (I.convert X) Hsub XNNan.
  rewrite [Xsub _ _]/= Rminus_diag_eq //.
  suff->: PolR.horner tt (XP (Xreal xi0) n) (Xreal 0) =
    (PolR.tnth (XP (Xreal xi0) n) 0) by apply: Poly_nth.
  rewrite PolR.is_horner XPoly_size big_ord_recl /=.
  rewrite big1 ?Xadd_0_r// ?Xmul_1_r//.
  move=> i _.
  rewrite /bump /= SuccNat2Pos.id_succ /= Rmult_0_l.
  case Ey: PolR.tnth =>[|y]; last by simpl; f_equal; ring.
  exfalso; apply: Hnot; rewrite /Xnan_ex.
  rewrite XPoly_nth in Ey; last by case: i.
  exists (inord (lift ord0 i)); rewrite inordK //= /bump /=; last first.
    by rewrite add1n; apply: ltnW; case: (i).
  exists xi0; split=>//.
  case: XDn Ey =>[//|r] /=.
  replace (INR _) with (INR (fact i.+1)) by done.
  by rewrite fact_zeroF.
case: xi0 H'xi0 Hxi0 @Xdelta0 Hlower Hupper HX0 => [HK|]; first exfalso.
  apply: (bounded_IInan E2); exact: contains_Xnan.
move=> xi0 H'xi0 Hxi0 Xdelta0 Hlower Hupper HX0.
have Hneq0 : Xreal xi0 <> Xnan by [].
have Hneq1 : I.convert_bound (I.lower X) <> Xnan.
  move=> K; rewrite K in Hlower; exfalso; exact: (bounded_lower_Xnan E2).
have Hneq2 : I.convert_bound (I.upper X) <> Xnan.
  move=> K; rewrite K in Hupper; exfalso; exact: (bounded_upper_Xnan E2).
have Hnot' : ~ Xnan_ex XDn n (I.convert X)
  by move=> K; apply: Hnot; apply: Xnan_ex_S.
have [Hlow|Hup] := @contains_lower_or_upper X (Xreal xi0) x XNNan Hx H'xi0.
  have [||H1|H2] := @Xmonot_contains_weak Xdelta0 _ _ _ _ Hneq1 Hneq0 _ Hlow.
  + rewrite /Xdelta0; apply: (Xdelta_real _(X:=I.convert X)) =>//.
    exact: (@bounded_contains_lower X (Xreal xi0) _ _).
  + apply: proj1 (@Zumkeller_monot_rem X xi0 n E2 H'xi0 Hnot _).
    apply: Ztech_derive_sign =>//.
    by exists xi0.
  + exact: contains_trans (I.convert Delta) _ _ (Xdelta0 x) Hlower HX0 H1.
  exact: contains_trans (I.convert Delta) _ _ (Xdelta0 x) HX0 Hlower H2.
have [||H1|H2] := @Xmonot_contains_weak Xdelta0 _ _ _ _ Hneq0 Hneq2 _ Hup.
+ rewrite /Xdelta0; apply: (Xdelta_real _(X:=I.convert X)) =>//.
  exact: (@bounded_contains_upper X (Xreal xi0) _ _).
+ apply: proj2 (@Zumkeller_monot_rem X xi0 n E2 H'xi0 Hnot _).
  apply: Ztech_derive_sign =>//.
  by exists xi0.
+ exact: contains_trans (I.convert Delta) _ _ (Xdelta0 x) HX0 Hupper H1.
exact: contains_trans (I.convert Delta) _ _ (Xdelta0 x) Hupper HX0 H2.
*)
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
Definition XP_rec1 xi0 := PolR.trec1 (XF_rec xi0) (XF0 xi0).

Instance validXPoly_rec1 :
  validXPoly XP_rec1.
Proof.
constructor; first by move=> *; rewrite PolR.tsize_trec1.
move=> r n k Hkn.
elim: k n Hkn =>[|k IHk] n Hkn.
  rewrite PolR.trec1_spec0 /= XDn_0.
  case (XF0 r)=> // r0 /=.
  case C: (is_zero 1); last by f_equal; field.
    by rewrite /is_zero (Req_bool_false _ _ R1_neq_R0) in C.
have K := @PolR.trec1_spec (XF_rec r) (XF0 r) n k.
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
  have K' := @PolR.trec1_spec (XF_rec r0) (XF0 r0) n k.
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
  (RPA (trec1 (F_rec X0) (F0 X0) n) err) XF0.
Proof. exact: (@i_validTM_TLrem XP_rec1). (* Rely on typeclass_instances *) Qed.

Corollary TM_rec1_correct' X0 X n :
  let err := Ztech prec (fun t => trec1 (F_rec X) (F0 t))
    (trec1 (F_rec X0) (F0 X0) n) F0 X0 X n in
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (trec1 (F_rec X0) (F0 X0) n) err) XF0.
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
Definition XP_rec2 xi0 := PolR.trec2 (XF_rec xi0) (XF0 xi0) (XF1 xi0).

Instance validXPoly_rec2 :
  validXPoly XP_rec2.
Proof.
constructor; first by move=> *; rewrite PolR.tsize_trec2.
move=> r n k Hkn.
move: n Hkn.
elim/nat_ind_gen : k => k Hk n Hkn.
case ck : k=> [|k'].
  rewrite PolR.trec2_spec0 /= XDn_0.
  case: (XF0 r) => // r0 /=.
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
have K := @PolR.trec2_spec (XF_rec r) (XF0 r) (XF1 r) n k'' Hkn.
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
rewrite (@PolR.trec2_spec (XF_rec r0) (XF0 r0) (XF1 r0) n k'' Hkn).
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
  (RPA (trec2 (F_rec X0) (F0 X0) (F1 X0) n) err) XF0.
Proof. exact: (@i_validTM_TLrem XP_rec2). (* Rely on typeclass_instances *) Qed.

Corollary TM_rec2_correct' X0 X n :
  let err := Ztech prec (fun t i => trec2 (F_rec X) (F0 t) (F1 t) i)
    (trec2 (F_rec X0) (F0 X0) (F1 X0) n) F0 X0 X n in
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X)
  (RPA (trec2 (F_rec X0) (F0 X0) (F1 X0) n) err) XF0.
Proof. exact: (@i_validTM_Ztech XP_rec2). (* Rely on typeclass_instances *) Qed.

End rec2_correct.
*)
End ProofOfRec.

Theorem TM_cst_correct n (icst X0 X : I.type) (cst : ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  contains (I.convert icst) cst ->
  i_validTM (I.convert X0) (I.convert X) (TM_cst icst X0 X n) (Xmask cst).
Proof.
move=> Hsubset Hex Hcst.
admit. (*apply TM_rec1_correct with
 (XDn := (fun n x => match n with
                | 0 => Xmask cst x
                | _ => Xmask (Xmask (Xreal 0) cst) x
              end)%XR)
 (XF0 := Xmask cst)
 (F_rec := fun _ => Rec.cst_rec)
 (XF_rec := fun _ => TX.Rec.cst_rec) =>//.
+ exact: nth_Xderive_pt_cst.
+ by move=> *; apply: I.mask_correct.
+ move=> x0 x ix0 ix k h0 h.
  rewrite /Rec.cst_rec /TX.Rec.cst_rec.
  apply: I.mask_correct =>//.
  by rewrite I.zero_correct; split; auto with real.
move=> r; case=> [/=|k].
  case: r=> [|r]=>//.
  case: cst Hcst => [|cst /=] Hcst=>//.
  rewrite zeroF; last by discrR.
  by rewrite /=; f_equal; field.
rewrite /TX.Rec.cst_rec.
case: cst Hcst; case: r => // a b Hb.
rewrite [fact]lock /= -lock.
rewrite !zeroF; first last.
    by apply: not_0_INR; apply: fact_neq_0.
  by apply: not_0_INR; apply: fact_neq_0.
by rewrite /Rdiv !Rmult_0_l.*)
Qed.

Theorem TM_cst_correct_strong n (icst X0 X : I.type) (f:ExtendedR->ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  is_const f X icst ->
  i_validTM (I.convert X0) (I.convert X) (TM_cst icst X0 X n) f.
Proof.
move=> Hsubset [t Ht] [cst Hcst1 Hcst2].
admit.
(*apply: (@TM_fun_eq_real (Xmask cst) _ _ _ _ _ (TM_cst_correct _ _ _ _)) =>//.
  by move=> x Hx; rewrite Hcst2.
by exists t.*)
Qed.

Lemma size_TM_cst c X0 X n : Pol.size (approx (TM_cst c X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec1. Qed.

Definition TM_any (Y : I.type) (X : I.type) (n : nat) :=
  let pol := Pol.polyCons (Imid Y) Pol.polyNil in
  {| approx := if n == 0 then pol
                   else Pol.set_nth pol n Pol.Int.zero;
     error := I.mask (I.sub prec Y (Imid Y)) X
  (* which might be replaced with [I.sub prec Y (Imid Y)] *)
  |}.

Definition sizes := (Pol.size_polyNil, Pol.size_polyCons,
                     PolR.size_polyNil, PolR.size_polyCons,
                     Pol.size_set_nth, PolR.size_set_nth).

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
have [x0 Hx0] := H0.
have Hx0': contains(I.convert X)(Xreal x0) by exact:subset_contains Hsubset _ _.
have Hrr := Hf _ Hx0'.
set r := proj_val (f (Xreal x0)).
have Hr : contains (I.convert Y) (Xreal r).
  exact: contains_Xreal.
split=>//.
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
- admit. (*move=> N xi0 Hxi0.
  set pol0 := PolR.tpolyCons (I.convert_bound (I.midpoint Y)) PolR.tpolyNil.
  set pol' := if n == 0 then pol0 else PolR.tset_nth pol0 n (Xreal 0).
  exists pol'.
  rewrite /N {N} /pol' /pol0 /TM_any.
  split=>//.
  + case: n.
      by rewrite !sizes.
    move=> n /=; rewrite tsize_set_nth PolR.tsize_set_nth.
    congr maxn.
    by rewrite !sizes.
  + move=> k Hk /=.
    case: n Hk =>//=.
      rewrite tsize_polyCons tsize_polyNil ltnS leqn0.
      move/eqP->.
      rewrite ?(tnth_polyCons,PolR.tnth_polyCons).
      * by apply: Imid_contains; exists r.
      * by rewrite PolR.tsize_polyNil.
      * by rewrite tsize_polyNil.
    move=> n.
    rewrite tsize_set_nth !sizes ltnS.
    case: k =>/=.
      rewrite tnth_set_nth PolR.tnth_set_nth /=.
      rewrite tnth_polyCons // PolR.tnth_polyCons //.
      by move=> _;
        apply: Imid_contains; exists r.
    move=> k; rewrite ltnS => Hk /=.
    rewrite tnth_set_nth PolR.tnth_set_nth /=.
    case: (k.+1 == n.+1); first by rewrite I.zero_correct; split;auto with real.
    rewrite tnth_out ?sizes // PolR.tnth_out ?sizes //.
    by rewrite I.zero_correct; split; auto with real.
  + move=> x Hx /=.
    case: x Hx =>[|x] Hx.
      move/contains_Xnan: Hx.
      move=> top; rewrite (Imask_IInan_r _ top) //.
      apply: not_emptyE.
      exists (Xsub (Xreal r) (I.convert_bound (I.midpoint Y))).
      apply I.sub_correct =>//.
      apply: Imid_contains.
      by exists r.
    have := Hf _ Hx.
    case Efx: (f (Xreal x)) =>[|y] /=.
      move/contains_Xnan=> Hnan.
      set J := I.mask _ _; suff->: I.convert J = IInan by done.
      rewrite Imask_IInan_l //.
        by exists x.
      erewrite Isub_Inan_propagate_l =>//.
      apply Imid_contains.
      by exists r.
    case E: (I.convert X) Hsubset Hx => [|l u] Hsubset Hx.
      rewrite (Imask_IInan_r _ E) //.
      apply: not_emptyE.
      exists (Xsub (Xreal r) (I.convert_bound (I.midpoint Y))).
      apply: I.sub_correct =>//.
      apply: Imid_contains.
      by exists r.
    move=> Hy.
    case: xi0 Hxi0 => [|xi0] Hxi0.
      have := subset_contains _ _ Hsubset Xnan Hxi0; done.
    rewrite is_horner_mask  /=.
    rewrite bigXadd_Xreal_proj.
      apply: Imask_contains.
        by exists xi0; rewrite -E in Hsubset; apply:subset_contains Hsubset _ _.
      case: n =>//=.
        rewrite !sizes big_ord_recl big_ord0 /=.
        set s := proj_val _.
        change (Xreal _) with (Xsub (Xreal y) (Xreal (s + 0))).
        apply: I.sub_correct=>//.
        rewrite /s PolR.tnth_polyCons // Xmul_1_r Rplus_0_r /=.
        have HY : not_empty (I.convert Y) by exists r.
        have := Imid_contains HY.
        have HY' : exists z : ExtendedR, contains (I.convert Y) z
          by exists (Xreal r).
        by have [{2}-> _] := I.midpoint_correct _ HY'.
      move=> n; rewrite !sizes big_ord_recl big1.
        set s := proj_val _.
        change (Xreal _) with (Xsub (Xreal y) (Xreal (s + 0))).
        apply: I.sub_correct=>//.
        rewrite /s PolR.tnth_set_nth /=.
        rewrite PolR.tnth_polyCons // Xmul_1_r Rplus_0_r.
        have HY : not_empty (I.convert Y) by exists r.
        have := Imid_contains HY.
        have HY' : exists z : ExtendedR, contains (I.convert Y) z
          by exists (Xreal r).
        by have [{2}-> _] := I.midpoint_correct _ HY'.
      move=> i _.
      rewrite lift0 PolR.tnth_set_nth.
      case: (i.+1 == n.+1).
        case: i => m Hm.
        rewrite FullXR.tpow_S /=.
        case: FullXR.tpow =>// z.
        by rewrite Rmult_0_l.
      rewrite PolR.tnth_out.
        rewrite FullXR.tpow_S /=.
        case: FullXR.tpow =>// z.
        by rewrite Rmult_0_l.
      by rewrite !sizes.
    case => m /= Hm.
    case: n Hm =>//=.
      rewrite !sizes ltnS leqn0.
      move/eqP->.
      rewrite PolR.tnth_polyCons //.
      have HY' : exists z : ExtendedR, contains (I.convert Y) z
        by exists (Xreal r).
      by have [{2}-> _] := I.midpoint_correct _ HY'.
    move=> n.
    rewrite !sizes maxnSS maxn0 ltnS => Hm.
    rewrite PolR.tnth_set_nth.
    case: (m == n.+1) =>//.
      by rewrite [FullXR.tpow tt _ _]Xpow_idem Xpow_Xreal.
    case: m Hm => [|m Hm]; last by rewrite PolR.tnth_out ?sizes.
    move=> h0.
    rewrite PolR.tnth_polyCons //=.
    have HY' : exists z : ExtendedR, contains (I.convert Y) z
      by exists (Xreal r).
    by have [{2}-> _] := I.midpoint_correct _ HY'.
*)
Qed.

Lemma size_TM_var X0 X n : Pol.size (approx (TM_var X0 X n)) = n.+1.
Proof. exact: Pol.size_rec2. Qed.

Lemma TM_var_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_var X0 X n) (fun x => x).
Proof.
move=> Hss Hex.
rewrite /TM_var /T_var.
admit. (*
apply TM_rec2_correct with
  (XDn := fun n x =>
    if n == O then x else
      if n == 1 then Xmask (Xreal 1) x else
        Xmask (Xreal 0) x)
  (XF1 := fun x => Xmask (Xreal 1) x)
  (F_rec := fun _ => Rec.var_rec)
  (XF_rec := fun _ => TX.Rec.var_rec)=> //.
+ exact: nth_Xderive_pt_var.
+ move=> x X1 HX1.
  rewrite /tone.
  by apply: I.mask_correct; first exact: I.fromZ_correct.
+ move=> x0 x x1 X1 X2 X3 h0 h h1;
  rewrite /Rec.var_rec /TX.Rec.var_rec.
  by apply I.mask_correct; apply: I.mask_correct;
  first by rewrite I.zero_correct; split; auto with real.
move=> r k.
rewrite /TX.Rec.var_rec.
rewrite [fact]lock /= -lock.
case: r=> [|r].
  rewrite [fact]lock /= -lock.
  by case: k.
case: k=> [|k].
  rewrite /= !zeroF; discrR.
  by rewrite /=; f_equal; field.
rewrite [fact]lock /= -lock.
rewrite !zeroF; discrR; first last.
    by apply: not_0_INR; apply: fact_neq_0.
  by apply: not_0_INR; apply: fact_neq_0.
case: k=> [|k].
  rewrite /= !zeroF; discrR.
  by rewrite /=; f_equal; field.
rewrite [fact]lock /= -lock.
rewrite !zeroF; discrR.
  rewrite [fact]lock /= -lock.
  f_equal; field.
  by apply: not_0_INR; apply: fact_neq_0.
by apply: not_0_INR; apply: fact_neq_0.
*)

Qed.

Theorem TM_var_correct_strong X0 X n (f : ExtendedR -> ExtendedR) :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  (forall x : R, contains (I.convert X) (Xreal x) -> f (Xreal x) = (Xreal x)) ->
  i_validTM (I.convert X0) (I.convert X) (TM_var X0 X n) f.
Proof.
move=> Hsubset [v Hv] H.
admit.
(*
apply: (TM_fun_eq
  (f := fun x => match x with Xnan => f Xnan | Xreal _ => f x end)).
  by case=> [|r] _.
apply: (i_validTM_nan (v := Xnan)).
apply: (TM_fun_eq (f := id)); last by apply: TM_var_correct =>//; exists v.
case=>//.
by move=> *; symmetry; apply: H.
*)
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
move=> Hsubset [t Ht].
admit. (* FIXME
eapply (i_validTM_Ztech
  (XDn := (fun k x => (\big[Xmul/Xreal 1]_(i < k) Xreal (IZR (p - Z.of_nat i))) *
                      (if Z.ltb p Z0 || Z.geb p (Z.of_nat k) then
                         Xpower_int x (p - Z.of_nat k)%Z
                       else Xmask (Xreal 0) x)))%XR); last by eexists; exact Ht.
6: done.
done.
red=> x; simpl.
apply nth_Xderive_pt_power_int.
apply: I.power_int_correct.
instantiate (1 := TX.T_power_int tt p).
split.
move=> x k.
rewrite (@PolR.tsize_dotmuldiv k.+1) 1?(@tsize_dotmuldiv k.+1) //
  ?(tsize_trec1, PolR.tsize_trec1, size_rec1up) //.
rewrite /T_power_int /TX.T_power_int.
move=> x n' k Hk.
rewrite PolR.tnth_dotmuldiv ?falling_seq_correct ?fact_seq_correct //.
rewrite tnth_pow_aux_rec //.
rewrite big_mkord.
rewrite bigXmul_Xreal_i.
rewrite !Xdiv_split.
rewrite !Xmul_assoc (Xmul_comm (Xinv _)).

repeat f_equal.
elim: k Hk =>[//|k IHk] Hk; first by rewrite !big_ord0.
rewrite !big_ord_recr /= -IHk ?mult_IZR //.
by rewrite ltnS in Hk; exact: ltnW.
by rewrite INR_IZR_INZ.
(* . *)
rewrite (@PolR.tsize_dotmuldiv n'.+1) //.
by rewrite PolR.tsize_trec1.
by rewrite size_rec1up.
by rewrite size_rec1up.

split=> Y y m.
rewrite (@PolR.tsize_dotmuldiv m.+1) //.
rewrite (@tsize_dotmuldiv m.+1) //.
by rewrite tsize_trec1.
by rewrite size_rec1up.
by rewrite size_rec1up.
by rewrite PolR.tsize_trec1.
by rewrite size_rec1up.
by rewrite size_rec1up.
(* . *)
move=> k Hy Hk.
rewrite ?(PolR.tnth_dotmuldiv, tnth_dotmuldiv); first last.
rewrite (@tsize_dotmuldiv m.+1) //.
by rewrite tsize_trec1.
by rewrite size_rec1up.
by rewrite size_rec1up.
rewrite (@PolR.tsize_dotmuldiv m.+1) //.
by rewrite PolR.tsize_trec1.
by rewrite size_rec1up.
by rewrite size_rec1up.
apply I.mul_correct.
apply I.div_correct.
rewrite falling_seq_correct.
rewrite /tfromZ -Z2R_IZR;apply I.fromZ_correct. (*TODO:Refactor*)
by rewrite -ltnS.
rewrite /tfromZ -Z2R_IZR;apply I.fromZ_correct. (*TODO:Refactor*)
case: k m Hk=>[//|k] m Hk.
rewrite trec1_spec0 PolR.trec1_spec0.
exact: I.power_int_correct.
rewrite ltnS in Hk.
rewrite trec1_spec // PolR.trec1_spec //.
rewrite /Rec.pow_aux_rec /TX.Rec.pow_aux_rec.
set o := (_ || _).
case: o.
  exact: I.power_int_correct.
apply: I.mask_correct =>//.
by rewrite I.zero_correct; split; auto with real.
*)
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

Lemma TM_sqrt_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_sqrt X0 X n) Xsqrt.
Proof.
move=> Hsubset Hex.
admit.
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
*)
Qed.

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

Lemma TM_sin_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_sin X0 X n) Xsin.
Proof.
move=> Hsubset Hex.
admit.
(*
apply TM_rec2_correct' with
  (XDn := nth_Xsin)
  (XF1 := Xcos)
  (F_rec := fun _ => Rec.sin_rec prec)
  (XF_rec := fun _ => TX.Rec.sin_rec tt)
=>//.
+ by move=> x; apply: nth_Xderive_pt_sin.
+ by move=> x X1 HX1; apply: I.sin_correct.
+ by move=> x X1 HX1; apply: I.cos_correct.
+ move=>*; rewrite /Rec.sin_rec /TX.Rec.sin_rec.
  apply: I.div_correct.
  apply: I.neg_correct; first done.
  apply: I.mul_correct.
    rewrite /tnat.
    rewrite INR_IZR_INZ.
    rewrite -Z2R_IZR.
    by apply: I.fromZ_correct.
  rewrite /tnat.
  rewrite INR_IZR_INZ.
  rewrite -Z2R_IZR.
  by apply: I.fromZ_correct.
move=> r k; rewrite /TX.Rec.sin_rec.
rewrite succnK.
suff->: nth_Xsin k.+2 r = (- nth_Xsin k r)%XR.
  case cn : (nth_Xsin k r) => [|sk] //.
  xtotal.
  + by elim (not_0_INR _ (fact_neq_0 k)).
  + elim (Rmult_integral _ _ Y0) => H0.
      have H1 : INR k.+2 <> 0%Re.
        by apply: Rgt_not_eq; apply: lt_0_INR; omega.
     by elim H1.
  + have H1 : INR k.+1 <> 0%Re.
      by apply: Rgt_not_eq; apply: lt_0_INR; omega.
  + by elim H1.
  + by elim (not_0_INR _ (fact_neq_0 k.+2)).
  f_equal.
  rewrite /Rdiv.
  field_simplify=>//.
    f_equal.
    rewrite -2!mult_INR; f_equal.
    rewrite 2!fact_simpl.
    by rewrite -(mult_assoc (fact k)) (mult_assoc (k.+2)) mult_comm.
  by elim (RIneq.Rmult_neq_0_reg _ _ Y0) => H1 H2.
rewrite /=; case cn : (nth_Xsin k r) => [|ns] //=.
f_equal; ring.
*)
Qed.

Lemma size_TM_sin X0 X (n : nat) : Pol.size (approx (TM_sin X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec2. Qed.

Lemma TM_cos_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_cos X0 X n) Xcos.
Proof.
move=> Hsubset Hex.
admit.
(*
apply TM_rec2_correct' with
  (XDn := nth_Xcos)
  (XF1 := fun x => Xneg (Xsin x))
  (F1 := fun x => topp (tsin prec x))
  (F_rec := fun _ => Rec.cos_rec prec)
  (XF_rec := fun _ => TX.Rec.cos_rec tt)
=>//.
+ by move=> x; apply: nth_Xderive_pt_cos.
+ by move=> x X1 HX1; apply: I.cos_correct.
+ by move=> x X1 HX1; apply: I.neg_correct; apply: I.sin_correct.
+ move=>*; rewrite /Rec.cos_rec /TX.Rec.cos_rec.
  apply: I.div_correct.
    exact: I.neg_correct.
  apply: I.mul_correct.
    rewrite /tnat.
    rewrite INR_IZR_INZ.
    rewrite -Z2R_IZR.
    exact: I.fromZ_correct.
  rewrite /tnat.
  rewrite INR_IZR_INZ.
  rewrite -Z2R_IZR.
  exact: I.fromZ_correct.
move=> r k; rewrite /TX.Rec.cos_rec.
rewrite succnK.
suff->: nth_Xcos k.+2 r = (- nth_Xcos k r)%XR.
  case cn : (nth_Xcos k r) => [|sk] //.
  xtotal.
  + by elim (not_0_INR _ (fact_neq_0 k)).
  + elim (Rmult_integral _ _ Y0) => H0.
      have H1 : INR k.+2 <> 0%Re.
        by apply: Rgt_not_eq; apply: lt_0_INR; omega.
      by elim H1.
    have H1 : INR k.+1 <> 0%Re.
      by apply: Rgt_not_eq; apply: lt_0_INR; omega.
    by elim H1.
  + by elim (not_0_INR _ (fact_neq_0 k.+2)).
  f_equal.
  rewrite /Rdiv.
  field_simplify=> //.
    f_equal.
    rewrite -2!mult_INR; f_equal.
    rewrite 2!fact_simpl.
    by rewrite -(mult_assoc (fact k)) (mult_assoc (k.+2)) mult_comm.
  by elim (RIneq.Rmult_neq_0_reg _ _ Y0) => H1 H2.
rewrite /=; case cn : (nth_Xcos k r) => [|ns] //=.
f_equal; ring.
*)
Qed.

Lemma size_TM_cos X0 X (n : nat) : Pol.size (approx (TM_cos X0 X n)) = n.+1.
Proof. by rewrite Pol.size_rec2. Qed.

Lemma size_TM_tan X0 X (n : nat) : Pol.size (approx (TM_tan X0 X n)) = n.+1.
Proof. by rewrite Pol.size_grec1. Qed.

Lemma size_TM_atan X0 X (n : nat) : Pol.size (approx (TM_atan X0 X n)) = n.+1.
Proof. by rewrite Pol.size_grec1. Qed.

Instance validIPoly_atan : validIPoly Xatan (TR.T_atan tt) (TI.T_atan prec).
Proof.
constructor.
- by move=> *; rewrite PolR.size_grec1 Pol.size_grec1.
- move => X0 xi0 n Hx.
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
- move=> X [x H1 H2] n; done.
Qed.

Instance validPoly_atan : validPoly Xatan (TR.T_atan tt).
Proof.
constructor.
- by move=> *; rewrite PolR.size_grec1.
- move=> x n k; rewrite ltnS => H;
  rewrite /TR.T_atan /PolR.nth /PolR.grec1
    (nth_grec1up_indep _ _ _ _ _ 0%R (m2 := k)) //
    nth_grec1up_last.
  case: k H => [|k H]; first by rewrite /= ?Rdiv_1.
  rewrite last_grec1up // head_gloop1.
  rewrite [size _]/= subn1 [_.+1.-1]/=.
  elim: k H x => [|k IHk] H x.
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
    apply: (@Rmult_eq_reg_r ri0); first rewrite -IHk Rmult_assoc Hri0; try lra.
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
    rewrite -{1}(Rmult_1_r (qk^`().[x])%P) -Rmult_plus_distr_l.
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
Qed.

Lemma TM_atan_correct X0 X n :
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) (TM_atan X0 X n) Xatan.
Proof.
move=> Hsubset [t Ht].
apply: i_validTM_Ztech =>//; last by exists t.
move=> k r Hr.
elim: k => [//|k IHk].
admit. (* TODO: derivability *)
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

Lemma horner_add pf pg x :
  PolR.size pf = PolR.size pg ->
  PolR.horner tt (PolR.add tt pf pg) x =
  Rplus (PolR.horner tt pf x) (PolR.horner tt pg x).
Proof.
(* Erik: Ideally, we should put this lemma in a more generic place *)
move=> Heq.
have Hsize := PolR.size_add tt pf pg.
rewrite Heq maxnn in Hsize.
admit.
(*
case Eg : (PolR.tsize pg) => [| n'].
  rewrite !PolR.is_horner Heq Hsize Eg !big_ord0.
  by case x => [|rx] //=; rewrite Rplus_0_l.
rewrite !is_horner_pos.
- rewrite Heq Hsize Eg.
  rewrite -big_split /=.
  apply: eq_bigr => i _; rewrite PolR.tnth_tadd.
    (* OLD CODE: by rewrite FullXR.tmul_distrl. *)
    by rewrite Xmul_Xadd_distr_r.
- by rewrite Heq Eg minnn.
- by rewrite Eg.
- by rewrite Heq Eg.
- by rewrite Hsize Eg.
*)
Qed.

Lemma horner_opp pf x :
  PolR.horner tt (PolR.opp pf) x =
  Ropp (PolR.horner tt pf x).
Proof.
(* Erik: Ideally, we should put this lemma in a more generic place *)
admit.
(*
have Hsize := PolR.size_opp pf.
case Ef : (PolR.tsize pf) => [| n'].
  rewrite !PolR.is_horner Hsize Ef !big_ord0.
  by case x => [|rx] //=; rewrite Ropp_0.
rewrite !is_horner_pos; first last.
  by rewrite PolR.tsize_opp Ef.
  by rewrite Ef.
rewrite Hsize Ef.
rewrite (big_morph Xneg (id1 := Xreal 0) (op1 := Xadd)).
apply: eq_bigr.
move=> i _.
rewrite PolR.tnth_opp.
by rewrite Xmul_Xneg_distr_l.
case: i.
by rewrite Ef.
by move=>*; rewrite Xneg_Xadd.
by congr Xreal; auto with real.
*)
Qed.

Lemma horner_sub pf pg x :
  PolR.size pf = PolR.size pg ->
  PolR.horner tt (PolR.sub tt pf pg) x =
  Rminus (PolR.horner tt pf x) (PolR.horner tt pg x).
Proof.
(* Erik: Ideally, we should put this lemma in a more generic place *)
move=> Heq.
admit.
(*
have Hsize := PolR.size_sub tt pf pg.
rewrite Heq maxnn in Hsize.
case Eg : (PolR.tsize pg) => [| n'].
  rewrite !PolR.is_horner Heq Hsize Eg !big_ord0.
  by case x => [|rx] //=; rewrite Rminus_0_r.
rewrite !is_horner_pos; first last.
  by rewrite PolR.tsize_sub Heq Eg maxnn.
  by rewrite Heq Eg.
  by rewrite Eg.
rewrite Xsub_split.
rewrite (big_morph Xneg (id1 := Xreal 0) (op1 := Xadd)).
rewrite Heq Hsize Eg -big_split /=.
apply: eq_bigr.
move=> i _.
rewrite PolR.tnth_sub.
rewrite Xsub_split.
rewrite Xmul_Xadd_distr_r //=.
by rewrite Xmul_Xneg_distr_l.
case: i.
by move=>*; rewrite Heq Eg minnn.
by move=>*; rewrite Xneg_Xadd.
by congr Xreal; auto with real.
*)
Qed.

(* TODO: Remove superfluous hypothesis, cf. [TM_add_correct]. *)
Lemma TM_add_correct_gen (smallX0 : interval) (X : I.type) (TMf TMg : rpa) f g :
  I.subset_ smallX0 (I.convert X) ->
  Pol.size (approx TMf) = Pol.size (approx TMg) ->
  i_validTM smallX0 (I.convert X) TMf f ->
  i_validTM smallX0 (I.convert X) TMg g ->
  i_validTM smallX0 (I.convert X) (TM_add TMf TMg)
  (fun xr => Xadd (f xr) (g xr)).
Proof.
move=> HinX Heq [Hef H0 Hf] [Heg _ Hg].
split=>//.
  suff->: Xreal 0 = (Xreal 0 + Xreal 0)%XR by apply: I.add_correct.
  by rewrite /= Rplus_0_l.
admit.
(*
move=> N x0 Hx0.
move:(Hf x0 Hx0) (Hg x0 Hx0) => [pf [Hf1 Hf2 Hf3]] [pg [Hg1 Hg2 Hg3]].
exists (PolR.tadd tt pf pg).
split; first by rewrite /= PolR.tsize_tadd /N Pol.tsize_tadd Hf1 Hg1.
  move=> k Hk /=.
  rewrite tnth_tadd ?PolR.tnth_tadd; first last.
  - rewrite Heq minnn.
    by move: Hk; rewrite /N tsize_tadd Heq maxnn=> ->.
  - rewrite Hg1 Hf1 Heq minnn.
    by move: Hk; rewrite /N tsize_tadd Heq maxnn=> ->.
  apply: I.add_correct.
    apply: Hf2.
    by rewrite /= /N tsize_tadd -Heq maxnn in Hk.
  apply: Hg2.
  by rewrite /= /N tsize_tadd Heq maxnn in Hk.
move=> x Hx /=.
rewrite horner_add; last by rewrite Hf1 Hg1 Heq.
suff->: f x + g x - (PolR.horner tt pf (x - x0) + PolR.horner tt pg (x - x0))
  = f x - PolR.horner tt pf (x - x0) + (g x - PolR.horner tt pg (x - x0)).
  by apply: I.add_correct; [apply: Hf3|apply: Hg3].
rewrite 4!Xsub_split Xadd_assoc.
by rewrite Xneg_Xadd Xadd_assoc 2!(Xadd_comm (g x)) !Xadd_assoc.
*)
Qed.

Lemma TM_add_correct (X0 X : I.type) (TMf TMg : rpa) f g :
  Pol.size (approx TMf) = Pol.size (approx TMg) ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X) (TM_add TMf TMg)
  (fun xr => Xadd (f xr) (g xr)).
Proof.
move=> Heq Hf Hg.
case Hf => [_ H0 _].
by apply TM_add_correct_gen.
Qed.

Lemma TM_opp_correct (X0 X : interval) (TMf : rpa) f :
  i_validTM X0 X TMf f ->
  i_validTM X0 X (TM_opp TMf)
  (fun xr => Xneg (f xr)).
Proof.
move=> [Hsubset Hzero /= Hmain].
split=>//.
have->: let x := (Xreal 0) in x = Xneg x by simpl; f_equal; rewrite Ropp_0.
exact: I.neg_correct.
simpl=> x0 Hx0.
admit.
(*
have [a [Hsize Hcont Hdelta]] := Hmain _ Hx0.
exists (PolR.opp a).
split=>//.
by rewrite PolR.tsize_opp tsize_opp.
move=> k Hk.
rewrite tsize_opp in Hk.
have Hk' := Hk.

rewrite -Hsize in Hk'.
rewrite PolR.tnth_opp // tnth_opp //.
apply: I.neg_correct.
exact: Hcont.
move=> x Hx.
rewrite Xsub_split -Xneg_Xadd.
apply: I.neg_correct.
rewrite horner_opp -Xsub_split.
exact: Hdelta.
*)
Qed.

Lemma TM_sub_correct (X0 X : interval) (TMf TMg : rpa) f g :
  Pol.size (approx TMf) = Pol.size (approx TMg) ->
  i_validTM X0 X TMf f ->
  i_validTM X0 X TMg g ->
  i_validTM X0 X (TM_sub TMf TMg)
  (fun xr => Xsub (f xr) (g xr)).
Proof.
move=> Hsame [Hzero1 Hsubset1 /= Hmain1] [Hzero2 _ /= Hmain2].
split=>//.
have->: let x := (Xreal 0) in x = Xsub x x by simpl; f_equal; auto with real.
simpl error.
exact: I.sub_correct.
simpl=> x0 Hx0.
admit.
(*
have [a [Hsize1 Hcont1 Hdelta1]] := Hmain1 _ Hx0.
have [b [Hsize2 Hcont2 Hdelta2]] := Hmain2 _ Hx0.
exists (PolR.tsub tt a b).
split=>//.
by rewrite PolR.tsize_sub tsize_sub Hsize1 Hsize2.
move=> k Hk.
rewrite tsize_sub Hsame maxnn in Hk.
pose lem := (Hsame,tnth_sub,Hsize1,Hsize2,minnn).

rewrite ?(PolR.tnth_sub,tnth_sub) ?lem //.
by apply: I.sub_correct; [apply: Hcont1|apply: Hcont2]; rewrite ?lem.
move=> x Hx.
have->: f x - g x - PolR.horner tt (PolR.tsub tt a b) (x - x0)
  = (f x - PolR.horner tt a (x - x0)) - (g x - PolR.horner tt b (x - x0)).
  rewrite horner_sub; last by rewrite Hsize1 Hsize2 Hsame.
  rewrite !(Xsub_split,Xneg_Xadd).
  rewrite !Xadd_assoc; congr Xadd.
  rewrite -!Xadd_assoc; congr Xadd.
  by rewrite Xadd_comm.
apply: I.sub_correct; [exact: Hdelta1|exact: Hdelta2].
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
  RPA (MapI.polymap (I.mul prec a) (approx M))
      (I.mul prec a (error M)).

Definition TM_div_mixed_r (M : rpa) (b : I.type) : rpa :=
  RPA (MapI.polymap (I.div prec ^~ b) (approx M))
      (I.div prec (error M) b).

Lemma size_TM_mul_mixed a M :
  Pol.size (approx (TM_mul_mixed a M)) = Pol.size (approx M).
Proof. by rewrite MapI.size_polymap. Qed.

Lemma size_TM_div_mixed_r M b :
  Pol.size (approx (TM_div_mixed_r M b)) = Pol.size (approx M).
Proof. by rewrite MapI.size_polymap. Qed.

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
split=>//; first by rewrite (proj1 (contains_Xnan _) Lem).
move=> /= x0 Hx0.
admit.
(*
have [q [Hsize Hcont Hhorner]] := Hmain _ Hx0.
exists (MapX.tpolymap (Xdiv ^~ (Xreal R0)) q).
split.
- by rewrite MapX.tsize_polymap MapI.tsize_polymap.
- move=> k Hk.
  rewrite MapI.tsize_polymap in Hk.
  rewrite MapX.tnth_polymap ?Hsize // MapI.tnth_polymap ?Hsize //.
  apply: I.div_correct =>//.
  exact: Hcont.
- move=> x Hx.
  move/(_ x Hx) in Hhorner.
  rewrite Xdiv_0_r /=.
  rewrite -(Xdiv_0_r (Xreal R0)).
  exact: I.div_correct.
*)
Qed.

Lemma TM_mul_mixed_correct a M X0 X f (y : R) :
  contains (I.convert a) (Xreal y) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul_mixed a M)
  (fun x => Xmul (Xreal y) (f x)).
Proof.
move=> Hy [H0 Hss Hmain].
split=>//.
  have->: (Xreal 0) = (Xmul (Xreal y) (Xreal 0)) by simpl; congr Xreal; ring.
  exact: I.mul_correct.
move=> /= x0 Hx0.
admit.
(*
have [q [Hsize Hcont Hhorner]] := Hmain _ Hx0.
exists (MapX.tpolymap (Xmul (Xreal y)) q).
split.
- by rewrite MapX.tsize_polymap MapI.tsize_polymap.
- move=> k Hk.
  rewrite MapI.tsize_polymap in Hk.
  rewrite MapX.tnth_polymap ?Hsize // MapI.tnth_polymap ?Hsize //.
  apply: I.mul_correct =>//.
  exact: Hcont.
- move=> x Hx.
  move/(_ x Hx) in Hhorner.
  clear - Hhorner Hy.
  rewrite !is_horner_mask in Hhorner *.
  set sub2 := Xsub _ _.
  set sub1 := Xsub _ _ in Hhorner.
  suff->: sub2 = Xmul (Xreal y) sub1 by exact: I.mul_correct.
  rewrite XmulC.
  rewrite /sub1 Xsub_split Xmul_Xadd_distr_r.
  rewrite /sub2 XmulC /=.
  rewrite {1}Xsub_split.
  congr Xadd.
  rewrite Xmul_Xneg_distr_l.
  congr Xneg.
  case E : (x - x0)%XR => [//|r /=].
  rewrite MapX.tsize_polymap.
  set lhs := @bigop _ _ _ _ _.
  have->: lhs = \big[Xadd/Xreal 0]_(i < PolR.tsize q)
  (Xmul (Xmul (PolR.tnth q i)
  (FullXR.tpow tt (Xreal r) i)) (Xreal y)).
    apply: eq_bigr.
      move=> i _; rewrite MapX.tnth_polymap.
      by rewrite XmulC XmulA XmulC XmulA.
    by case: i.
  by rewrite big_Xmul_Xadd_distr.
*)
Qed.

Lemma TM_mul_mixed_nan1 a M f X0 X:
  not_empty (I.convert X0) ->
  contains (I.convert a) Xnan ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  let pol := approx (TM_mul_mixed a M) in
  forall k : nat, k < Pol.size pol ->
  I.convert (Pol.nth pol k) = IInan.
Proof.
case=>[t Ht].
move/contains_Xnan => Ha /=.
case=>[Hnan Hsubst Hmain].
rewrite MapI.size_polymap.
move=> k Hk.
rewrite MapI.nth_polymap //.
admit. (* FIXME
have [q [Hq1 Hq2 Hq3]] := Hmain _ Ht.
exact: Imul_Inan_propagate_l (Hq2 _ Hk) _.
*)
Qed.

Lemma TM_mul_mixed_nan2 a M f X0 X:
  contains (I.convert a) Xnan ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  I.convert (error (TM_mul_mixed a M)) = IInan.
Proof.
move/contains_Xnan => Ha /=.
case=>[Hnan Hsubst Hmain].
exact: Imul_Inan_propagate_l Hnan _.
Qed.

Corollary TM_mul_mixed_correct_strong a M X0 X f g :
  not_empty (I.convert X0) ->
  is_const f X a ->
  i_validTM (I.convert X0) (I.convert X) M g ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul_mixed a M)
  (fun x => Xmul (f x) (g x)).
Proof.
move=> tHt [[|y] Hy1 Hy2] Hg; move: (Hg) => [Hnan Hsubset Hmain].
- split=>//.
  by rewrite (TM_mul_mixed_nan2 Hy1 Hg).
  move=> /= x0 Hx0.
  admit. (*
  have [q [Hq1 Hq2 Hq3]] := Hmain _ Hx0.

  exists (MapX.tpolymap (Xmul Xnan) q).
  split.
  + by rewrite MapX.tsize_polymap MapI.tsize_polymap.
  + move=> k Hk.
    by rewrite (TM_mul_mixed_nan1 tHt Hy1 Hg).
  + move=> x Hx.
    by rewrite (TM_mul_mixed_nan2 Hy1 Hg).
apply: (@TM_fun_eq_real _ _ _ _ _ _ (TM_mul_mixed_correct Hy1 Hg)).
move=> x Hx.
by rewrite Hy2.
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
move=> Hy [H0 Hss Hmain].
split=>//.
  have->: (Xreal 0) = (Xdiv (Xreal 0) (Xreal y)).
  simpl.
  rewrite zeroF //.
  by simpl; congr Xreal; rewrite /Rdiv Rmult_0_l.
  exact: I.div_correct.
move=> /= x0 Hx0.
admit.
(*
have [q [Hsize Hcont Hhorner]] := Hmain _ Hx0.
exists (MapX.tpolymap (Xdiv ^~ (Xreal y)) q).
split.
- by rewrite MapX.tsize_polymap MapI.tsize_polymap.
- move=> k Hk.
  rewrite MapI.tsize_polymap in Hk.
  rewrite MapX.tnth_polymap ?Hsize // MapI.tnth_polymap ?Hsize //.
  apply: I.div_correct =>//.
  exact: Hcont.
- move=> x Hx.
  move/(_ x Hx) in Hhorner.
  clear - Hhorner Hy Hy0.
  rewrite !is_horner_mask in Hhorner *.
  set sub2 := Xsub _ _.
  set sub1 := Xsub _ _ in Hhorner.
  suff->: sub2 = Xdiv sub1 (Xreal y) by exact: I.div_correct.
  rewrite /sub1 Xsub_split Xdiv_split Xmul_Xadd_distr_r.
  rewrite /sub2 XmulC /=.
  rewrite {1}Xsub_split.
  congr Xadd.
  by rewrite Xdiv_split /= zeroF // XmulC.
  rewrite Xmul_Xneg_distr_l.
  congr Xneg.
  case E : (x - x0)%XR => [//|r /=].
  rewrite MapX.tsize_polymap.
  set lhs := @bigop _ _ _ _ _.
  have->: lhs = \big[Xadd/Xreal 0]_(i < PolR.tsize q)
  (Xmul (Xmul (PolR.tnth q i)
  (FullXR.tpow tt (Xreal r) i)) (Xinv (Xreal y))).
    apply: eq_bigr.
      move=> i _; rewrite MapX.tnth_polymap.
      rewrite !Xdiv_split /= zeroF //.
      by rewrite -!XmulA; congr Xmul; rewrite XmulC.
    by case: i.
  rewrite /= zeroF //.
by rewrite big_Xmul_Xadd_distr.
*)
Qed.

Lemma TM_div_mixed_r_nan1 M b f X0 X:
  not_empty (I.convert X0) ->
  contains (I.convert b) Xnan ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  let pol := approx (TM_div_mixed_r M b) in
  forall k : nat, k < Pol.size pol ->
  I.convert (Pol.nth pol k) = IInan.
Proof.
case=>[t Ht].
move/contains_Xnan => Ha /=.
case=>[Hnan Hsubst Hmain].
admit. (* FIXME
rewrite MapI.size_polymap.
move=> k Hk.
rewrite MapI.nth_polymap //.

have [q [Hq1 Hq2 Hq3]] := Hmain _ Ht.
exact: Idiv_Inan_propagate_r (Hq2 _ Hk) _.
*)
Qed.

Lemma TM_div_mixed_r_nan2 M b f X0 X:
  contains (I.convert b) Xnan ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  I.convert (error (TM_div_mixed_r M b)) = IInan.
Proof.
move/contains_Xnan => Ha /=.
case=>[Hnan Hsubst Hmain].
exact: Idiv_Inan_propagate_r Hnan _.
Qed.

Corollary TM_div_mixed_r_correct_strong M b X0 X f g :
  not_empty (I.convert X0) ->
  i_validTM (I.convert X0) (I.convert X) M f ->
  is_const g X b ->
  i_validTM (I.convert X0) (I.convert X) (TM_div_mixed_r M b)
  (fun x => Xdiv (f x) (g x)).
Proof.
move=> tHt Hf [[|y] Hy1 Hy2]; move: (Hf) => [Hnan Hsubset Hmain].
- split=>//.
  by rewrite (TM_div_mixed_r_nan2 Hy1 Hf).
  move=> /= x0 Hx0.
  admit. admit.
(*
  have [q [Hq1 Hq2 Hq3]] := Hmain _ Hx0.
  exists (MapX.tpolymap (Xdiv^~Xnan) q).
  split.
  + by rewrite MapX.tsize_polymap MapI.tsize_polymap.
  + move=> k Hk.
    by rewrite (TM_div_mixed_r_nan1 tHt Hy1 Hf).
  + move=> x Hx.
    by rewrite (TM_div_mixed_r_nan2 Hy1 Hf).
apply: (@TM_fun_eq_real _ _ _ _ _ _ (TM_div_mixed_r_correct Hy1 Hf)).
move=> x Hx.
by rewrite Hy2.
*)
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

Lemma TM_mul_correct_gen (smallX0: interval) (X0 X: I.type) (TMf TMg: rpa) f g :
  I.subset_ smallX0 (I.convert X0) ->
  I.subset_ (I.convert X0) (I.convert X) ->
  not_empty smallX0 ->
  let n := Pol.size (approx TMf) in
  n = Pol.size (approx TMg)-> 0 < n ->
  i_validTM smallX0 (I.convert X) TMf f ->
  i_validTM smallX0 (I.convert X) TMg g ->
  i_validTM smallX0 (I.convert X) (TM_mul TMf TMg X0 X n.-1)
  (fun xr => Xmul (f xr) (g xr)).
Proof.
move=> HinX0 HinX /not_empty'E [t Ht] n Heq npos
        [Hef H0 Hf] [Heg _ Hg].
have Hint : contains (I.convert X0) t by apply: (subset_contains smallX0).
  admit.
(*
case: (Hf t Ht) => [Af [Af1 Af2 Af3]].
case: (Hg t Ht) => [Ag [Ag1 Ag2 Ag3]].
split=>//.
  have H00: (Xreal 0)=(Xreal 0 + Xreal 0) by rewrite /= Rplus_0_l.
  rewrite H00; apply: I.add_correct.
    apply: (@mul_0_contains_0_r _
      (PolR.horner tt (PolR.tmul_tail tt n.-1 Af Ag) (t - t))); last first.
      apply: pow_contains_0 =>//.
      exact: subset_sub_contains_0 Hint _.
    set ip := tmul_tail _ _ _.
    set rp := PolR.tmul_tail _ _ _.
    rewrite Xsub_split Xadd_Xneg.
    apply: Bnd.ComputeBound_correct; first split.
    - by rewrite PolR.tsize_mul_tail tsize_mul_tail Af1 Ag1.
    - move=> k Hk; apply:Link.link_tmul_tail=>//.
      by rewrite /ip tsize_mul_tail in Hk.
    case Heqt: t Ht=> [|r] H.
      case HX0: (I.convert X0)=> [|l u].
        - rewrite (@Isub_Inan_propagate_l _ Xnan) //.
            by rewrite HX0.
          rewrite HX0 /= in HinX.
          by case: (I.convert X) HinX.
      by rewrite Heqt HX0 /= in Hint.
    apply: (@subset_sub_contains_0 _ (Xreal r)) =>//.
    by rewrite Heqt in Hint.
  rewrite H00; apply: I.add_correct.
    apply: (@mul_0_contains_0_l _ (PolR.horner tt Ag (t - t))) =>//.
    apply: Bnd.ComputeBound_correct =>//.
    apply: I.sub_correct =>//.
    exact: (subset_contains (I.convert X0)).
  rewrite H00; apply: I.add_correct.
    apply: (@mul_0_contains_0_l _ (PolR.horner tt Af (t - t))) =>//.
    apply: Bnd.ComputeBound_correct =>//.
    apply: I.sub_correct =>//.
    exact: (subset_contains (I.convert X0)).
  exact: (@mul_0_contains_0_l _ (Xreal 0)).
move=> N x0 Hx0 {Af} {Af1} {Af2} {Af3} {Ag} {Ag1} {Ag2} {Ag3}.
case: (Hf x0 Hx0) => [pf [Hf1 Hf2 Hf3]].
case: (Hg x0 Hx0) => [pg [Hg1 Hg2 Hg3]].
exists (PolR.tmul_trunc tt n.-1 pf pg).
split; first by rewrite PolR.tsize_mul_trunc /N /= tsize_mul_trunc.
  by move=> k Hkn; apply: Link.link_tmul_trunc;
   rewrite /N tsize_mul_trunc in Hkn =>//;
   rewrite -?Heq -/n prednK.
move=> x Hx /=.
move:(Hg3 x Hx) (Hf3 x Hx)=> {Hf3} {Hg3} Hg3 Hf3.
rewrite /mul_error.
suff->: (Xmul (f x) (g x) -
  PolR.horner tt (PolR.tmul_trunc tt n.-1 pf pg) (x - x0))
  = (PolR.horner tt (PolR.tmul_tail tt n.-1 pf pg) (x-x0) * (x-x0)^n.-1.+1 +
  ((f x - PolR.horner tt pf (x - x0)) * (PolR.horner tt pg (x - x0)) +
  ((g x - PolR.horner tt pg (x - x0)) * (PolR.horner tt pf (x - x0)) +
  (f x - PolR.horner tt pf (x - x0)) * (g x - PolR.horner tt pg (x - x0)))))%XR.
  apply: I.add_correct.
    apply: I.mul_correct.
      apply: Bnd.ComputeBound_correct =>//; first split.
      - by rewrite tsize_mul_tail PolR.tsize_mul_tail Hf1 Hg1.
      - move=> k Hk; apply: Link.link_tmul_tail => //.
        by rewrite tsize_mul_tail in Hk.
      by apply: I.sub_correct =>//; apply: (subset_contains smallX0).
    apply: I.power_int_correct.
    by apply: I.sub_correct=> //; apply: (subset_contains smallX0).
  apply: I.add_correct.
    apply: I.mul_correct =>//.
    apply: Bnd.ComputeBound_correct =>//.
    by apply: I.sub_correct =>//; apply: (subset_contains smallX0).
  apply: I.add_correct.
    apply: I.mul_correct =>//.
    apply: Bnd.ComputeBound_correct =>//.
    by apply: I.sub_correct =>//; apply: (subset_contains smallX0).
  exact: I.mul_correct.
clear Hf Hf2 Hf3 Hg Hg2 Hg3.
set sf := PolR.horner tt pf (x - x0).
set sg := PolR.horner tt pg (x - x0).
(****************)
case cxx0 : (x - x0)%XR => [|rxx0] /=.
  rewrite [(_ * Xnan)%XR]Xmul_comm /=.
  by rewrite horner_in_nan Xsub_split Xadd_comm.
case cn : n => [|n'] /=.
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
Qed.

Lemma TM_mul_correct (X0 X : I.type) (TMf TMg : rpa) f g n :
  not_empty (I.convert X0) ->
  n = Pol.size (approx TMf) ->
  n = Pol.size (approx TMg) -> 0 < n ->
  i_validTM (I.convert X0) (I.convert X) TMf f ->
  i_validTM (I.convert X0) (I.convert X) TMg g ->
  i_validTM (I.convert X0) (I.convert X) (TM_mul TMf TMg X0 X n.-1)
  (fun xr => Xmul (f xr) (g xr)).
Proof.
move=> Ht H1 H2 Hpos [Hef H0 Hf] Hg.
rewrite H1.
apply: TM_mul_correct_gen => //.
exact: subset_refl.
by rewrite -H1 H2.
by rewrite -H1.
Qed.

Definition poly_horner_tm n p (Mf : rpa) (X0 X : I.type) : rpa :=
  @Pol.fold rpa
  (fun a b => (TM_add (TM_cst a X0 X n) (TM_mul b Mf X0 X n)))
  (TM_cst I.zero X0 X n) p.

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
  by rewrite Pol.fold_polyNil /TM_cst Pol.size_rec1.
by rewrite Pol.fold_polyCons size_TM_add /TM_cst Pol.size_rec1 size_TM_mul maxnn.
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
admit. (* size *)
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
apply: (TM_fun_eq (f :=
  fun xr => Xmul (f xr) (Xinv (g xr)))).
  by move=> x; rewrite Xdiv_split.
rewrite /TM_div.
apply: TM_mul_correct =>//; first by rewrite size_poly_horner_tm (prednK Hnpos).
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
