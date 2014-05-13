Require Import ZArith Psatz.
Require Import Fcore_Raux.
Require Import Interval_xreal.
Require Import Interval_generic Interval_interval.
Require Import Interval_definitions.
Require Import Interval_specific_ops.
Require Import Interval_float_sig.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Interval_xreal.
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

(** The interface *)

Module Type PolyBound
  (I : IntervalOps)
  (Import Pol : IntMonomPolyOps I)
  (PolX : ExactMonomPolyOps FullXR)
  (Link : LinkIntX I Pol PolX).

Parameter ComputeBound : forall (u : Pol.U) (p : Pol.T) (X : I.type), I.type.

Parameter ComputeBound_correct : forall u p px X,
  Link.contains_pointwise p px ->
  forall x, contains (I.convert X) x ->
  contains (I.convert (ComputeBound u p X)) (PolX.teval tt px x).

(* TODO: Rely on [Link.contains_pointwise] or so *)
Parameter ComputeBound_nth0 : forall prec p pr X,
  PolX.tsize pr = tsize p ->
  (forall i, i < tsize p -> contains (I.convert (tnth p i)) (PolX.tnth pr i)) ->
  contains (I.convert X) (Xreal 0) ->
  I.subset_ (I.convert (tnth p 0)) (I.convert (ComputeBound prec p X)).

End PolyBound.

(** The implementations *)

Module PolyBoundHorner
  (I : IntervalOps)
  (Import Pol : IntMonomPolyOps I)
  (PolX : ExactMonomPolyOps FullXR)
  (Link : LinkIntX I Pol PolX)
  <: PolyBound I Pol PolX Link.

Module Import Aux := IntervalAux I.

Definition ComputeBound : Pol.U -> Pol.T -> I.type -> I.type :=
  Pol.teval.

Theorem ComputeBound_correct u fi fx X :
  Link.contains_pointwise fi fx ->
  forall x, contains (I.convert X) x ->
  contains (I.convert (ComputeBound u fi X)) (PolX.teval tt fx x).
Proof.
move=> Hfifx x Hx; rewrite /ComputeBound.
elim/PolX.tpoly_ind: fx fi Hfifx => [|a b IH]; elim/tpoly_ind.
- rewrite PolX.teval_polyNil teval_polyNil.
  by move=> *; apply: I.mask_correct =>//; exact: Int.zero_correct.
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

Lemma ComputeBound_nth0 prec p pr X :
  PolX.tsize pr = tsize p ->
  (forall i, i < tsize p -> contains (I.convert (tnth p i)) (PolX.tnth pr i)) ->
  contains (I.convert X) (Xreal 0) ->
  I.subset_ (I.convert (tnth p 0)) (I.convert (ComputeBound prec p X)).
Proof.
rewrite /ComputeBound.
move=> Hsize Hnth HX.
elim/tpoly_ind: p pr Hsize Hnth =>[|a p IHp] pr Hsize Hnth.
  rewrite teval_polyNil tnth_polyNil.
  apply: contains_subset.
    exists (Xreal 0).
    by apply: I.fromZ_correct.
  have := I.mask_correct (I.fromZ 0) X _ (Xreal 0) _ HX; exact.
elim/PolX.tpoly_ind: pr Hsize Hnth =>[|ar pr IHpr] Hsize Hnth.
  by exfalso; rewrite tsize_polyCons PolX.tsize_polyNil in Hsize.
rewrite tnth_polyCons // teval_polyCons //.
have H1 : contains (I.convert (Int.tmul prec (ComputeBound prec p X) X)) (Xreal 0).
  apply: (@mul_0_contains_0_r prec (PolX.teval tt pr (Xreal 0))) =>//.
  apply: ComputeBound_correct =>//.
  rewrite tsize_polyCons PolX.tsize_polyCons in Hsize.
  split; first by case: Hsize.
  move=> i Hi; move/(_ i.+1) in Hnth.
  rewrite tnth_polyCons // PolX.tnth_polyCons in Hnth => //.
    apply: Hnth.
    by rewrite tsize_polyCons /leq subSS.
  by case: Hsize =>->.
apply: Iadd_zero_subset_l => //.
exists ar.
move/(_ 0) in Hnth.
rewrite tsize_polyCons tnth_polyCons // PolX.tnth_polyCons // in Hnth.
exact: Hnth.
Qed.

End PolyBoundHorner.
