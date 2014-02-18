(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

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
Require Import Rstruct.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop ssralg.
Require Import xreal_ssr_compat.
Require Import poly_datatypes.
Require Import interval_compl.
Require Import taylor_poly.
Require Import coeff_inst.
Require Import rpa_inst.
Require Import derive_compl.
Require Import taylor_model_int_sharp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type FloatIntervalOps (F : FloatOps with Definition even_radix := true)
  <: IntervalOps.
  Include FloatIntervalFull F.
End FloatIntervalOps.

Module RigPolyApproxFloat (F : FloatOps with Definition even_radix := true)
  (P : FloatPolyOps F) (I : FloatIntervalOps F).
Module Fl := MaskBaseF F.
Include RigPolyApprox I Fl P.
End RigPolyApproxFloat.

Module PolyMap (A : BaseOps) (PolA : PolyOps A) (B : BaseOps) (PolB : PolyOps B).

Definition tpolymap (f : A.T -> B.T) : PolA.T -> PolB.T :=
  @PolA.tfold _ (fun x (*acc*) => PolB.tpolyCons (f x) (*acc*)) PolB.tpolyNil.

Lemma tsize_polymap (f : A.T -> B.T) (p : PolA.T) :
  PolB.tsize (tpolymap f p) = PolA.tsize p.
Proof.
elim/PolA.tpoly_ind: p; first rewrite /tpolymap.
  by rewrite PolA.tsize_polyNil PolA.tfold_polyNil PolB.tsize_polyNil.
move=> a p IH; rewrite /tpolymap.
by rewrite PolA.tfold_polyCons PolB.tsize_polyCons PolA.tsize_polyCons IH.
Qed.

Lemma tnth_polymap (f : A.T -> B.T) (i : nat) (p : PolA.T) :
  i < PolA.tsize p -> PolB.tnth (tpolymap f p) i = f (PolA.tnth p i).
Proof.
elim/PolA.tpoly_ind: p i =>[|a p IH i H]; first by rewrite PolA.tsize_polyNil.
rewrite PolA.tnth_polyCons; last by rewrite PolA.tsize_polyCons ltnS in H.
rewrite /tpolymap PolA.tfold_polyCons PolB.tnth_polyCons; last first.
  by rewrite tsize_polymap; rewrite PolA.tsize_polyCons ltnS in H.
case: i IH H =>[//|i IH H]; rewrite IH //.
by rewrite PolA.tsize_polyCons ltnS in H.
Qed.

Definition tpolymap_polyCons (f : A.T -> B.T) a p :
  tpolymap f (PolA.tpolyCons a p) =
  PolB.tpolyCons (f a) (tpolymap f p).
Proof @PolA.tfold_polyCons _ _ _ _ _.

Definition tpolymap_polyNil (f : A.T -> B.T) :
  tpolymap f PolA.tpolyNil = PolB.tpolyNil.
Proof @PolA.tfold_polyNil _ _ _.

End PolyMap.

Module TaylorModelFloat (F : FloatOps with Definition even_radix := true)
  (PolF : FloatPolyOps F)
  (I : FloatIntervalOps F)
  (Import Pol : IntMonomPolyOps I)
  (PolX : ExactMonomPolyOps FullXR)
  (Link : LinkIntX I Pol PolX).
Module Import TM := TaylorModel I Pol PolX Link.
Module RPAF := RigPolyApproxFloat F PolF I.

Notation f_type := F.type.
Notation f_poly := PolF.T.
Notation f_rpa := RPAF.rpa.
Notation f_RPA := RPAF.RPA.
Notation f_error := RPAF.error.
Notation f_approx := RPAF.approx.

Notation i_type := I.type.
Notation i_poly := Pol.T.
Notation i_rpa := TM.RPA.rpa.
Notation i_RPA := TM.RPA.RPA.
Notation i_error := TM.RPA.error.
Notation i_approx := TM.RPA.approx.

Notation x_type := ExtendedR.
Notation x_poly := PolX.T.

Notation i_prec := I.precision.
Notation i_eval := Pol.teval.
Notation x_eval := (PolX.teval tt).
(* Erik: [Pol.teval]/[PolX.teval] may take 1 more argument *)

Definition i2f_mid : i_type -> f_type := I.midpoint.

Lemma i2f_mid_correct (xi : i_type) :
  (exists x : x_type, contains (I.convert xi) x) ->
  I.convert_bound (i2f_mid xi) =
  Xreal (proj_val (I.convert_bound (I.midpoint xi))) /\
  contains (I.convert xi) (I.convert_bound (I.midpoint xi)).
Proof (I.midpoint_correct xi).

Definition f2i : f_type -> i_type := fun x => I.bnd x x.

Module MapI := PolyMap Pol.Int Pol Pol.Int Pol.
Module MapIF := PolyMap Pol.Int Pol PolF.Fl PolF.
Module MapFX := PolyMap PolF.Fl PolF FullXR PolX.

Notation i_poly_map := MapI.tpolymap.

Definition i2f_poly : i_poly -> f_poly := MapIF.tpolymap i2f_mid.

Definition i2f_rem (pr : i_prec) : i_poly -> i_poly :=
  i_poly_map (fun x => I.sub pr x (f2i (i2f_mid x))).

Notation f2x := I.convert_bound.

Definition f2x_poly : f_poly -> x_poly := MapFX.tpolymap f2x.

Notation i2ix := I.convert.

Notation subset_ := Interval_interval.subset.

Definition f_validTM
  (X0 X : interval) (M0 : f_rpa) (f : ExtendedR -> ExtendedR) :=
  [/\ contains (i2ix (f_error M0)) (Xreal 0),
    subset_ X0 X &
    forall xi0 x : ExtendedR, contains X0 xi0 -> contains X x ->
    contains (i2ix (f_error M0))
    (Xsub (f x) (x_eval (f2x_poly (f_approx M0)) (Xsub x xi0)))].

Definition i2f_tm (pr : i_prec) (X0 X : i_type) (M : i_rpa) : f_rpa :=
  f_RPA
  (i2f_poly (i_approx M))
  (I.add pr (i_error M) (i_eval pr (i2f_rem pr (i_approx M)) (I.sub pr X X0))).

(* Erik: (X - X0) could be handled by [i_eval] in order not to appear here *)

Lemma teval_contains_0 pr P (X : i_type) :
  (forall k, k < Pol.tsize P -> contains (I.convert(Pol.tnth P k)) (Xreal 0)) ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (i_eval pr P X)) (Xreal 0).
Proof.
move=> HP0 HX0.
elim/Pol.tpoly_ind: P HP0 => [|x P IHP] HP0.
  rewrite Pol.teval_polyNil; case: X HX0 =>//.
  by move=> *; apply Pol.Int.zero_correct.
rewrite Pol.teval_polyCons.
have->: Xreal 0 = Xadd (Xreal 0) (Xreal 0) by rewrite Xadd_0_r.
apply: I.add_correct.
  have->: Xreal 0 = Xmul (Xreal 0) (Xreal 0) by rewrite Xmul_0_r.
  apply: I.mul_correct =>//; apply IHP => k Hk.
  move: HP0; move/(_ k.+1); rewrite Pol.tsize_polyCons ltnS; move/(_ Hk).
  by rewrite Pol.tnth_polyCons.
move: HP0; move/(_ 0); rewrite Pol.tsize_polyCons; move/(_ erefl).
by rewrite Pol.tnth_polyCons.
Qed.

Lemma sub_midp_contains_0 pr (X : i_type) :
  (exists t : x_type, contains (I.convert X) t) ->
  contains (I.convert (I.sub pr X (f2i (i2f_mid X)))) (Xreal 0).
Proof.
move=> tHt; have [L1 L2] := i2f_mid_correct tHt; have [t Ht] := tHt.
set t' := f2x (i2f_mid X).
apply (@subset_sub_contains_0 pr t' (f2i (i2f_mid X)) X).
  rewrite /t' /I.convert /I.bnd I.bnd_correct /I.convert_bound -/f2x {3}L1 /=.
  by case: (f2x (i2f_mid X)); intuition.
rewrite /I.convert /I.bnd I.bnd_correct -/f2x L1 /= -/i2ix.
by case E: (i2ix X) =>[//|l u]; apply: contains_le; rewrite -E -L1; apply: L2.
Qed.

Lemma Xsub_Xnan_r (a : ExtendedR) : Xsub a Xnan = Xnan.
Proof. by case: a. Qed.

Lemma Xsub_diag_eq (x : ExtendedR) : Xsub x x = Xmask (Xreal 0) x.
Proof. by case: x=>[//|r /=]; rewrite Rminus_diag_eq. Qed.

Lemma Imask_mask (x y : i_type) : I.mask (I.mask x y) y = I.mask x y.
Proof. by case: y. Qed.

Lemma contains_bnd2 (fx : f_type) :
  f2x fx <> Xnan ->
  contains (I.convert (I.bnd fx fx)) (f2x fx).
Proof.
case E : (f2x fx) =>[//|r] _.
rewrite /= -/f2x [f2x _]E.
by auto with real.
Qed.

Lemma i2f_mid_nan (x : i_type) :
  (exists t : ExtendedR, contains (i2ix x) t) ->
  f2x (I.midpoint x) <> Xnan.
Proof.
move=> Hx.
have [H1 H2] := I.midpoint_correct _ Hx.
by rewrite [f2x _]H1.
Qed.

Theorem i2f_tm_correct pr (X0 X : i_type) M f :
  (exists t, contains (I.convert X0) t) ->
  i_validTM (i2ix X0) (i2ix X) M f ->
  f_validTM (i2ix X0) (i2ix X) (i2f_tm pr X0 X M) f.
Proof.
move=> [t Ht] [Hzero Hsubset].
set N := Pol.tsize (i_approx M) => H.
have Hcut :
  contains (I.convert (i_eval pr (i2f_rem pr (i_approx M)) (I.sub pr X X0)))
  (Xreal 0).
  have L := @subset_sub_contains_0 pr t X0 X Ht Hsubset.
  apply: teval_contains_0 =>// k Hk; rewrite /i2f_rem.
  rewrite MapI.tnth_polymap; last by rewrite MapI.tsize_polymap in Hk.
  set xi := Pol.tnth (i_approx M) k.
  apply: sub_midp_contains_0.
  have {H} [a [_ Hpw _]] := (H t Ht).
  by exists (PolX.tnth a k); apply: Hpw; rewrite MapI.tsize_polymap in Hk.
red; split=>//.
  have->: Xreal 0 = Xadd (Xreal 0) (Xreal 0) by rewrite Xadd_0_r.
  exact: I.add_correct.
move=> xi0 x Hxi0 Hx.
have {H} [alpha [Hsize Hpw Hdelta]] := (H xi0 Hxi0).
move/(_ x Hx) in Hdelta.
set T'x := x_eval (f2x_poly (i2f_poly (i_approx M))) (Xsub x xi0).
pose Tx := x_eval alpha (Xsub x xi0).
case E: Tx =>[|r].
  rewrite /Tx in E; rewrite E /FullXR.tsub Xsub_Xnan_r in Hdelta.
  have Hnan := contains_Xnan Hdelta.
  by rewrite (Iadd_Inan_propagate_l pr Hcut Hnan).
have->: (f x - T'x = (f x - Tx) + (Tx - T'x))%XR.
  rewrite !Xsub_split.
  rewrite (Xadd_assoc (f x)) -(Xadd_assoc _ Tx) (Xadd_comm _ Tx) Xadd_Xneg.
  suff->: Xmask (Xreal 0) Tx = Xreal 0; by [rewrite Xadd_0_l | rewrite E ].
apply: I.add_correct =>//; rewrite /Tx /T'x.
elim/tpoly_ind: (i_approx M) alpha {Hdelta Tx T'x E} @N Hsize Hpw.
  move=> alpha N Hsize Hpw.
  rewrite [alpha]tpolyNil_size0; last by rewrite Hsize /N tsize_polyNil.
  rewrite /i2f_poly !MapIF.tpolymap_polyNil.
  rewrite /f2x_poly !MapFX.tpolymap_polyNil.
  rewrite /i2f_rem !MapI.tpolymap_polyNil.
  rewrite Xsub_diag_eq !(teval_polyNil,PolX.teval_polyNil).
  apply: I.mask_correct; first exact: Int.zero_correct.
  change I.I.convert with I.convert.
  case: x Hx =>[|x] Hx; case: xi0 Hxi0 =>[|y] Hxi0 /=;
    (try have Hx' := contains_Xnan Hx); try have Hxi0' := contains_Xnan Hxi0.
  - by rewrite (Isub_Inan_propagate_l pr (y:=Xnan) _ Hx').
  - by rewrite (Isub_Inan_propagate_l pr (y:=Xreal y) _ Hx').
  - by rewrite (Isub_Inan_propagate_r pr (y:=Xreal x) _ Hxi0').
  - by apply: (subset_sub_contains_0 pr (x0:=Xreal y) _ Hsubset).
move=> p0 p IH alpha N Hsize Hpw.
elim/PolX.tpoly_ind: alpha @N Hsize Hpw.
  by rewrite tsize_polyCons PolX.tsize_polyNil.
move=> a0 alpha _ N Hsize Hpw.
rewrite /i2f_rem !(MapI.tpolymap_polyCons,MapIF.tpolymap_polyCons).
have Hsize' : PolX.tsize alpha = tsize p.
  by rewrite PolX.tsize_polyCons /N tsize_polyCons in Hsize; case: Hsize.
rewrite /i2f_poly !MapIF.tpolymap_polyCons.
rewrite /f2x_poly !MapFX.tpolymap_polyCons.
rewrite !teval_polyCons !PolX.teval_polyCons.
rewrite /Int.tadd /Int.tmul /FullXR.tadd /FullXR.tmul.
set t1 := (Xmul (x_eval _ _) _).
set t2 := (Xmul _ _).
set t3 := f2x _.
have->: ((t1 + a0) - (t2 + t3) = t1 - t2 + (a0 - t3))%XR.
  rewrite Xsub_Xadd_distr !Xsub_split; rewrite !Xadd_assoc; congr Xadd.
  by rewrite -!Xadd_assoc [Xadd a0 _]Xadd_comm.
apply: I.add_correct; last first.
  apply: I.sub_correct.
    move/(_ 0) in Hpw; rewrite tnth_polyCons // PolX.tnth_polyCons // in Hpw.
    by rewrite /N tsize_polyCons in Hpw; move/(_ erefl) in Hpw.
  rewrite /t3 /f2x /f2i /i2f_mid.
  apply: contains_bnd2; apply: i2f_mid_nan.
  exists a0.
  move/(_ 0): Hpw; rewrite /N tsize_polyCons; move/(_ erefl).
  by rewrite tnth_polyCons // PolX.tnth_polyCons.
rewrite Xsub_split -Xmul_Xneg_distr_l -Xmul_Xadd_distr_r.
apply: I.mul_correct; last exact: I.sub_correct.
rewrite -Xsub_split; apply: IH =>//.
move=> k Hk; move/(_ k.+1): Hpw.
rewrite tnth_polyCons // PolX.tnth_polyCons; last by rewrite Hsize'.
by rewrite /N tsize_polyCons ltnS; move/(_ Hk).
Qed.

End TaylorModelFloat.
