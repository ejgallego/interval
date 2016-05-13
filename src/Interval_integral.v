(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2015-2016, Inria

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

Require Import Reals List.
Require Import Coquelicot.Coquelicot.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrbool.
Require Import Interval_xreal.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_missing.
Require Import coquelicot_compl.
Require Import Interval_taylor_model.

Require Import interval_compl.

Module IntegralTactic (F : FloatOps with Definition even_radix := true) (I : IntervalOps with Definition bound_type := F.type with Definition precision := F.precision with Definition convert_bound := F.toX).

Module J := IntervalExt I.
Module F' := FloatExt F.

Local Notation toR x := (proj_val (F.toX x)).

Lemma F_realP (fl : F.type) :
 reflect (F.toX fl = Xreal (toR fl)) (F.real fl).
Proof.
have := F.real_correct fl.
rewrite <- F.toF_correct.
by case: (F.toF fl)=> [||y z t] ->; constructor.
Qed.

Lemma contains_convert_bnd_l (a b : F.type) : F.real a ->
  toR a <= toR b -> contains (I.convert (I.bnd a b)) (F.toX a).
Proof.
rewrite F.real_correct I.bnd_correct /= /I.convert_bound.
case: F.toX => //= r _ H.
split.
apply Rle_refl.
now destruct F.toX.
Qed.

Lemma contains_convert_bnd (a b : F.type) r :  F.real a -> F.real b ->
  toR a <= r <= toR b -> contains (I.convert (I.bnd a b)) (Xreal r).
Proof.
rewrite 2!F.real_correct I.bnd_correct /= /I.convert_bound.
case: F.toX => //= ra _.
by case: F.toX.
Qed.

(* Remember : toR = fun x : F.type => proj_val (FtoX (F.toF x)) *)
(* The statement of I.midpoint_correct is really clumsy *)
(* contains_le is also difficult to use... *)
(* I.midpoint_correct should be stated using toR *)
(* le_lower should either be a notation over le_upper or a new def *)
(* so that it simplifies to <= or else provide suitable lemmas *)
Lemma midpoint_bnd_in (a b : F.type) :
  F.real a -> F.real b -> toR a <= toR b ->
  toR a <= toR (I.midpoint (I.bnd a b)) <= toR b.
Proof.
intros Ha Hb Hab.
have non_empty_iab : exists x : ExtendedR, contains (I.convert (I.bnd a b)) x.
  by exists (F.toX a); apply: contains_convert_bnd_l.
generalize (I.midpoint_correct (I.bnd a b) non_empty_iab).
unfold I.convert_bound.
set m := F.toX _.
move => [->].
rewrite I.bnd_correct /= /I.convert_bound.
move/F_realP: Ha => ->.
by move/F_realP: Hb => ->.
Qed.

Definition thin (f : F.type) : I.type :=
  if F.real f then I.bnd f f else I.nai.

Lemma thin_correct (fl : F.type) :
 contains (I.convert (thin fl)) (F.toX fl).
Proof.
rewrite /thin F.real_correct /I.convert_bound.
case ex: (F.toX fl) => [|r] /=.
by rewrite I.nai_correct.
rewrite I.bnd_correct /I.convert_bound ex.
split; exact: Rle_refl.
Qed.

Lemma thin_correct_toR (fl : F.type) :
  contains (I.convert (thin fl)) (Xreal (toR fl)).
Proof.
  case Hrealfl : (F.real fl);move: Hrealfl; move/F_realP => Hrealfl.
  * rewrite -Hrealfl.
      by apply: (thin_correct fl).
  * move/F_realP: Hrealfl; rewrite /thin.
    move /negbTE => ->.
    by rewrite I.nai_correct.
Qed.

Section IntervalIntegral.

(* A fixed precision *)
Variable prec : F.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Definition integralEstimatorCorrect (estimator : I.type -> I.type -> I.type) :=
  forall ia ib a b,
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains (I.convert (estimator ia ib)) (Xreal (RInt f a b)).

Section Functions.

Variable est : I.type -> I.type -> I.type.

Definition diam x := F.sub Interval_definitions.rnd_UP prec (I.upper x) (I.lower x).

Definition div2 f := F.scale2 f (F.ZtoS (-1)).

Fixpoint integral_interval_absolute (depth : nat) (ia ib : I.type) (epsilon : F.type) :=
  let int := I.join ia ib in
  match depth with
    | O => let m := I.midpoint' int in
           I.add prec (est ia m) (est m ib)
    | S n => let m := I.midpoint' int in
             let halfeps := div2 epsilon in
             let roughEstimate_1 := est ia m in
             let roughEstimate_2 := est m ib in
             match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
               | true,true => I.add prec roughEstimate_1 roughEstimate_2
               | true,false => let int2 := integral_interval_absolute n m ib (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
               | false,true => let int1 := integral_interval_absolute n ia m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
               | false,false =>
                 let i1 := integral_interval_absolute n ia m halfeps in
                 let i2 := integral_interval_absolute n m ib halfeps in
                 I.add prec i1 i2
             end
  end.

Definition integral_interval_relative
    (depth : nat) (ia ib : I.type) (epsilon : F.type) :=
  if I.bounded ia && I.bounded ib then
    let roughEst := est ia ib in
    if depth is O then roughEst
    else
      let epsilon :=
        if I.bounded roughEst then
          F.mul Interval_definitions.rnd_UP prec epsilon
            (I.upper (I.abs roughEst))
        else epsilon in
      if F'.le (diam roughEst) epsilon then roughEst
      else integral_interval_absolute (depth-1) ia ib epsilon
  else I.nai.

Lemma integral_interval_absolute_Sn n a b epsilon :
  let int := I.join a b in
  let m := I.midpoint' int in
  let halfeps := div2 epsilon in
  let roughEstimate_1 := est a m in
  let roughEstimate_2 := est m b in
  integral_interval_absolute (S n) a b epsilon =
  match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
    | true,true => I.add prec roughEstimate_1 roughEstimate_2
    | true,false => let int2 := integral_interval_absolute n m b (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
    | false,true => let int1 := integral_interval_absolute n a m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
    | false,false =>
      let i1 := integral_interval_absolute n a m halfeps in
      let i2 := integral_interval_absolute n m b halfeps in
      I.add prec i1 i2
  end.
Proof.
by [].
Qed.

Definition naive_integral (ia ib : I.type) :=
  I.mul prec (I.sub prec ib ia) (iF (I.join ia ib)).

End Functions.

Section Proofs.

Variable estimator : I.type -> I.type -> I.type.

Hypothesis Hcorrect : integralEstimatorCorrect estimator.

Definition ex_RInt_base_case :=
  forall a b ia ib,
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  I.convert (estimator ia ib) <> IInan ->
  ex_RInt f a b.

Lemma integral_interval_absolute_ex_RInt (depth : nat) ia ib a b epsilon :
  ex_RInt_base_case ->
  I.bounded ia ->
  I.bounded ib ->
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  I.convert (integral_interval_absolute estimator depth ia ib epsilon) <> IInan ->
  ex_RInt f a b.
Proof.
move => ex_RInt_base_case Hboundia Hboundib Hia Hib HnotInan.
elim: depth epsilon a b ia ib HnotInan Hboundia Hboundib Hia Hib =>
[|d Hd] epsilon a b ia ib HnotInan Hboundia Hboundib Hia Hib.
- set iab := (I.join ia ib).
  set m' := I.midpoint' iab.
  have Hm'm :  (not_empty (I.convert m')).
  move: (I.midpoint'_correct iab) => [H1 H2].
    by apply: H2; exists a; apply: I.join_correct; left.
  elim: Hm'm => m Hm.
  apply: (ex_RInt_Chasles _ _ m).
  + apply: (ex_RInt_base_case _ _ ia m') => // .
    move: HnotInan; rewrite /integral_interval_absolute -/m'.
    set I1 := estimator ia m'.
    by case HI1 : (I.convert I1) => [| l1 u1 ]; first rewrite I.add_propagate_l.
  + apply: (ex_RInt_base_case _ _ m' ib) => // .
    move: HnotInan; rewrite /integral_interval_absolute -/m'.
    set I2 := estimator m' ib.
    by case HI2 : (I.convert I2) => [| l2 u2 ]; first rewrite I.add_propagate_r.
- set iab := (I.join ia ib).
  set m' := I.midpoint' iab.
  have Boundedm' : I.bounded m'. by admit. (* not true but we might want it to be true *)
  have Hm'm :  (not_empty (I.convert m')).
  move: (I.midpoint'_correct iab) => [H1 H2].
    by apply: H2; exists a; apply: I.join_correct; left.
  elim: Hm'm => m Hm.
  apply: (ex_RInt_Chasles _ _ m).
  + rewrite integral_interval_absolute_Sn in HnotInan.
    move: HnotInan.
    set b1 := (X in if X then _ else _).
    case: b1.
    * set b2 := (X in if X then _ else _).
      case Hb2 : b2 => HnotInan.
      apply: (ex_RInt_base_case _ _ ia m') => // .
      move: HnotInan.
      set I1 := estimator ia m'.
        by case HI1 : (I.convert I1) => [| l1 u1 ];
          first rewrite I.add_propagate_l.
     apply: (ex_RInt_base_case _ _ ia m') => // .
     move: HnotInan.
     set I1 := estimator ia m'.
       by case HI1 : (I.convert I1) => [| l1 u1 ];
         first rewrite I.add_propagate_l.
    * set b2 := (X in if X then _ else _).
      case Hb2 : b2 => HnotInan.
        - set epsilon1 := (F.sub_exact epsilon
                       (diam (estimator (I.midpoint' (I.join ia ib)) ib))).
        apply: (Hd epsilon1 a m ia m') => // .
        set i1 := (X in I.convert X).
        move: HnotInan; rewrite (* -/m' -/epsilon1 *) -/i1.
          by case HI1 : (I.convert i1) => [| l1 u1 ]; first rewrite I.add_propagate_l.
        - set epsilon1 := (div2 epsilon).
        apply: (Hd epsilon1 a m ia m') => // .
        set i1 := (X in I.convert X).
        move: HnotInan; rewrite (* -/m' -/epsilon1 *) -/i1.
          by case HI1 : (I.convert i1) => [| l1 u1 ]; first rewrite I.add_propagate_l.
  + rewrite integral_interval_absolute_Sn in HnotInan.
    move: HnotInan.
    set b1 := (X in if X then _ else _).
    case: b1.
    * set b2 := (X in if X then _ else _).
      case: b2 => HnotInan.
        apply: (ex_RInt_base_case _ _ m' ib) => // .
        move: HnotInan.
        set I1 := estimator m' ib.
        by case HI1 : (I.convert I1) => [| l1 u1 ];
                            first rewrite I.add_propagate_r.
        set epsilon1 := (F.sub_exact epsilon
                       (diam (estimator ia (I.midpoint' (I.join ia ib))))).
        apply: (Hd epsilon1 m b m' ib) => // .
        set i1 := (X in I.convert X).
        move: HnotInan; rewrite (* -/m' -/epsilon1 *) -/i1.
        by case HI1 : (I.convert i1) => [| l1 u1 ]; first rewrite I.add_propagate_r.
    * set b2 := (X in if X then _ else _).
      case: b2 => HnotInan.
      apply: (ex_RInt_base_case _ _ m' ib) => // .
      move: HnotInan.
      set I1 := estimator m' ib.
        by case HI1 : (I.convert I1) => [| l1 u1 ];
                            first rewrite I.add_propagate_r.
      set epsilon1 := div2 epsilon.
      apply: (Hd epsilon1 m b m' ib) => // .
        set i1 := (X in I.convert X).
        move: HnotInan; rewrite (* -/m' -/epsilon1 *) -/i1.
        by case HI1 : (I.convert i1) => [| l1 u1 ]; first rewrite I.add_propagate_r.
Admitted.

Lemma integral_interval_absolute_correct (depth : nat) (a b : R) (ia ib : I.type) epsilon :
  I.bounded ia ->
  I.bounded ib ->
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains (I.convert (integral_interval_absolute estimator depth ia ib epsilon)) (Xreal (RInt f a b)).
Proof.
move => Hiab Hibb Hcontia Hcontib HexRInt.
elim: depth epsilon a b ia ib Hcontia Hcontib Hiab Hibb HexRInt => [|d Hd] epsilon a b ia ib Hcontia Hcontib Hiab Hibb HexRInt.
- set iab := (I.join ia ib).
  set m' := I.midpoint' iab.
  have Boundedm' : I.bounded m' by admit.
  move: (I.midpoint'_correct iab) => [H1 H2].
  have Hm'm :  (not_empty (I.convert m')).
    by apply: H2; exists a; apply: I.join_correct; left.
  elim: Hm'm => m Hm.
    have hIl : ex_RInt f a m.
    apply:  (ex_RInt_Chasles_1 _ _ _ b) => // .
      by admit. (* not true, thinking about how to go around this *)

    (* rewrite /contains in Hm. *)
    have hIr : ex_RInt f m b.
    apply:  (ex_RInt_Chasles_2 f a)=> // .
      by admit. (* not true, idem *)
    have -> : RInt f a b =
            RInt f a m + RInt f m b.
      by rewrite RInt_Chasles // .
   by apply: J.add_correct; apply: Hcorrect.
- set iab := (I.join ia ib).
  set m' := I.midpoint' iab.
  have Boundedm' : I.bounded m' by admit. (* not true, see previous lemma *)
  move: (I.midpoint'_correct iab) => [H1 H2].
  have Hm'm :  (not_empty (I.convert m')).
    by apply: H2; exists a; apply: I.join_correct; left.
  elim: Hm'm => m Hm.
    have hIl : ex_RInt f a m.
    apply:  (ex_RInt_Chasles_1 _ _ _ b) => // .
      by admit. (* see above *)

    (* rewrite /contains in Hm. *)
    have hIr : ex_RInt f m b.
    apply:  (ex_RInt_Chasles_2 f a)=> // .
      by admit. (* see above *)
    have -> : RInt f a b =
            RInt f a m + RInt f m b.
      by rewrite RInt_Chasles // .
  rewrite integral_interval_absolute_Sn.
  set b1 := (X in if X then _ else _).
  case Hb1: b1.
  + set b2 := (X in if X then _ else _).
    case Hb2: b2.
    * by apply: J.add_correct; apply: Hcorrect.
    * apply: J.add_correct; first by apply: Hcorrect.
        apply: Hd => // .
  + set b2 := (X in if X then _ else _).
    case Hb2: b2.
    * apply: J.add_correct; first by apply: Hd.
        by apply: Hcorrect.
    * apply: J.add_correct; by apply: Hd.
Admitted.


Lemma integral_interval_relative_ex_RInt (depth : nat) a b ia ib epsilon :
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt_base_case ->
  I.convert (integral_interval_relative estimator depth ia ib epsilon) <> IInan ->
  ex_RInt f a b.
Proof.
move => Hcontia Hcontib ex_RInt_base_case HnotInan.
move: HnotInan.
rewrite /integral_interval_relative.
case Hiab: (I.bounded ia);
case Hibb: (I.bounded ib); rewrite ?I.nai_correct => //= .
case: depth => [|depth].
by apply: ex_RInt_base_case.
set b1 := (X in if X then _ else _).
case Hb1 : b1; first by apply: ex_RInt_base_case.
by apply: integral_interval_absolute_ex_RInt.
Qed.

Lemma integral_interval_relative_correct (depth : nat)  a b ia ib epsilon :
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains (I.convert (integral_interval_relative estimator depth ia ib epsilon)) (Xreal (RInt f a b)).
Proof.
move => Hcontia Hcontib Hex_RInt.
rewrite /integral_interval_relative.
case Hiab: (I.bounded ia);
case Hibb: (I.bounded ib); rewrite ?I.nai_correct => //= .
case: depth => [|depth].
  by apply: Hcorrect.
set b1 := (X in if X then _ else _).
case Hb1 : b1; first by apply: Hcorrect.
by apply: integral_interval_absolute_correct.
Qed.

Lemma naive_integral_correct (ia ib: I.type) (a b : R) :
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains (I.convert (naive_integral ia ib)) (Xreal (RInt f a b)).
Proof.
move => Hcont1 Hcont2 Hfint.
rewrite /naive_integral.
apply: J.contains_RInt => //.
intros x Hx.
apply: HiFIntExt.
apply: contains_connected Hx; apply: I.join_correct.
now apply Rmin_case ; [left|right].
now apply Rmax_case ; [left|right].
Qed.

Lemma toX_toF_Freal a : F.toX a <> Xnan -> F.real a.
Proof.
move: (F.real_correct a).
rewrite -F.toF_correct.
by case: (F.toF a).
Qed.

Lemma integral_epsilon_correct (depth : nat) (a b : R) (ia ib : I.type) epsilon :
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  ex_RInt f a b ->
  contains
    (I.convert (integral_interval_relative estimator depth ia ib epsilon))
    (Xreal (RInt f a b)).
Proof.
move => Hconta Hcontb HFInt.
by apply: integral_interval_relative_correct.
Qed.

End Proofs.

End IntervalIntegral.

End IntegralTactic.

Module IntegralTaylor (I : IntervalOps).

Module J := IntervalExt I.
Module TM := TM I.

Section DepthZeroPol.

(* A fixed precision *)
Variable prec : I.precision.

Variables (f : R -> R) (iF : I.type -> I.type).

Hypothesis HiFIntExt : forall xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (iF xi)) (Xreal (f x)).

Variable Mf : TM.TMI.rpa.
Variables X : I.type.
Definition X0 := I.bnd (I.midpoint X) (I.midpoint X).
Definition iX := I.convert X.
Definition iX0 := I.convert X0.

Hypothesis validMf : TM.TMI.i_validTM iX0 iX Mf (fun x => Xreal (f x)).

Variables (a b : R).

(* f is integrable on [a, b]*)
Hypothesis Hintegrable : ex_RInt f a b.

Variables ia ib : I.type.

Hypothesis Hconta : contains (I.convert ia) (Xreal a).
Hypothesis Hcontb : contains (I.convert ib) (Xreal b).
Hypothesis Hcontxa : contains iX (Xreal a).
Hypothesis Hcontxb : contains iX (Xreal b).

Definition taylor_integral :=
  TM.TMI.integralEnclosure prec X0 Mf ia ib.

(* now we take the intersection of a naive and intelligent way of computing the integral *)
Definition taylor_integral_naive_intersection :=
  let temp := I.mul prec (I.sub prec ib ia) (iF (I.join ia ib)) in
  if I.subset I.nai temp then I.nai
  else I.meet temp taylor_integral.

Lemma taylor_integral_correct :
  contains
    (I.convert taylor_integral)
    (Xreal (RInt f a b)).
Proof.
rewrite /taylor_integral.
apply: (@TM.TMI.integralEnclosure_correct prec X0 X (fun x => Xreal (f x)) Mf (proj_val (I.convert_bound (I.midpoint X)))) => //.
rewrite /X0 I.bnd_correct (proj1 (I.midpoint_correct X _)).
split ; apply Rle_refl.
eexists.
exact: Hcontxa.
Qed.

Lemma taylor_integral_naive_intersection_correct :
  contains
    (I.convert taylor_integral_naive_intersection)
    (Xreal (RInt f a b)).
Proof.
rewrite /taylor_integral_naive_intersection.
set tmp := I.mul prec (I.sub prec ib ia) (iF (I.join ia ib)).
case I.subset.
by rewrite I.nai_correct.
apply I.meet_correct.
apply J.contains_RInt => //.
intros x Hx.
apply HiFIntExt.
assert (H := I.join_correct ia ib).
apply: contains_connected Hx.
apply H.
now apply Rmin_case ; [left|right].
apply H.
now apply Rmax_case ; [left|right].
exact: taylor_integral_correct.
Qed.

End DepthZeroPol.

End IntegralTaylor.
