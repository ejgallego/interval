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

Section Missing.

Lemma filter_prod_at_point_infty :
  forall a (P : R -> R -> Prop),
  (forall x y, a <= x <= y -> P x y) ->
  filter_prod (at_point a) (Rbar_locally p_infty)
  (fun ab : R * R => P ab.1 ab.2).
Proof.
intros a P HP.
apply (Filter_prod _ _ _ (fun x => x = a) (fun x => a < x)).
- easy.
- now exists a.
- move => x y -> /= H.
  apply HP.
  split.
  apply Rle_refl.
  now apply Rlt_le.
Qed.

Lemma filterlimi_const_loc {T} {U : UniformSpace}
  {F : (T -> Prop) -> Prop} {FF : Filter F} :
  forall (f : T -> U -> Prop) (a : U),
  F (fun x => f x a) ->
  filterlimi f F (locally a).
Proof.
intros f a Hf P HP.
rewrite /filtermapi /=.
apply: filter_imp Hf => x H.
exists a.
apply (conj H).
exact: locally_singleton.
Qed.

Lemma filterlimi_const {T} {U : UniformSpace}
  {F : (T -> Prop) -> Prop} {FF : Filter F} :
  forall (f : T -> U -> Prop) (a : U),
  (forall x, f x a) ->
  filterlimi f F (locally a).
Proof.
intros f a Hf.
apply filterlimi_const_loc.
exact: filter_forall.
Qed.

Lemma is_RInt_gen_0 {Fa Fb : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFb : Filter Fb} :
  is_RInt_gen (fun y => 0) Fa Fb zero.
Proof.
apply: filterlimi_const.
intros [a b].
rewrite -(scal_zero_r (b - a)).
exact: is_RInt_const.
Qed.

(* TODO: find better name *)
Lemma is_RInt_gen_filterlim {V : CompleteNormedModule R_AbsRing}
  {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> V) (lf : V) :
  is_RInt_gen f Fa Fb lf ->
  filterlim (fun x => RInt f x.1 x.2) (filter_prod Fa Fb) (locally lf).
Proof.
move => Hlf P HlfP.
have := (Hlf P HlfP).
case => Q R HFa HFb.
econstructor.
exact: HFa.
exact: HFb.
move => x y HQx HRy.
case : (p x y HQx HRy) => x0 [HRInt HP].
by move: (is_RInt_unique f x y _ HRInt ) => ->.
Qed.

(* very inelegant *)
Lemma ex_RInt_ex_RInt_gen {V : CompleteNormedModule R_AbsRing}
  {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> V) :
  ex_RInt_gen f Fa Fb ->
  (filter_prod Fa Fb (fun ab => ex_RInt f ab.1 ab.2)).
Proof.
intros [lf Hlf].
have := (Hlf (fun _ => True)).
case. now exists (mkposreal _ Rlt_0_1).
move => Q R HFaQ HFbR His_RInt.
apply: Filter_prod HFaQ HFbR _.
move => x y HQx HRy.
case: (His_RInt x y HQx HRy) => I [H _].
now exists I.
Qed.

(* very inelegant again *)
(* we probably want a more general lemma linking filterlim and filterlimi *)
Lemma RInt_gen_le {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f : R -> R) (g : R -> R) (lf : R) (lg : R) :
  filter_prod Fa Fb (fun ab => fst ab <= snd ab)
  -> filter_prod Fa Fb (fun ab => forall x, fst ab <= x <= snd ab -> f x <= g x)
  -> is_RInt_gen f Fa Fb lf -> is_RInt_gen g Fa Fb lg
    -> lf <= lg.
Proof.
move => Hab Hle.
move => Hlf Hlg.
apply (filterlim_le (F := filter_prod Fa Fb) (fun x => RInt f x.1 x.2) (fun x => RInt g x.1 x.2) lf lg).
apply: (filter_imp (fun x => ex_RInt f x.1 x.2 /\ ex_RInt g x.1 x.2 /\ (forall y, x.1 <= y <= x.2 -> f y <= g y) /\ x.1 <= x.2)).
move => x [H1 [H2 [H3 H4]]].
apply: RInt_le => // .
move => x0 Hx0. have:= H3 x0. apply.
by split; now apply Rlt_le.
apply: filter_and.
apply: ex_RInt_ex_RInt_gen.
now exists lf.
apply: filter_and.
apply: ex_RInt_ex_RInt_gen.
now exists lg.
apply: filter_and => // .
exact: is_RInt_gen_filterlim.
exact: is_RInt_gen_filterlim.
Qed.

Lemma ex_RInt_gen_cauchy {V : CompleteNormedModule R_AbsRing}
  {Fb : (R -> Prop) -> Prop} {FFb : ProperFilter Fb}
  (a : R) (f : R -> V) :
  ex_RInt_gen f (at_point a) Fb <->
  (filter_prod (at_point a) Fb (fun ab => ex_RInt f ab.1 ab.2) /\
  is_RInt_gen f Fb Fb zero).
Proof.
split.
- intros [If HIf].
  split.
  apply ex_RInt_ex_RInt_gen.
  now exists If.
  rewrite -(plus_opp_l If).
  apply: is_RInt_gen_Chasles (HIf).
  exact: is_RInt_gen_swap.
- intros [Hab Hb].
  refine (proj1 (filterlimi_locally_cauchy _ _) _).
    apply: filter_imp Hab.
    move => /= [a' b'] /= HIf.
    apply (conj HIf).
    intros y1 y2 H1 H2.
    rewrite -(is_RInt_unique _ _ _ _ H1).
    exact: is_RInt_unique.
  intros eps.
  destruct (Hb (ball_norm zero eps)) as [Qb Rb FbQb FbRb Hb'].
  apply locally_ball_norm.
  exists (fun ab => ab.1 = a /\ Qb ab.2 /\ Rb ab.2).
  split.
    eexists (fun x => x = a) _.
    easy.
    apply (filter_and _ _ FbQb FbRb).
    easy.
  intros [u1 u2] [v1 v2] [-> [Qbu2 Rbu2]] [-> [Qbv2 Rbv2]] I1 I2 HI1 HI2.
  apply: norm_compat1.
  destruct (Hb' _ _ Qbu2 Rbv2) as [I [HI HI']].
  unfold minus.
  apply is_RInt_swap in HI1.
  rewrite -(is_RInt_unique _ _ _ _ HI1).
  rewrite -(is_RInt_unique _ _ _ _ HI2).
  rewrite plus_comm RInt_Chasles.
  revert HI'.
  by rewrite /ball_norm minus_zero_r -(is_RInt_unique _ _ _ _ HI).
  eexists.
  exact HI1.
  eexists.
  exact HI2.
Qed.

End Missing.

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

Definition integralEstimatorCorrect (estimator : I.type) ia ib :=
  forall a b,
  contains (I.convert ia) (Xreal a) ->
  contains (I.convert ib) (Xreal b) ->
  I.convert estimator <> IInan ->
  exists I : R,
  is_RInt f a b I /\
  contains (I.convert estimator) (Xreal I).

Definition integralEstimatorCorrect_infty (estimator : I.type) ia:=
  forall a,
  contains (I.convert ia) (Xreal a) ->
  I.convert estimator <> IInan ->
  exists I : R,
  is_RInt_gen f (at_point a) (Rbar_locally p_infty) I /\
  contains (I.convert estimator) (Xreal I).

Section Functions.

Variable est : I.type -> I.type -> I.type.

Definition diam x := F.sub Interval_definitions.rnd_UP prec (I.upper x) (I.lower x).

Definition div2 f := F.scale2 f (F.ZtoS (-1)).

Fixpoint integral_interval_absolute (depth : nat) (ia ib : I.type) (epsilon : F.type) :=
  let int := I.join ia ib in
  let m := I.midpoint' int in
  match I.bounded m with
    | false => I.nai
    | true =>
      match depth with
        | O => I.add prec (est ia m) (est m ib)
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
      end
  end.

Variable est_infty : I.type -> I.type.

Fixpoint integral_interval_absolute_infty (depth : nat) (ia: I.type) (epsilon : F.type) :=
  let int := I.upper_extent ia in
  let m := I.midpoint' int in
  match I.bounded m with
    | false => I.nai
    | true =>
      match depth with
        | O => I.add prec (est ia m) (est_infty m)
        | S n => let m := I.midpoint' int in
                 let halfeps := div2 epsilon in
                 let roughEstimate_1 := est ia m in
                 let roughEstimate_2 := est_infty m in
                 match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
                   | true,true => I.add prec roughEstimate_1 roughEstimate_2
                   | true,false => let int2 := integral_interval_absolute_infty n m (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
                   | false,true => let int1 := integral_interval_absolute n ia m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
                   | false,false =>
                     let i1 := integral_interval_absolute n ia m halfeps in
                     let i2 := integral_interval_absolute_infty n m halfeps in
                     I.add prec i1 i2
                 end
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

Definition integral_interval_relative_infty
    (depth : nat) (ia : I.type) (epsilon : F.type) :=
  if I.bounded ia then
    let roughEst := est_infty ia in
    if depth is O then roughEst
    else
      let epsilon :=
        if I.bounded roughEst then
          F.mul Interval_definitions.rnd_UP prec epsilon
            (I.upper (I.abs roughEst))
        else epsilon in
      if F'.le (diam roughEst) epsilon then roughEst
      else integral_interval_absolute_infty (depth-1) ia epsilon
  else I.nai.


Lemma integral_interval_absolute_Sn {n ia ib epsilon} :
  let int := I.join ia ib in
  let m := I.midpoint' int in
  let halfeps := div2 epsilon in
  let roughEstimate_1 := est ia m in
  let roughEstimate_2 := est m ib in
  I.bounded m ->
  integral_interval_absolute (S n) ia ib epsilon =
  match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
    | true,true => I.add prec roughEstimate_1 roughEstimate_2
    | true,false => let int2 := integral_interval_absolute n m ib (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
    | false,true => let int1 := integral_interval_absolute n ia m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
    | false,false =>
      let i1 := integral_interval_absolute n ia m halfeps in
      let i2 := integral_interval_absolute n m ib halfeps in
      I.add prec i1 i2
  end.
Proof.
rewrite /=.
move ->.
by [].
Qed.

Lemma integral_interval_absolute_infty_Sn {n ia epsilon} :
  let int := I.upper_extent ia in
  let m := I.midpoint' int in
  let halfeps := div2 epsilon in
  let roughEstimate_1 := est ia m in
  let roughEstimate_2 := est_infty m in
  I.bounded m ->
  integral_interval_absolute_infty (S n) ia epsilon =
  match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
    | true,true => I.add prec roughEstimate_1 roughEstimate_2
    | true,false => let int2 := integral_interval_absolute_infty n m (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
    | false,true => let int1 := integral_interval_absolute n ia m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
    | false,false =>
      let i1 := integral_interval_absolute n ia m halfeps in
      let i2 := integral_interval_absolute_infty n m halfeps in
      I.add prec i1 i2
  end.
Proof.
(* rewrite /integral_interval_absolute. *)
rewrite /=.
move ->.
by [].
Qed.


Definition naive_integral (ia ib : I.type) :=
  I.mul prec (I.sub prec ib ia) (iF (I.join ia ib)).

End Functions.

Section Proofs.

Variable estimator : I.type -> I.type -> I.type.
Variable estimator_infty : I.type -> I.type.

Lemma integral_interval_absolute_correct (depth : nat) ia ib epsilon :
  (forall ia ib, integralEstimatorCorrect (estimator ia ib) ia ib) ->
  I.bounded ia ->
  I.bounded ib ->
  integralEstimatorCorrect (integral_interval_absolute estimator depth ia ib epsilon) ia ib.
Proof.
move => base_case Hboundia Hboundib.
elim: depth epsilon ia ib Hboundia Hboundib =>
[|d Hd] epsilon ia ib Hboundia Hboundib a b Hia Hib HnotInan.
- move: HnotInan.
  set iab := (I.join ia ib).
  rewrite /integral_interval_absolute.
  set m' := I.midpoint' iab.
  case: (I.bounded m'); last by rewrite I.nai_correct.
  have [m Hm]:  (not_empty (I.convert m')).
    move: (I.midpoint'_correct iab) => [H1 H2].
    by apply: H2; exists a; apply: I.join_correct; left.
  move => HnotInan.
  case: (base_case ia m' a m) => // [M|Iam [Ham Cam]].
    apply: HnotInan.
    exact: I.add_propagate_l.
  case: (base_case m' ib m b) => // [M|Imb [Hmb Cmb]].
    apply: HnotInan.
    exact: I.add_propagate_r.
  exists (Iam + Imb).
  split.
  exact: is_RInt_Chasles Ham Hmb.
  exact: J.add_correct.
- set iab := (I.join ia ib).
  set m' := I.midpoint' iab.
  case Hbnded: (I.bounded m'); last first.
    by rewrite /integral_interval_absolute Hbnded I.nai_correct in HnotInan.
  rewrite (integral_interval_absolute_Sn _ Hbnded) in HnotInan |- *.
  have [m Hm]: (not_empty (I.convert m')).
    move: (I.midpoint'_correct iab) => [H1 H2].
    by apply: H2; exists a; apply: I.join_correct; left.
  have K: (forall i1 i2,
      I.convert i1 <> Inan ->
      I.convert i2 <> Inan ->
      integralEstimatorCorrect i1 ia m' ->
      integralEstimatorCorrect i2 m' ib ->
      exists I : R, is_RInt f a b I /\ contains (I.convert (I.add prec i1 i2)) (Xreal I)).
    move => i1 i2 N1 N2 H1 H2.
    case: (H1 a m) => {H1} // [I1 [H1 C1]].
    case: (H2 m b) => {H2} // [I2 [H2 C2]].
    exists (I1 + I2).
    split.
    exact: is_RInt_Chasles H1 H2.
    exact: J.add_correct.
  move: HnotInan.
  set b1 := (X in if X then _ else _).
  case: b1.
  + set b2 := (X in if X then _ else _).
    case Hb2 : b2 => HnotInan.
    * apply: K => // [L|L] ; apply: HnotInan.
      exact: I.add_propagate_l.
      exact: I.add_propagate_r.
    * apply: K => // [L|L|] ; try apply: HnotInan.
      exact: I.add_propagate_l.
      exact: I.add_propagate_r.
      exact: Hd.
  + set b2 := (X in if X then _ else _).
    case: b2 => HnotInan.
    * apply: K => // [L|L|] ; try apply: HnotInan.
      exact: I.add_propagate_l.
      exact: I.add_propagate_r.
      exact: Hd.
    * apply: K => // [L|L||] ; try apply: HnotInan.
      exact: I.add_propagate_l.
      exact: I.add_propagate_r.
      exact: Hd.
      exact: Hd.
Qed.

Lemma integral_interval_absolute_infty_correct (depth : nat) ia epsilon :
  (forall ia ib, integralEstimatorCorrect (estimator ia ib) ia ib) ->
  (forall ia, integralEstimatorCorrect_infty (estimator_infty ia) ia) ->
  I.bounded ia ->
  integralEstimatorCorrect_infty (integral_interval_absolute_infty estimator estimator_infty depth ia epsilon) ia.
Proof.
move => base_case base_case_infty Hboundia.
elim: depth epsilon ia Hboundia =>
[|d Hd] epsilon ia Hboundia a Hia HnotInan.
- move: HnotInan.
  set iab := (I.upper_extent ia).
  rewrite /integral_interval_absolute_infty.
  set m' := I.midpoint' iab.
  case: (I.bounded m'); last by rewrite I.nai_correct.
  have [m Hm]:  (not_empty (I.convert m')).
    move: (I.midpoint'_correct iab) => [H1 H2].
    apply: H2; exists a.
    apply: I.upper_extent_correct; first exact : Hia.
    exact: Rle_refl.
  move => HnotInan.
  case: (base_case ia m' a m) => // [M|Iam [Ham Cam]].
    apply: HnotInan.
    exact: I.add_propagate_l.
  case: (base_case_infty m' m) => // [M|Imb [Hmb Cmb]].
    apply: HnotInan.
    exact: I.add_propagate_r.
  exists (Iam + Imb).
  split.
  apply: is_RInt_gen_Chasles Hmb.
  by rewrite is_RInt_gen_at_point.
  exact: J.add_correct.
- set iab := (I.upper_extent ia).
  set m' := I.midpoint' iab.
  case Hbnded: (I.bounded m'); last first.
    by rewrite /integral_interval_absolute_infty Hbnded I.nai_correct in HnotInan.
  rewrite (integral_interval_absolute_infty_Sn _ _ Hbnded) in HnotInan |- *.
  have [m Hm]:  (not_empty (I.convert m')).
    move: (I.midpoint'_correct iab) => [H1 H2].
    apply: H2; exists a.
    apply: I.upper_extent_correct; first exact : Hia.
    exact: Rle_refl.
  have K: (forall i1 i2,
      I.convert i1 <> Inan ->
      I.convert i2 <> Inan ->
      integralEstimatorCorrect i1 ia m' ->
      integralEstimatorCorrect_infty i2 m' ->
      exists I : R, is_RInt_gen f (at_point a) (Rbar_locally p_infty) I /\ contains (I.convert (I.add prec i1 i2)) (Xreal I)).
    move => i1 i2 N1 N2 H1 H2.
    case: (H1 a m) => {H1} // [I1 [H1 C1]].
    case: (H2 m) => {H2} // [I2 [H2 C2]].
    exists (I1 + I2).
    split.
    apply: is_RInt_gen_Chasles H2.
    by rewrite is_RInt_gen_at_point.
    exact: J.add_correct.
  move: HnotInan.
  set b1 := (X in if X then _ else _).
  case: b1.
  + set b2 := (X in if X then _ else _).
    case Hb2 : b2 => HnotInan.
    * apply: K => // [L|L] ; apply: HnotInan.
      exact: I.add_propagate_l.
      exact: I.add_propagate_r.
    * apply: K => // [L|L|] ; try apply: HnotInan.
      exact: I.add_propagate_l.
      exact: I.add_propagate_r.
      exact: Hd.
  + set b2 := (X in if X then _ else _).
    case: b2 => HnotInan.
    * apply: K => // [L|L|] ; try apply: HnotInan.
      exact: I.add_propagate_l.
      exact: I.add_propagate_r.
      exact: integral_interval_absolute_correct.
    * apply: K => // [L|L||] ; try apply: HnotInan.
      exact: I.add_propagate_l.
      exact: I.add_propagate_r.
      exact: integral_interval_absolute_correct.
      exact: Hd.
Qed.

Lemma integral_interval_relative_correct (depth : nat) ia ib epsilon :
  (forall ia ib, integralEstimatorCorrect (estimator ia ib) ia ib) ->
  integralEstimatorCorrect (integral_interval_relative estimator depth ia ib epsilon) ia ib.
Proof.
move => base_case.
rewrite /integral_interval_relative.
case Hiab: (I.bounded ia);
  case Hibb: (I.bounded ib) => /=;
  try (move => a b _ _ ; by rewrite I.nai_correct).
case: depth => [|depth].
exact: base_case.
set b1 := (X in if X then _ else _).
case Hb1 : b1.
exact: base_case.
exact: integral_interval_absolute_correct.
Qed.

Lemma integral_interval_relative_infty_correct (depth : nat) ia epsilon :
  (forall ia ib, integralEstimatorCorrect (estimator ia ib) ia ib) ->
  (forall ia, integralEstimatorCorrect_infty (estimator_infty ia) ia) ->
  integralEstimatorCorrect_infty (integral_interval_relative_infty estimator estimator_infty depth ia epsilon) ia.
Proof.
move => base_case base_case_infty.
rewrite /integral_interval_relative_infty.
case Hiab: (I.bounded ia); last by move => a _ ; rewrite I.nai_correct.
case: depth => [|depth].
exact: base_case_infty.
set b1 := (X in if X then _ else _).
case Hb1 : b1.
exact: base_case_infty.
exact: integral_interval_absolute_infty_correct.
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

End Proofs.

End IntervalIntegral.

(* this can probably be significantly shortened *)
Lemma bounded_ex {xi} (Hbnded : I.bounded xi) : (exists l u : R, I.convert xi = Ibnd (Xreal l) (Xreal u)).
Proof.
exists (proj_val (I.convert_bound (I.lower xi))).
exists (proj_val (I.convert_bound (I.upper xi))).
have := (I.bounded_correct xi).
rewrite Hbnded; case => // .
move => Hlb Hub.
case: (I.lower_bounded_correct xi Hlb) => <- => /= HbndedProp.
case: (I.upper_bounded_correct xi Hub) => <-.
by rewrite /I.bounded_prop => /= -> /=.
Qed.

Lemma integral_interval_mul_infty :
  forall prec a ia f fi g Ig Igi,
  contains (I.convert ia) (Xreal a) ->
  (forall x, a <= x -> contains (I.convert fi) (Xreal (f x))) ->
  I.bounded fi ->
  (forall x, a <= x -> continuous f x) ->
  (forall x, a <= x -> 0 <= g x) ->
  is_RInt_gen g (at_point a) (Rbar_locally p_infty) Ig ->
  contains (I.convert Igi) (Xreal Ig) ->
  exists Ifg,
  is_RInt_gen (fun t => f t * g t) (at_point a) (Rbar_locally p_infty) Ifg /\
  contains (I.convert (I.mul prec fi Igi)) (Xreal Ifg).
Proof.
intros prec a ia f fi g Ig Igi Hia Hf Hfi Cf Hg HIg HIg'.
move: (bounded_ex Hfi) => [] l [] u HiFia.
have Hgoodorder_bis : forall x, a <= x -> l <= f x <= u.
  move => x0 Hax0.
  move: (Hf _ Hax0).
  by rewrite HiFia.
suff [Ifg HIfg]: ex_RInt_gen (fun t => f t * g t) (at_point a) (Rbar_locally p_infty).
exists Ifg.
have HIntl : is_RInt_gen (fun x => scal l (g x)) (at_point a) (Rbar_locally p_infty) (scal l Ig).
  by apply: is_RInt_gen_scal.
have HIntu : is_RInt_gen (fun x => scal u (g x)) (at_point a) (Rbar_locally p_infty) (scal u Ig).
  by apply: is_RInt_gen_scal.
have Hgoodorder : l <= u.
  move: (Hgoodorder_bis a (Rle_refl a)).
  intros [H1 H2].
  exact: Rle_trans H1 H2.
have intgpos : 0 <= Ig.
  have -> : 0 = norm 0 by rewrite norm_zero.
  apply: (RInt_gen_norm (fun _ => 0) g 0 Ig _ _ _ HIg) => //= .
  + now apply filter_prod_at_point_infty.
  + apply (filter_prod_at_point_infty a (fun x y => forall z, x <= z <= y -> norm 0 <= g z)).
    intros m n [Hm _] o [Ho _].
    rewrite norm_zero.
    apply Hg.
    now apply Rle_trans with m.
  + exact: is_RInt_gen_0.
apply (conj HIfg).
apply: (contains_connected _ (scal l Ig) (scal u Ig)).
apply: J.mul_correct => // .
  rewrite HiFia.
  exact: (conj (Rle_refl _)).
apply: J.mul_correct => // .
  rewrite HiFia.
  exact: conj (Rle_refl _).
split.
apply: (@RInt_gen_le (at_point a) (Rbar_locally p_infty) _ _ (fun x => scal l (g x)) (fun x => scal (f x) (g x)) _ _) => // .
  now apply filter_prod_at_point_infty.
  apply (filter_prod_at_point_infty a (fun x y => forall z, x <= z <= y -> _ <= _)).
  intros m n [Hm _] o [Ho _].
  rewrite /scal /= /mult /= .
  apply: Rmult_le_compat_r => // .
  apply Hg.
  now apply Rle_trans with m.
  apply Hgoodorder_bis.
  now apply Rle_trans with m.
apply: (@RInt_gen_le (at_point a) (Rbar_locally p_infty) _ _ (fun x => scal (f x) (g x)) (fun x => scal u (g x)) _ _) => // .
  now apply filter_prod_at_point_infty.
  apply (filter_prod_at_point_infty a (fun x y => forall z, x <= z <= y -> _ <= _)).
  intros m n [Hm _] o [Ho _].
  rewrite /scal /= /mult /= .
  apply: Rmult_le_compat_r => // .
  apply Hg.
  now apply Rle_trans with m.
  apply Hgoodorder_bis.
  now apply Rle_trans with m.
refine (proj2 (ex_RInt_gen_cauchy _ _) _).
split.
apply filter_prod_at_point_infty.
Admitted.

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
