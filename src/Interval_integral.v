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
Require Import xreal_ssr_compat.
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

Definition integralEstimatorCorrect (estimator : F.type -> F.type -> I.type) :=
        forall a b,
          ex_RInt f (toR a) (toR b) ->
          toR a <= toR b ->
          F.real a ->
          F.real b ->
          contains (I.convert (estimator a b)) (Xreal (RInt f (toR a) (toR b))).

Section Functions.

Variable est : F.type -> F.type -> I.type.

Definition diam x := F.sub Interval_definitions.rnd_UP prec (I.upper x) (I.lower x).

Definition div2 f := F.scale2 f (F.ZtoS (-1)).

Fixpoint integral_float_absolute (depth : nat) (a b : F.type) (epsilon : F.type) :=
  let int := I.bnd a b in
  match depth with
    | O => let m := I.midpoint int in
           I.add prec (est a m) (est m b)
    | S n => let m := I.midpoint int in
             let int1 := I.bnd a m in
             let int2 := I.bnd m b in
             let halfeps := div2 epsilon in
             let roughEstimate_1 := est a m in
             let roughEstimate_2 := est m b in
             match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
               | true,true => I.add prec roughEstimate_1 roughEstimate_2
               | true,false => let int2 := integral_float_absolute n m b (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
               | false,true => let int1 := integral_float_absolute n a m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
               | false,false =>
                 let i1 := integral_float_absolute n a m halfeps in
                 let i2 := integral_float_absolute n m b halfeps in
                 I.add prec i1 i2
             end
  end.

Definition integral_float_relative
    (depth : nat) (a b : F.type) (epsilon : F.type) :=
  if F.real a && F.real b then
    let roughEst := est a b in
    if depth is O then roughEst
    else
      let epsilon :=
        if I.bounded roughEst then
          F.mul Interval_definitions.rnd_UP prec epsilon
            (I.upper (I.abs roughEst))
        else epsilon in
      if F'.le (diam roughEst) epsilon then roughEst
      else integral_float_absolute (depth-1) a b epsilon
  else I.nai.

Lemma integral_float_absolute_Sn n a b epsilon :
  let int := I.bnd a b in
  let m := I.midpoint int in
  let int1 := I.bnd a m in
  let int2 := I.bnd m b in
  let halfeps := div2 epsilon in
  let roughEstimate_1 := est a m in
  let roughEstimate_2 := est m b in
  integral_float_absolute (S n) a b epsilon =
  match F'.le (diam roughEstimate_1) halfeps, F'.le (diam roughEstimate_2) halfeps with
    | true,true => I.add prec roughEstimate_1 roughEstimate_2
    | true,false => let int2 := integral_float_absolute n m b (F.sub_exact epsilon (diam roughEstimate_1)) in I.add prec roughEstimate_1 int2
    | false,true => let int1 := integral_float_absolute n a m (F.sub_exact epsilon (diam roughEstimate_2)) in I.add prec int1 roughEstimate_2
    | false,false =>
      let i1 := integral_float_absolute n a m halfeps in
      let i2 := integral_float_absolute n m b halfeps in
      I.add prec i1 i2
  end.
Proof.
by [].
Qed.

Definition integral_float_absolute_signed (depth : nat) (a b : F.type) (epsilon : F.type) :=
  match F'.le a b with
    | false => I.neg (integral_float_relative depth b a epsilon)
    | true => integral_float_relative depth a b epsilon
  end.

Definition naive_integral (ia ib : I.type) :=
  I.mul prec (I.sub prec ib ia) (iF (I.join ia ib)).

Definition integral_intBounds_epsilon depth (i1 i2 : I.type) epsilon :=
  let b1 := I.upper i1 in
  let a2 := I.lower i2 in
  if F'.le b1 a2 then
    let si1 := naive_integral i1 (thin b1) in
    let si2 := naive_integral (thin a2) i2 in
    I.add prec (I.add prec si1 (integral_float_absolute_signed depth b1 a2 epsilon)) si2
  else I.nai.

End Functions.

Section Proofs.

Variable estimator : F.type -> F.type -> I.type.

Hypothesis Hcorrect : integralEstimatorCorrect estimator.

Definition ex_RInt_base_case :=
  forall u0 l1,
  F.real u0 ->
  F.real l1 ->
  toR u0 <= toR l1 ->
  I.convert (estimator u0 l1) <> IInan ->
  ex_RInt f (toR u0) (toR l1).

Lemma integral_ex_RInt_aux u0 l1 :
  F'.le u0 l1 ->
  F.real u0 /\ F.real l1 /\ toR u0 <= toR l1.
Proof.
  rewrite 2!F.real_correct.
  move /F'.le_correct => H.
  destruct F.toX ; try easy.
  by destruct F.toX.
Qed.

Lemma integral_float_absolute_ex_RInt (depth : nat) u0 l1 epsilon :
  ex_RInt_base_case ->
  I.convert (integral_float_absolute estimator depth u0 l1 epsilon) <> IInan ->
  F'.le u0 l1 ->
  ex_RInt f (toR u0) (toR l1).
Proof.
move => ex_RInt_base_case HnotInan Hleu0l1.
have [Hrealu0 [Hreall1 Hleu0ml1]] := integral_ex_RInt_aux _ _ Hleu0l1.
elim: depth u0 l1 epsilon Hreall1 Hrealu0 HnotInan {Hleu0l1} Hleu0ml1 => [|d HId] u0 l1 epsilon Hreall1 Hrealu0 HnotInan Hleu0ml1.
- pose m := I.midpoint (I.bnd u0 l1).
  have Hrealm : (F.real m).
    suff: F.toX m = Xreal (toR m).
    by rewrite F.real_correct => ->.
  have := (I.midpoint_correct (I.bnd u0 l1)).
    + case.
      exists (Xreal (toR u0)).
      move: (contains_convert_bnd_l u0 l1 Hrealu0 Hleu0ml1).
      by move/F_realP :Hrealu0 => -> .
    + by [].
  (* first we establish a useful inequality on u0, m and l1 *)
  have := (midpoint_bnd_in u0 l1 Hrealu0 Hreall1 Hleu0ml1).
  rewrite -[I.midpoint _]/m.
  move => [Hleu0m Hleml1].
  apply: (ex_RInt_Chasles _ _ (toR m)).
    + apply: ex_RInt_base_case => //.
      contradict HnotInan.
      exact: I.add_propagate_l.
    + apply: ex_RInt_base_case => //.
      contradict HnotInan.
      exact: I.add_propagate_r.
- pose m := I.midpoint (I.bnd u0 l1).
  have Hrealm : (F.real m).
    suff: F.toX m = Xreal (toR m).
      by move/F_realP.
    have := (I.midpoint_correct (I.bnd u0 l1)).
      case.
      exists (Xreal (toR u0)).
      move: (contains_convert_bnd_l u0 l1 Hrealu0 Hleu0ml1).
      by move/F_realP :Hrealu0 => ->.
    by [].
  (* first we establish a useful inequality on u0, m and l1 *)
  have := (midpoint_bnd_in u0 l1 Hrealu0 Hreall1 Hleu0ml1).
  rewrite -[I.midpoint _]/m.
  move => [Hleu0m Hleml1].
  apply: (ex_RInt_Chasles _ _ (toR m)).
  + move: HnotInan.
    rewrite integral_float_absolute_Sn -[I.midpoint _]/m.
    set b1 := (X in (if X then _ else _)).
    set b2 := (X in (if X then (I.add prec _ _) else _)).
    case Hb1 : b1.
    * case Hb2 : b2; move => HnotInan;
      apply: (ex_RInt_base_case) => //;
      contradict HnotInan;
      exact: I.add_propagate_l.
    * set b3 := (X in (if X then _ else _)).
      case Hb3 : b3.
      - set epsilon' := (F.sub_exact _ _); move => HnotInan.
        apply: (HId u0 m epsilon') => //.
        contradict HnotInan.
        exact: I.add_propagate_l.
      - set epsilon' := (div2 _); move => HnotInan.
        apply: (HId u0 m epsilon') => //.
        contradict HnotInan.
        exact: I.add_propagate_l.
  + move: HnotInan.
    rewrite integral_float_absolute_Sn -[I.midpoint _]/m.
    set b1 := (X in (if X then _ else _)).
    set b2 := (X in (if X then (I.add prec _ _) else _)).
    case Hb1 : b1.
    * case Hb2 : b2.
      + move => HnotInan.
        apply: ex_RInt_base_case => //.
        contradict HnotInan.
        exact: I.add_propagate_r.
      + set epsilon' := (F.sub_exact _ _); move => HnotInan.
        apply: (HId m l1 epsilon') => //.
        contradict HnotInan.
        exact: I.add_propagate_r.
    * set b3 := (X in (if X then _ else _)).
      case Hb3 : b3.
      - move => HnotInan; apply: ex_RInt_base_case => //.
        rewrite -/iF.
        contradict HnotInan.
        exact: I.add_propagate_r.
      - set epsilon' := (div2 _); move => HnotInan.
        apply: (HId m l1 epsilon') => //.
        contradict HnotInan.
        exact: I.add_propagate_r.
Qed.

Lemma integral_float_absolute_correct (depth : nat) (a b : F.type) epsilon :
  F.real a -> F.real b ->
  ex_RInt f (toR a) (toR b) ->
  toR a <= toR b ->
  contains (I.convert (integral_float_absolute estimator depth a b epsilon)) (Xreal (RInt f (toR a) (toR b))).
Proof.
move => Hareal Hbreal.
elim: depth a b epsilon Hareal Hbreal => [ | k Hk] a b epsilon Hareal Hbreal Hintegrable Hleab.
- set midpoint := I.midpoint (I.bnd a b).
  have hIl : ex_RInt f (toR a) (toR midpoint).
    by apply:  (ex_RInt_Chasles_1 _ _ _ (toR b)) => //; apply: midpoint_bnd_in.
  have hIr : ex_RInt f (toR midpoint) (toR b).
    by apply:  (ex_RInt_Chasles_2 f (toR a))=> //; apply: midpoint_bnd_in.
  have -> : RInt f (toR a) (toR b) =
            RInt f (toR a) (toR midpoint) + RInt f (toR midpoint) (toR b).
    by rewrite RInt_Chasles.
  set I1 := RInt _ _ _; set I2 := RInt _ _ _.
  have [in1 in2] := midpoint_bnd_in a b Hareal Hbreal Hleab.
  have hm : F.real (I.midpoint (I.bnd a b)).
  suff /I.midpoint_correct []:
    exists x : ExtendedR, contains (I.convert (I.bnd a b)) x by move/F_realP.
    by exists (I.convert_bound a); apply: contains_convert_bnd_l => //; exact/F_realP.
 by rewrite Xreal_add; apply: I.add_correct; apply: Hcorrect => // .
- set midpoint := I.midpoint (I.bnd a b).
have hIl : ex_RInt f (toR a) (toR midpoint).
  by apply:  (ex_RInt_Chasles_1 _ _ _ (toR b)) => //; apply: midpoint_bnd_in.
have hIr : ex_RInt f (toR midpoint) (toR b).
  by apply:  (ex_RInt_Chasles_2 f (toR a))=> //; apply: midpoint_bnd_in.
have -> : RInt f (toR a) (toR b) =
  RInt f (toR a) (toR midpoint) + RInt f (toR midpoint) (toR b).
  by rewrite RInt_Chasles.
set I1 := RInt _ _ _; set I2 := RInt _ _ _.
have [in1 in2] := midpoint_bnd_in a b Hareal Hbreal Hleab.
rewrite integral_float_absolute_Sn.
rewrite (* /integral_float_absolute -/integral_float_absolute. *) -[Xreal (_ + _)]/(Xadd (Xreal I1) (Xreal I2)).
set d1 := diam _.
set d2 := diam _.
have hm : F.real (I.midpoint (I.bnd a b)).
  suff /I.midpoint_correct []:
    exists x : ExtendedR, contains (I.convert (I.bnd a b)) x by move/F_realP.
  by exists (I.convert_bound a); apply: contains_convert_bnd_l => //; exact/F_realP.
case Hcmp1 : (F'.le d1 (div2 epsilon)); case Hcmp2 : (F'.le d2 (div2 epsilon));
repeat ((try (apply: I.add_correct => // )); try (apply: Hcorrect => // ); try (apply: Hk => // )).
Qed.

Lemma integral_float_relative_ex_RInt (depth : nat) u0 l1 epsilon :
  ex_RInt_base_case ->
  I.convert (integral_float_relative estimator depth u0 l1 epsilon) <> IInan ->
  F'.le u0 l1 ->
  ex_RInt f (toR u0) (toR l1).
Proof.
move => ex_RInt_base_case HnotInan Hleu0l1.
have [Hrealu0 [Hreall1 Hleu0ml1]] := integral_ex_RInt_aux _ _ Hleu0l1.
move: HnotInan.
rewrite /integral_float_relative.
rewrite Hrealu0 Hreall1.
case: depth => [|depth].
exact: ex_RInt_base_case.
case: F'.le.
- exact: ex_RInt_base_case.
- move => HnotInan.
  exact: integral_float_absolute_ex_RInt HnotInan _.
Qed.

Lemma integral_float_relative_correct (depth : nat) (a b : F.type) epsilon :
  ex_RInt f (toR a) (toR b) ->
  toR a <= toR b ->
  contains (I.convert (integral_float_relative estimator depth a b epsilon)) (Xreal (RInt f (toR a) (toR b))).
Proof.
case Hareal : (F.real a); case Hbreal: (F.real b) => Hfint Hab; case: depth => [|depth];
  rewrite /integral_float_relative ?Hareal ?Hbreal /= ?I.nai_correct //.
- by rewrite /=; apply: Hcorrect.
- case: I.bounded; case: F'.le; first by apply: Hcorrect.
  + by apply: integral_float_absolute_correct.
  + by apply: Hcorrect.
  + by apply: integral_float_absolute_correct.
Qed.

Lemma integral_float_absolute_signed_correct (depth : nat) (a b : F.type) epsilon :
  ex_RInt f (toR a) (toR b) ->
  (F.real a) -> (F.real b) ->
  contains (I.convert (integral_float_absolute_signed estimator depth a b epsilon)) (Xreal (RInt f (toR a) (toR b))).
Proof.
rewrite /integral_float_absolute_signed /F'.le F.cmp_correct.
move => Hint /F_realP -> /F_realP -> /=.
case: Rcompare_spec => Hab ;
  try apply: integral_float_relative_correct => //.
- exact: Rlt_le.
- exact: Req_le.
rewrite -RInt_swap.
apply: J.neg_correct.
apply: integral_float_relative_correct.
+ exact: ex_RInt_swap.
+ exact: Rlt_le.
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
    (I.convert (integral_intBounds_epsilon estimator depth ia ib epsilon))
    (Xreal (RInt f a b)).
Proof.
move => Hconta Hcontb HFInt.
rewrite /integral_intBounds_epsilon.
generalize (I.upper_correct ia) (I.lower_correct ib).
set ua := I.upper ia.
set lb := I.lower ib.
unfold I.convert_bound.
intros Hua' Hlb'.
case Hle: F'.le; last by rewrite I.nai_correct.
assert (F.toX ua <> Xnan /\ F.toX lb <> Xnan /\
  proj_val (F.toX ua) <= proj_val (F.toX lb)) as [Hua [Hlb Hualb]].
  generalize (F'.le_correct ua lb).
  destruct F'.le. 2: easy.
  intros H.
  specialize (H eq_refl).
  destruct F.toX. easy.
  destruct F.toX. easy.
  split. easy.
  split ; easy.
have Haua: (a <= toR ua).
  case: (I.convert ia) Hconta Hua' Hua => [|l u] /= H -> //=.
  move: H => [_].
  by case: u.
have Hlbb : (toR lb <= b).
  case: (I.convert ib) Hcontb Hlb' Hlb => [|l u] /= H -> //=.
  move: H => [H _].
  by case: l H.
have Hfint_a_lb : ex_RInt f a (toR lb).
  apply: (ex_RInt_Chasles_1 _ _ _ b) HFInt.
  split => //.
  now apply Rle_trans with (1 := Haua).
have Hfint_ua_lb : ex_RInt f (toR ua) (toR lb).
apply: (ex_RInt_Chasles_2 _ a) Hfint_a_lb.
by split.
have -> : Xreal (RInt f a b) =
        Xadd
          (Xadd (Xreal (RInt f a (toR ua))) (Xreal (RInt f (toR ua) (toR lb))))
          (Xreal (RInt f (toR lb) b)).
     rewrite /= 2?RInt_Chasles //.
     apply: (ex_RInt_Chasles_2 _ a) => //.
     split => //.
     now apply Rle_trans with (1 := Haua).
     apply: ex_RInt_Chasles_1 Hfint_a_lb.
     by split.
   apply: I.add_correct.
   + apply: I.add_correct.
     * apply: naive_integral_correct => //.
       generalize (thin_correct ua).
       by destruct F.toX.
       apply: ex_RInt_Chasles_1 Hfint_a_lb.
       by split.
     * apply: integral_float_absolute_signed_correct => // ; apply: toX_toF_Freal => // .
   + apply: naive_integral_correct => //.
     generalize (thin_correct lb).
     by destruct (F.toX lb).
     apply: (ex_RInt_Chasles_2 _ a) => //.
     split => //.
     now apply Rle_trans with (1 := Haua).
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
