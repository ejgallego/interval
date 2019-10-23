(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2016, Inria

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

From Coq Require Import Reals List ZArith Psatz.
From Coquelicot Require Import Coquelicot.
From mathcomp.ssreflect Require Import ssreflect ssrbool.

Require Import Stdlib.
Require Import Coquelicot.
Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.
Require Import Float_full.
Require Import Integral.
Require Import Eval.
Require Import Bertrand.
Require Import Tree.
Require Import Prog.
Require Import Reify.

Module IntervalTactic (F : FloatOps with Definition even_radix := true).

Inductive interval_tac_parameters : Set :=
  | i_prec (p : positive)
  | i_bisect (v : R)
  | i_bisect_diff (v : R)
  | i_bisect_taylor (v : R)
  | i_degree (d : nat)
  | i_depth (d : nat)
  | i_fuel (f : positive)
  | i_native_compute
  | i_delay.

Module Private.

Module I := FloatIntervalFull F.
Module J := IntervalExt I.
Module Fext := FloatExt F.
Module A := IntervalAlgos I.
Module Int := IntegralTactic F I.
Module Int' := IntegralTaylor I.
Module Bertrand := BertrandInterval F I.
Module T := Tree.Bnd I.
Module R := Reify.Bnd I.

Theorem app_merge_hyps_eval_bnd :
  forall prec vars hyps consts,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  exists bp,
  map A.interval_from_bp bp = R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts /\
  map A.real_from_bp bp = vars ++ map (fun c => eval c nil) consts.
Proof.
intros prec vars hyps consts He.
assert (exists bp1,
    map A.interval_from_bp bp1 = R.merge_hyps prec hyps /\
    map A.real_from_bp bp1 = vars) as [bp1 [<- <-]].
  revert vars He.
  induction (R.merge_hyps prec hyps) as [|h t IH].
    intros [|vars].
    now exists nil.
    easy.
  intros [|v vars].
  easy.
  intros [H1 H2].
  destruct (IH vars H2) as [bp [<- <-]].
  now exists (cons (A.Bproof v h H1) bp).
assert (exists bp2,
    map A.interval_from_bp bp2 = map (T.eval_bnd prec) consts /\
    map A.real_from_bp bp2 = map (fun c => eval c nil) consts) as [bp2 [<- <-]].
  clear.
  induction consts as [|h t IH].
    now exists nil.
  simpl.
  destruct IH as [bp [<- <-]].
  now exists (cons (A.Bproof _ _ (T.eval_bnd_correct prec h)) bp).
rewrite <- 2!map_app.
now exists (bp1 ++ bp2).
Qed.

Definition eval_bnd prec hyps prog consts g :=
  R.eval_goal_bnd prec g (nth 0 (A.BndValuator.eval prec prog (R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts)) I.nai).

Theorem eval_bnd_correct :
  forall prec vars hyps prog consts g,
  eval_bnd prec hyps prog consts g = true ->
  eval_hyps hyps vars
    (eval_goal g (nth 0 (eval_real prog (vars ++ map (fun c => eval c nil) consts)) 0%R)).
Proof.
intros prec vars hyps prog consts g H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
destruct (app_merge_hyps_eval_bnd _ _ _ consts H') as [bp [<- <-]].
apply A.BndValuator.eval_correct'.
Qed.

Theorem eval_bisect_aux :
  forall prec depth var0 vars hyps prog consts g fi,
  (forall bp xi x, contains (I.convert xi) (Xreal x) ->
   contains (I.convert (fi xi (map A.interval_from_bp bp)))
     (Xreal (nth 0 (eval_real prog (x :: map A.real_from_bp bp)) 0))) ->
  let bounds := R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun b => R.eval_goal_bnd prec g (fi b bounds)) depth = true ->
  eval_hyps hyps (var0 :: vars)
    (eval_goal g (eval_real' prog (var0 :: vars) consts)).
Proof.
intros prec depth var0 vars hyps prog consts g fi Hfi.
simpl.
intros H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply A.bisect_1d_correct' with (P := fun x => eval_goal g (eval_real' prog (x :: vars) consts)) (2 := H).
intros x xi Ix.
apply (R.eval_goal_bnd_correct prec).
destruct hyps as [|hx hyps].
easy.
destruct H' as [H1 H2].
unfold eval_real'.
simpl.
destruct (app_merge_hyps_eval_bnd _ _ _ consts H2) as [bp [<- <-]].
now apply Hfi.
destruct R.merge_hyps as [|vi t].
easy.
simpl in H' |- *.
rewrite I.lower_correct I.upper_correct.
now destruct I.convert.
Qed.

Definition eval_bisect prec depth hyps prog consts g :=
  let bounds := R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun b =>
    R.eval_goal_bnd prec g (nth 0 (A.BndValuator.eval prec prog (b :: bounds)) I.nai)
  ) depth.

Theorem eval_bisect_correct :
  forall prec depth var0 vars hyps prog consts g,
  eval_bisect prec depth hyps prog consts g = true ->
  eval_hyps hyps (var0 :: vars)
    (eval_goal g (eval_real' prog (var0 :: vars) consts)).
Proof.
intros prec depth var0 vars hyps prog consts g H.
apply (eval_bisect_aux prec depth) with (fi := fun b bounds => nth 0 (A.BndValuator.eval prec prog (b :: bounds)) I.nai) (2 := H).
intros bp xi x Ix.
apply (A.BndValuator.eval_correct' _ _ (A.Bproof _ _ Ix :: bp)).
Qed.

Definition eval_bisect_diff prec depth hyps prog consts g :=
  let bounds := R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts in
  let xi := nth 0 bounds I.nai in
  let bounds := tail bounds in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun b =>
    R.eval_goal_bnd prec g (A.DiffValuator.eval prec prog bounds 0 b)
  ) depth.

Theorem eval_bisect_diff_correct :
  forall prec depth var0 vars hyps prog consts g,
  eval_bisect_diff prec depth hyps prog consts g = true ->
  eval_hyps hyps (var0 :: vars)
    (eval_goal g (eval_real' prog (var0 :: vars) consts)).
Proof.
intros prec depth var0 vars hyps prog consts g H.
apply (eval_bisect_aux prec depth) with (fi := fun b bounds => A.DiffValuator.eval prec prog bounds 0 b) (2 := H).
intros bp xi x Ix.
apply A.DiffValuator.eval_correct with (1 := Ix).
Qed.

Definition eval_bisect_taylor prec deg depth hyps prog consts g :=
  let bounds := R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts in
  let xi := nth 0 bounds I.nai in
  let bounds := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const (tail bounds) in
  A.bisect_1d (I.lower xi) (I.upper xi) (fun b =>
    R.eval_goal_bnd prec g (A.TaylorValuator.TM.eval (prec, deg)
      (nth 0 (A.TaylorValuator.eval prec deg b prog bounds) A.TaylorValuator.TM.dummy) b b)
  ) depth.

Theorem eval_bisect_taylor_correct :
  forall prec deg depth var0 vars hyps prog consts g,
  eval_bisect_taylor prec deg depth hyps prog consts g = true ->
  eval_hyps hyps (var0 :: vars)
    (eval_goal g (eval_real' prog (var0 :: vars) consts)).
Proof.
intros prec deg depth var0 vars hyps prog consts g H.
apply (eval_bisect_aux prec depth) with (fi := fun b bounds =>
  A.TaylorValuator.TM.eval (prec, deg)
    (nth 0 (A.TaylorValuator.eval prec deg b prog (A.TaylorValuator.TM.var ::
      map A.TaylorValuator.TM.const bounds)) A.TaylorValuator.TM.dummy) b b) (2 := H).
intros bp xi x Ix.
rewrite map_map.
apply A.TaylorValuator.eval_correct with (1 := Ix).
Qed.

Ltac tuple_to_list params l :=
  match params with
  | pair ?a ?b => tuple_to_list a (b :: l)
  | ?b => constr:(b :: l)
  | ?z => fail 100 "Unknown tactic parameter" z
  end.

Inductive interval_tac_method : Set :=
  | itm_eval
  | itm_bisect
  | itm_bisect_diff
  | itm_bisect_taylor.

Ltac do_interval vars prec degree depth fuel native nocheck eval_tac :=
  let prec := eval vm_compute in (F.PtoP prec) in
  massage_goal ;
  reify_full vars ;
  match eval_tac with
  | itm_eval => apply (eval_bnd_correct prec)
  | itm_bisect => apply (eval_bisect_correct prec depth)
  | itm_bisect_diff => apply (eval_bisect_diff_correct prec depth)
  | itm_bisect_taylor => apply (eval_bisect_taylor_correct prec degree depth)
  end ;
  clear ;
  match nocheck with
  | true =>
    match native with
    | true => native_cast_no_check (refl_equal true)
    | false => vm_cast_no_check (refl_equal true)
    end
  | false =>
    (abstract
    match native with
    | true => native_cast_no_check (refl_equal true)
    | false => vm_cast_no_check (refl_equal true)
    end) ||
    fail 1 "Numerical evaluation failed to conclude. You may want to adjust some parameters"
  end.

Ltac do_parse params depth :=
  let rec aux vars prec degree depth fuel native nocheck itm params :=
    match params with
    | nil => constr:((vars, prec, degree, depth, fuel, native, nocheck, itm))
    | cons (i_prec ?p) ?t => aux vars p degree depth fuel native nocheck itm t
    | cons (i_degree ?d) ?t => aux vars prec d depth fuel native nocheck itm t
    | cons (i_bisect ?x) ?t => aux (cons x nil) prec degree depth fuel native nocheck itm_bisect t
    | cons (i_bisect_diff ?x) ?t => aux (cons x nil) prec degree depth fuel native nocheck itm_bisect_diff t
    | cons (i_bisect_taylor ?x) ?t => aux (cons x nil) prec degree depth fuel native nocheck itm_bisect_taylor t
    | cons (i_depth ?d) ?t => aux vars prec degree d fuel native nocheck itm t
    | cons (i_fuel ?f) ?t => aux vars prec degree depth f native nocheck itm t
    | cons i_native_compute ?t => aux vars prec degree depth fuel true nocheck itm t
    | cons i_delay ?t => aux vars prec degree depth fuel native true itm t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@nil R) 30%positive 10%nat depth 100%positive false false itm_eval params.

Ltac do_interval_parse params :=
  match do_parse params 15%nat with
  | (?vars, ?prec, ?degree, ?depth, ?fuel, ?native, ?nocheck, ?itm) =>
    do_interval vars prec degree depth fuel native nocheck itm
  end.

End Private.

Import Private.

Tactic Notation "interval" :=
  do_interval_parse (@nil interval_tac_parameters).

Tactic Notation "interval" "with" constr(params) :=
  do_interval_parse ltac:(tuple_to_list params (@nil interval_tac_parameters)).

(*
Tactic Notation "interval_intro" constr(t) :=
  do_interval_intro_parse t (fun v : I.type => v) (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" :=
  do_interval_intro_parse t I.upper_extent (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "upper"  :=
  do_interval_intro_parse t I.lower_extent (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "with" constr(params) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "as" simple_intropattern(H) :=
  do_interval_intro_parse t (fun v : I.type => v) (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.upper_extent (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "as" simple_intropattern(H)  :=
  do_interval_intro_parse t I.lower_extent (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.
*)

End IntervalTactic.

(*Require Import Specific_stdz.*)
Require Import Specific_bigint.
Require Import Specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.
Module ITSFBI2 := IntervalTactic SFBI2.
Export ITSFBI2.

(*

Require Import Generic_ops.
Module GFSZ2 := GenericFloat Radix2.
Module ITGFSZ2 := IntervalTactic GFSZ2.
Export ITGFSZ2.

Goal True.
interval_intro
  (RInt_gen
     (fun x => (1 * (/ (x * (pow (ln x) 2)))))
     (at_right 0)
     (at_point (1/3))) with (i_integral_deg 2).
done.


Goal True.
interval_intro
  (RInt_gen
     (fun x => (1 / x * (/ (x * (ln x)^3))))
     (at_point 10)
     (Rbar_locally p_infty)) with (i_integral_deg 0).
done.


Goal True.
interval_intro
  (RInt_gen
     (fun x => (1 / ((x^2 - 1)*(x^4 + 1)) * (powerRZ x 2 * (ln x)^1)))
     (at_right 0)
     (at_point (1/2))).
done.

Lemma blo0 :
   1 <= RInt (fun x => exp x) 0 1 <= 2.
Proof.
interval.
Qed.

Lemma blo1 :
  forall x, (Rabs x <= 15/3)%R ->
  (-4 <= x + 1)%R.
Proof.
intros.
interval.
Qed.

Lemma blo2 :
  (2/3 <= 5/7)%R.
Proof.
intros.
interval_intro (5/7)%R lower with (i_prec 4%nat).
apply Rle_trans with (2 := H).
interval.
Qed.

Lemma blo3 :
  forall x, (x <= 0)%R ->
  (0 <= x - x <= 0)%R.
Proof.
intros.
Time interval with (i_bisect_diff x).
Qed.

Lemma blo4 :
  forall x, (3/2 <= x <= 2)%R ->
  forall y, (1 <= y <= 33/32)%R ->
  (Rabs (sqrt(1 + x/sqrt(x+y)) - 144/1000*x - 118/100) <= 71/32768)%R.
Proof.
intros.
interval with (i_bisect x).
Qed.

Lemma blo5 :
  forall x, (-1 <= x <= 1)%R ->
  (0 <= exp x - (1 + x) <= 3/4)%R.
Proof.
intros.
split; try interval with (i_bisect_taylor x, i_degree 2).
interval with (i_bisect_diff x).
Qed.

Lemma blo6 : 51/1000 <= RInt_gen (fun x => sin x * (powerRZ x (-5)%Z * pow (ln x) 1%nat)) (at_point R1) (Rbar_locally p_infty) <= 52/1000.
Proof.
interval.
Qed.

Lemma blo7 :  -962587772 * / 8589934592 <=
      RInt_gen (fun x : R => x * (powerRZ x 1 * ln x ^ 1))
        (at_right 0) (at_point 1) <= -940939775 * / 8589934592.
Proof.
interval.
Qed.

Lemma blo8 : 876496966 * / 4398046511104 <=
      RInt_gen (fun x : R => 1 / x ^ 2 * exp (- x))
        (at_point 5) (Rbar_locally p_infty) <= 876509397 * / 4398046511104.
Proof.
interval.
Qed.

Lemma pi10 : (31415926535/10000000000 < PI < 31415926536/10000000000)%R.
Proof.
split; interval with (i_prec 40).
Qed.

*)
