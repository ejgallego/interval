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
From Flocq Require Import Zaux.
From Coquelicot Require Import Coquelicot.

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
Require Import Refine.

Inductive interval_tac_parameters : Set :=
  | i_prec (p : positive)
  | i_bisect (v : R)
  | i_autodiff (v : R)
  | i_taylor (v : R)
  | i_degree (d : nat)
  | i_depth (d : nat)
  | i_fuel (f : positive)
  | i_width (w : Z)
  | i_relwidth (w : positive)
  | i_native_compute
  | i_delay.

Module Private.

Inductive interval_tac_method : Set :=
  | itm_naive
  | itm_autodiff
  | itm_taylor.

Inductive interval_extent : Set :=
  | ie_none
  | ie_lower
  | ie_upper.

Ltac tuple_to_list params l :=
  match params with
  | pair ?a ?b => tuple_to_list a (b :: l)
  | pair _ ?b => fail 100 "Unknown tactic parameter" b
  | ?b => constr:(b :: l)
  | ?b => fail 100 "Unknown tactic parameter" b
  end.

Ltac do_interval_generalize convert :=
  match goal with
  | |- contains (convert ?b) (Xreal ?t) -> _ =>
    let H := fresh "H" in
    intro H ;
    lazymatch eval cbv -[IZR Rdiv] in (convert b) with
    | Ibnd ?l ?u =>
      lazymatch l with
      | Xreal ?l =>
        lazymatch u with
        | Xnan => change (l <= t /\ True)%R in H ; destruct H as [H _]
        | Xreal ?u => change (l <= t <= u)%R in H
        end
      | Xnan =>
        lazymatch u with
        | Xreal ?u => change (True /\ t <= u)%R in H ; destruct H as [_ H]
        | Xnan => fail "Xnan: Nothing known about" t
        end
      end
    | Inan => fail "Inan: Nothing known about" t
    end ;
    revert H
  end.

Ltac do_reduction nocheck native :=
  clear ;
  lazymatch nocheck with
  | true =>
    match native with
    | true => native_cast_no_check (eq_refl true)
    | false => vm_cast_no_check (eq_refl true)
    end
  | false =>
    (abstract
    match native with
    | true => native_cast_no_check (eq_refl true)
    | false => vm_cast_no_check (eq_refl true)
    end) ||
    fail "Numerical evaluation failed to conclude. You may want to adjust some parameters"
  end.

Ltac merge_vars fvar bvars :=
  let rec aux acc l :=
    match l with
    | ?v :: ?l' =>
      let acc := list_add v acc in
      aux acc l'
    | nil => acc
    end in
  lazymatch fvar with
  | Some ?x => aux (cons x nil) bvars
  | None => aux (@nil R) bvars
  end.

Ltac get_var_indices vars bvars :=
  let rec aux1 v i l :=
    lazymatch l with
    | v :: _ => i
    | _ :: ?l' => aux1 v (S i) l'
    end in
  let rec aux2 acc l :=
    lazymatch l with
    | ?v :: ?l' =>
      let i := aux1 v 0%nat vars in
      aux2 (cons i acc) l'
    | nil => acc
    end in
  aux2 (@nil nat) bvars.

Ltac hide_lhs :=
  lazymatch goal with
  | |- ?l = _ =>
    let l' := fresh "l" in
    set (l' := l)
  end.

Definition reify_var : R.
Proof. exact 0%R. Qed.

Ltac get_RInt_vars y i f :=
  let fapp := eval cbv beta in (f reify_var) in
  let vars := constr:(reify_var :: @nil R) in
  let vars := get_vars fapp vars in
  let vars := match get_vars fapp vars with reify_var :: ?vars => vars end in
  let vars := constr:(i :: vars) in
  let vars := match get_vars y vars with i :: ?vars => vars end in
  vars.

Ltac reify_RInt y f u v :=
  let i := constr:(RInt f u v) in
  let vars := get_RInt_vars y i f in
  let vars := get_vars u vars in
  let vars := get_vars v vars in
  reify_partial y (i :: vars) ;
  intros <- ;
  erewrite <- RInt_ext by (
    let t := fresh "t" in
    intros t _ ; hide_lhs ;
    let fapp := eval cbv beta in (f t) in
    reify_partial fapp (t :: vars) ;
    exact (fun H => H)) ;
  reify_partial u vars ;
  intros <- ;
  reify_partial v vars ;
  intros <- ;
  find_hyps vars.

Ltac reify_RInt_gen_infty y fm u :=
  let i := constr:(RInt_gen fm (at_point u) (Rbar_locally p_infty)) in
  let f :=
    lazymatch fm with
    | (fun x => @?f x * _)%R => f
    | (fun x => @?f x / _)%R => f
    | (fun x => @?f x * / _)%R => f
    | _ => fail "Unsupported integrand"
    end in
  let vars := get_RInt_vars y i f in
  let vars := get_vars u vars in
  reify_partial y (i :: vars) ;
  intros <- ;
  erewrite <- RInt_gen_ext_eq by (
    let t := fresh "t" in
    intros t ; hide_lhs ;
    apply (f_equal (fun x => Rmult x _)) ;
    let fapp := eval cbv beta in (f t) in
    reify_partial fapp (t :: vars) ;
    exact (fun H => H)) ;
  reify_partial u vars ;
  intros <- ;
  find_hyps vars.

Ltac reify_RInt_gen_zero y fm v :=
  let i := constr:(RInt_gen fm (at_right 0) (at_point v)) in
  let f :=
    lazymatch fm with
    | (fun x => @?f x * _)%R => f
    | (fun x => @?f x / _)%R => f
    | (fun x => @?f x * / _)%R => f
    | _ => fail "Unsupported integrand"
    end in
  let vars := get_RInt_vars y i f in
  let vars := get_vars v vars in
  reify_partial y (i :: vars) ;
  intros <- ;
  erewrite <- RInt_gen_ext_eq by (
    let t := fresh "t" in
    intros t ; hide_lhs ;
    apply (f_equal (fun x => Rmult x _)) ;
    let fapp := eval cbv beta in (f t) in
    reify_partial fapp (t :: vars) ;
    exact (fun H => H)) ;
  reify_partial v vars ;
  intros <- ;
  find_hyps vars.

End Private.

Module IntervalTacticAux (F : FloatOps with Definition sensible_format := true).

Module I := FloatIntervalFull F.
Module J := IntervalExt I.
Module F' := FloatExt F.
Module A := IntervalAlgos I.
Module T := Tree.Bnd I.
Module R := Reify.Bnd I.
Module BI := BertrandInterval I.
Module IR := IntegralRefiner I.
Module IT := IntegralTaylor I.
Module IU := IntegralTactic I.

Definition compute_inputs prec hyps consts :=
  R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts.

Theorem app_merge_hyps_eval_bnd :
  forall prec vars hyps consts,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  A.contains_all (compute_inputs prec hyps consts) (vars ++ map (fun c => eval c nil) consts).
Proof.
intros prec vars hyps consts He.
unfold compute_inputs.
revert vars He.
induction (R.merge_hyps prec hyps) as [|h t IH].
  intros [|vars]. 2: easy.
  intros _.
  simpl.
  split.
    now rewrite 2!map_length.
  intros n.
  rewrite (nth_map (Evar 0)).
  destruct le_lt_dec as [H|H].
    now rewrite I.nai_correct.
  rewrite (nth_map_lt (Evar 0)) by easy.
  apply T.eval_bnd_correct.
intros [|v vars].
  easy.
simpl.
intros [H1 H2].
apply A.contains_all_cons with (2 := H1).
now apply IH.
Qed.

Theorem eval_bisect_aux :
  forall prec depth idx vars hyps prog consts g fi,
  ( forall xi x, A.contains_all xi x ->
    contains (I.convert (fi xi)) (Xreal (nth 0 (eval_real prog x) 0)) ) ->
  A.bisect (compute_inputs prec hyps consts) idx (fun xi => R.eval_goal_bnd prec g (fi xi)) depth = true ->
  eval_hyps hyps vars (eval_goal g (eval_real' prog vars consts)).
Proof.
intros prec depth idx vars hyps prog consts g fi Hfi H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply A.bisect_correct with (P := fun x => eval_goal g (nth 0 (eval_real prog x) 0)) (2 := H).
- intros x xi Ix.
  apply (R.eval_goal_bnd_correct prec).
  now apply Hfi.
- now apply app_merge_hyps_eval_bnd.
Qed.

Theorem eval_bisect_contains_aux :
  forall prec depth idx vars hyps prog consts b fi,
  ( forall xi x, A.contains_all xi x ->
    contains (I.convert (fi xi)) (Xreal (nth 0 (eval_real prog x) 0)) ) ->
  A.bisect (compute_inputs prec hyps consts) idx (fun xi => I.subset (fi xi) b) depth = true ->
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth idx vars hyps prog consts b fi Hfi H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply A.bisect_correct with (P := fun x => contains (I.convert b) (Xreal (nth 0 (eval_real prog x) 0))) (2 := H).
- intros x xi Ix H''.
  eapply subset_contains.
  apply I.subset_correct, H''.
  now apply Hfi.
- now apply app_merge_hyps_eval_bnd.
Qed.

Definition eval_bisect_fun prec prog xi :=
  nth 0 (A.BndValuator.eval prec prog xi) I.nai.

Definition eval_bisect prec depth idx hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => R.eval_goal_bnd prec g (eval_bisect_fun prec prog xi)) depth.

Theorem eval_bisect_correct :
  forall prec depth idx vars hyps prog consts g,
  eval_bisect prec depth idx hyps prog consts g = true ->
  eval_hyps hyps vars (eval_goal g (eval_real' prog vars consts)).
Proof.
intros prec depth idx vars hyps prog consts g H.
apply eval_bisect_aux with (2 := H).
intros xi x Ix.
now apply A.BndValuator.eval_correct'.
Qed.

Definition eval_bisect_contains prec depth idx hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => I.subset (eval_bisect_fun prec prog xi) b) depth.

Theorem eval_bisect_contains_correct :
  forall prec depth idx vars hyps prog consts b,
  eval_bisect_contains prec depth idx hyps prog consts b = true ->
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth idx vars hyps prog consts b H.
apply eval_bisect_contains_aux with (2 := H).
intros xi x Ix.
now apply A.BndValuator.eval_correct'.
Qed.

Definition eval_bisect_plain prec depth extend idx hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  A.lookup (eval_bisect_fun prec prog) bounds idx extend depth.

Definition eval_bisect_diff_fun prec prog xi :=
  match xi with
  | nil => I.nai
  | xi :: li => A.DiffValuator.eval prec prog li 0 xi
  end.

Definition eval_bisect_diff prec depth idx hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => R.eval_goal_bnd prec g (eval_bisect_diff_fun prec prog xi)) depth.

Theorem eval_bisect_diff_correct :
  forall prec depth idx vars hyps prog consts g,
  eval_bisect_diff prec depth idx hyps prog consts g = true ->
  eval_hyps hyps vars (eval_goal g (eval_real' prog vars consts)).
Proof.
intros prec depth idx vars hyps prog consts g H.
apply eval_bisect_aux with (2 := H).
intros xi x Ix.
destruct xi as [|xi li].
  easy.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.DiffValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_contains_diff prec depth idx hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => I.subset (eval_bisect_diff_fun prec prog xi) b) depth.

Theorem eval_bisect_contains_diff_correct :
  forall prec depth idx vars hyps prog consts b,
  eval_bisect_contains_diff prec depth idx hyps prog consts b = true ->
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth idx vars hyps prog consts b H.
apply eval_bisect_contains_aux with (2 := H).
intros xi x Ix.
destruct xi as [|xi li].
  easy.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.DiffValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_diff_plain prec depth extend idx hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  A.lookup (eval_bisect_diff_fun prec prog) bounds idx extend depth.

Definition eval_bisect_taylor_fun prec deg prog xi :=
  match xi with
  | nil => I.nai
  | xi :: li =>
    let li := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const li in
    A.TaylorValuator.TM.eval (prec, deg)
      (nth 0 (A.TaylorValuator.eval prec deg xi prog li) A.TaylorValuator.TM.dummy) xi xi
  end.

Definition eval_bisect_taylor prec deg depth idx hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => R.eval_goal_bnd prec g (eval_bisect_taylor_fun prec deg prog xi)) depth.

Theorem eval_bisect_taylor_correct :
  forall prec deg depth idx vars hyps prog consts g,
  eval_bisect_taylor prec deg depth idx hyps prog consts g = true ->
  eval_hyps hyps vars (eval_goal g (eval_real' prog vars consts)).
Proof.
intros prec deg depth idx vars hyps prog consts g H.
apply eval_bisect_aux with (2 := H).
intros xi x Ix.
destruct xi as [|xi li].
  easy.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.TaylorValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_contains_taylor prec deg depth idx hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => I.subset (eval_bisect_taylor_fun prec deg prog xi) b) depth.

Theorem eval_bisect_contains_taylor_correct :
  forall prec deg depth idx vars hyps prog consts b,
  eval_bisect_contains_taylor prec deg depth idx hyps prog consts b = true ->
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec deg depth idx vars hyps prog consts b H.
apply eval_bisect_contains_aux with (2 := H).
intros xi x Ix.
destruct xi as [|xi li].
  easy.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.TaylorValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_taylor_plain prec deg depth extend idx hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  A.lookup (eval_bisect_taylor_fun prec deg prog) bounds idx extend depth.

Definition eval_RInt_init prec deg hyps pf pu pv cf cu cv :=
  let fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai in
  let ui :=
    let bounds := hyps ++ map (T.eval_bnd prec) cu in
    nth 0 (A.BndValuator.eval prec pu bounds) I.nai in
  let vi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cv in
    nth 0 (A.BndValuator.eval prec pv bounds) I.nai in
  let cb := fun x =>
    match x with IR.IBu => ui | IR.IBv => vi | IR.IBp x => I.singleton x end in
  let mid := fun u v =>
    let u := cb u in
    let v := cb v in
    I.midpoint (I.join u v) in
  let Fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun u v =>
      let u := cb u in
      let v := cb v in
      let xi := I.join u v in
      let gi :=
        A.TaylorValuator.TM.get_tm (prec, deg) xi
          (nth 0 (A.TaylorValuator.eval prec deg xi pf (A.TaylorValuator.TM.var :: bounds))
            A.TaylorValuator.TM.dummy) in
      IT.taylor_integral_naive_intersection prec fi gi xi u v in
  (mid, Fi).

Lemma contains_RInt :
  forall prec deg limit check vars hyps pf pu pv cf cu cv,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  no_floor_prog pf = true ->
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_init prec deg hyps pf pu pv cf cu cv in
  contains (I.convert (IR.bisect prec limit mid Fi check))
    (Xreal (RInt (fun t => Prog.eval_real' pf (t :: vars) cf)
      (Prog.eval_real' pu vars cu) (Prog.eval_real' pv vars cv))).
Proof.
intros prec deg limit check vars hyps pf pu pv cf cu cv H' Hp.
unfold eval_RInt_init, Prog.eval_real'.
simpl.
fold (compute_inputs prec hyps cu).
fold (compute_inputs prec hyps cv).
assert (Hcu := app_merge_hyps_eval_bnd prec _ _ cu H').
assert (Hcv := app_merge_hyps_eval_bnd prec _ _ cv H').
generalize (A.BndValuator.eval_correct' prec pv _ _ Hcv 0).
generalize (A.BndValuator.eval_correct' prec pu _ _ Hcu 0).
generalize (nth 0 (A.BndValuator.eval prec pv (compute_inputs prec hyps cv)) I.nai).
generalize (nth 0 (A.BndValuator.eval prec pu (compute_inputs prec hyps cu)) I.nai).
generalize (nth 0 (Prog.eval_real pv (vars ++ map (fun c => eval c nil) cv)) 0%R).
generalize (nth 0 (Prog.eval_real pu (vars ++ map (fun c => eval c nil) cu)) 0%R).
clear -H' Hp.
intros u v ui vi Hu Hv.
apply IR.contains_RInt_valid.
apply IR.bisect_correct ; [ typeclasses eauto .. | idtac ].
intros u' v'.
set (cbu := match u' with IR.IBu => ui | IR.IBv => vi | IR.IBp x => I.singleton x end).
set (cbv := match v' with IR.IBu => ui | IR.IBv => vi | IR.IBp x => I.singleton x end).
fold (compute_inputs prec hyps cf).
match goal with
| |- IR.valid _ _ _ _ _ ?fi =>
  let fi' := eval pattern cbu, cbv in fi in
  change fi with fi'
end.
apply IR.valid_at_point ; try easy.
apply (app_merge_hyps_eval_bnd prec _ _ cf) in H'.
clear -H' Hp.
intros ui vi u v Hu Hv.
set (i := IT.taylor_integral_naive_intersection _ _ _ _ _ _).
apply RInt_helper.
intros Hi.
assert (ex_RInt (fun t => nth 0 (Prog.eval_real pf (t :: vars ++ map (fun c => eval c nil) cf)) 0%R) u v) as [I HI].
  apply (A.BndValuator.ex_RInt_eval prec) with (xi := I.join ui vi) (1 := H') (2 := Hp).
    apply contains_connected.
    apply Rmin_case ; apply I.join_correct.
    now left.
    now right.
    apply Rmax_case ; apply I.join_correct.
    now left.
    now right.
  contradict Hi.
  unfold i, IT.taylor_integral_naive_intersection. clear i.
  rewrite I.real_correct.
  destruct (I.convert (I.mul _ _ _)) as [|il iu] eqn:Hm.
    easy.
  exfalso.
  now rewrite I.mul_propagate_r in Hm.
exists I.
apply (conj HI).
rewrite <- is_RInt_unique with (1 := HI).
apply IT.taylor_integral_naive_intersection_correct ; cycle 2.
  now exists I.
  exact Hu.
  exact Hv.
  apply I.join_correct.
  now left.
  apply I.join_correct.
  now right.
  intros xi x Ix.
  now apply A.BndValuator.eval_correct_ext'.
apply A.TaylorValuator.TM.get_tm_correct ; cycle 1.
  exists u.
  apply I.join_correct.
  now left.
now apply A.TaylorValuator.eval_correct_aux'.
Qed.

Definition check_goal prec hyps pg cg g :=
  let bounds := hyps ++ map (T.eval_bnd prec) cg in
  fun b =>
    let yi := nth 0 (A.BndValuator.eval prec pg (b :: bounds)) I.nai in
    R.eval_goal_bnd prec g yi.

Definition eval_RInt prec deg limit hyps pg pf pu pv cg cf cu cv g :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_init prec deg hyps pf pu pv cf cu cv in
  let check := check_goal prec hyps pg cg g in
  check (IR.bisect prec limit mid Fi check).

Theorem eval_RInt_correct :
  forall prec deg limit vars hyps pg pf pu pv cg cf cu cv g,
  no_floor_prog pf = true ->
  eval_RInt prec deg limit hyps pg pf pu pv cg cf cu cv g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt (fun t => Prog.eval_real' pf (t :: vars) cf)
        (Prog.eval_real' pu vars cu) (Prog.eval_real' pv vars cv)) :: vars) cg)).
Proof.
intros prec deg limit vars hyps pg pf pu pv cg cf cu cv g Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
unfold eval_real'.
simpl.
fold (compute_inputs prec hyps cg).
apply A.BndValuator.eval_correct_ext'.
now apply app_merge_hyps_eval_bnd.
now apply contains_RInt.
Qed.

Definition eval_RInt_contains prec deg limit hyps pf pu pv cf cu cv b :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_init prec deg hyps pf pu pv cf cu cv in
  let check yi := I.subset yi b in
  check (IR.bisect prec limit mid Fi check).

Theorem eval_RInt_contains_correct :
  forall prec deg limit vars hyps pf pu pv cf cu cv b,
  no_floor_prog pf = true ->
  eval_RInt_contains prec deg limit hyps pf pu pv cf cu cv b = true ->
  eval_hyps hyps vars (
    contains (I.convert b) (Xreal
      (RInt (fun t => Prog.eval_real' pf (t :: vars) cf)
        (Prog.eval_real' pu vars cu) (Prog.eval_real' pv vars cv)))).
Proof.
intros prec deg limit vars hyps pf pu pv cf cu cv b Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
eapply subset_contains.
apply I.subset_correct.
apply H.
now apply contains_RInt.
Qed.

Definition check_width prec (w : F.type * bool) yi :=
  let yl := I.lower yi in
  let yu := I.upper yi in
  let (f, r) := w in
  let w := if r then F.mul_UP prec (F.midpoint yl yu) f else f in
  F'.le' (F.sub_UP prec (I.upper yi) (I.lower yi)) f.

Definition eval_RInt_plain prec deg limit hyps pf pu pv cf cu cv w :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_init prec deg hyps pf pu pv cf cu cv in
  IR.bisect prec limit mid Fi (check_width prec w).

Definition bertrand_prog alpha beta p :=
  let x := length p in
  app p (Prog.Unary (PowerInt alpha) x :: Prog.Unary Ln (S x) :: Prog.Unary (PowerInt (Z_of_nat beta)) 0 :: Prog.Binary Mul 2 0 :: Prog.Binary Mul 4 0 :: nil).

Lemma bertrand_prog_correct :
  forall alpha beta p c x,
  nth 0 (Prog.eval_real (bertrand_prog alpha beta p) (x :: c)) 0 =
  (nth 0 (Prog.eval_real p (x :: c)) 0 * (powerRZ x alpha * pow (ln x) beta)).
Proof.
intros alpha beta p c x.
unfold Prog.eval_real, bertrand_prog.
rewrite 2!Prog.rev_formula.
rewrite rev_app_distr.
simpl.
replace (nth (length p) _ _) with x.
now rewrite <- pow_powerRZ.
rewrite <- rev_length.
now induction (rev p) as [|h t].
Qed.

Definition c1 := F.fromZ 1.

Definition bertrand_infty_interval alpha beta prec ui :=
  if F'.le' c1 (I.lower ui) then
    BI.f_int_fast prec ui alpha beta
  else I.nai.

Definition bertrand_zero_interval alpha beta prec vi :=
  if andb (F'.lt' F.zero (I.lower vi)) (F'.le' (I.upper vi) c1) then
    BI.f0eps_int prec vi alpha beta
  else I.nai.

Definition invxln_prog beta p :=
  let x := length p in
  app p (Prog.Unary Ln x :: Prog.Unary (PowerInt (Z_of_nat (S (S beta)))) 0 :: Prog.Binary Mul (S (S x)) 0 :: Prog.Binary Div 3 0 :: nil).

Lemma invxln_prog_correct :
  forall beta p c x,
  nth 0 (Prog.eval_real (invxln_prog beta p) (x :: c)) 0 =
  (nth 0 (Prog.eval_real p (x :: c)) 0 / (x * pow (ln x) (S (S beta)))).
Proof.
intros beta p c x.
unfold Prog.eval_real, invxln_prog.
rewrite 2!Prog.rev_formula.
rewrite rev_app_distr.
simpl.
replace (nth (length p) _ _) with x.
now rewrite Pos2Nat.inj_succ, SuccNat2Pos.id_succ.
rewrite <- rev_length.
now induction (rev p) as [|h t].
Qed.

Definition invxln_interval beta prec ui :=
  if F'.lt' c1 (I.lower ui) then
    BI.f_neg_int prec ui (S beta)
  else I.nai.

(*Eval cbv -[ln exp powerRZ IZR] in Prog.eval_real (invxln_prog 2 (Prog.Unary Exp 0 :: nil)) (42%R :: nil).*)

Definition eval_RInt_gen_infty_init prec deg hyps (mi : F.precision -> I.type -> I.type) pf pfm pu cf cfm cu :=
  let fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai in
  let fmi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cfm in
    fun b => nth 0 (A.BndValuator.eval prec pfm (b :: bounds)) I.nai in
  let ui :=
    let bounds := hyps ++ map (T.eval_bnd prec) cu in
    nth 0 (A.BndValuator.eval prec pu bounds) I.nai in
  let mid u v :=
    match u, v with
    | IR.IBu, IR.IBv => I.midpoint (I.upper_extent ui)
    | IR.IBu, IR.IBp v => I.midpoint (I.join ui (I.singleton v))
    | IR.IBp u, IR.IBv => I.midpoint (I.upper_extent (I.singleton u))
    | IR.IBp u, IR.IBp v => I.midpoint (I.bnd u v)
    | _, _ => F.zero
    end in
  let Fi1 :=
    let bounds := hyps ++ map (T.eval_bnd prec) cfm in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun ui vi =>
      let xi := I.join ui vi in
      let gi :=
        A.TaylorValuator.TM.get_tm (prec, deg) xi
          (nth 0 (A.TaylorValuator.eval prec deg xi pfm (A.TaylorValuator.TM.var :: bounds))
            A.TaylorValuator.TM.dummy) in
      IT.taylor_integral_naive_intersection prec fmi gi xi ui vi in
  let Fi2 :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun ui =>
      let yi := fi (I.upper_extent ui) in
      if I.bounded yi then I.mul prec yi (mi prec ui) else I.nai in
  let Fi u v :=
    match u, v with
    | IR.IBu, IR.IBv => Fi2 ui
    | IR.IBu, IR.IBp v => Fi1 ui (I.singleton v)
    | IR.IBp u, IR.IBv => Fi2 (I.singleton u)
    | IR.IBp u, IR.IBp v => Fi1 (I.singleton u) (I.singleton v)
    | _, _ => I.nai
    end in
  (mid, Fi).

Lemma contains_RInt_gen_infty :
  forall prec deg limit check vars hyps mi mp mr pf pu cf cu,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  (forall yi ui f u, contains (I.convert ui) (Xreal u) ->
    (forall t, (u <= t)%R -> continuous f t) ->
    (forall t, (u <= t)%R -> contains (I.convert yi) (Xreal (f t))) ->
    I.bounded yi = true ->
    I.convert (mi prec ui) <> Inan ->
    exists I : R,
    is_RInt_gen (fun t : R => f t * mr t) (at_point u) (Rbar_locally p_infty) I /\
    contains (I.convert (I.mul prec yi (mi prec ui))) (Xreal I)) ->
  (forall c t, nth 0 (Prog.eval_real mp (t :: c)) 0 = nth 0 (Prog.eval_real pf (t :: c)) 0 * mr t)%R ->
  no_floor_prog mp = true ->
  no_floor_prog pf = true ->
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_infty_init prec deg hyps mi pf mp pu cf cf cu in
  contains (I.convert (IR.bisect prec limit mid Fi check))
    (Xreal (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * mr t)
      (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty))).
Proof.
intros prec deg limit check vars hyps mi mp mr pf pu cf cu H' Hf Hm1 Hm2 Hp.
unfold Prog.eval_real'.
simpl.
fold (compute_inputs prec hyps cu).
assert (Hcu := app_merge_hyps_eval_bnd prec _ _ cu H').
generalize (A.BndValuator.eval_correct' prec pu _ _ Hcu 0).
generalize (nth 0 (A.BndValuator.eval prec pu (compute_inputs prec hyps cu)) I.nai).
generalize (nth 0 (Prog.eval_real pu (vars ++ map (fun c => eval c nil) cu)) 0%R).
clear -H' Hf Hm1 Hm2 Hp.
intros u ui Hu.
apply IR.bisect_correct with (uf := at_point u) (vf := Rbar_locally p_infty) ;
  [ typeclasses eauto .. | idtac ].
intros u' v'.
fold (compute_inputs prec hyps cf).
set (bounds := compute_inputs prec hyps cf).
apply (app_merge_hyps_eval_bnd prec _ _ cf) in H'.
set (fi :=
  fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai).
set (fmi :=
  fun b => nth 0 (A.BndValuator.eval prec mp (b :: bounds)) I.nai).
set (Fi1 :=
  let bounds := map A.TaylorValuator.TM.const bounds in
  fun ui vi =>
    let xi := I.join ui vi in
    let gi :=
      A.TaylorValuator.TM.get_tm (prec, deg) xi
        (nth 0 (A.TaylorValuator.eval prec deg xi mp (A.TaylorValuator.TM.var :: bounds))
          A.TaylorValuator.TM.dummy) in
    IT.taylor_integral_naive_intersection prec fmi gi xi ui vi).
set (Fi2 :=
  let bounds := map A.TaylorValuator.TM.const bounds in
  fun ui =>
    let yi := fi (I.upper_extent ui) in
    if I.bounded yi then I.mul prec yi (mi prec ui) else I.nai).
apply IR.valid_at_mixed with (u := u) (v := Rbar_locally p_infty)
    (fi1 := Fi1) (fi2 := Fi2) (ui := ui) (u' := u') (v' := v').
- typeclasses eauto.
- exact Hu.
- clear -H' Hf Hm1 Hm2 Hp.
  intros ui vi u v Hu Hv.
  apply RInt_helper.
  intros Hi.
  assert (ex_RInt (fun t => nth 0 (Prog.eval_real pf (t :: vars ++ map (fun c => eval c nil) cf)) 0%R * mr t) u v) as [I HI].
    eapply ex_RInt_ext.
      intros x _.
      apply Hm1.
    apply (A.BndValuator.ex_RInt_eval prec) with (xi := I.join ui vi) (1 := H').
      apply Hm2.
      apply contains_connected.
      apply Rmin_case ; apply I.join_correct.
      now left.
      now right.
      apply Rmax_case ; apply I.join_correct.
      now left.
      now right.
    contradict Hi.
    unfold Fi1, IT.taylor_integral_naive_intersection, fmi. clear -Hi.
    rewrite I.real_correct.
    destruct (I.convert (I.mul _ _ _)) as [|il iu] eqn:Hm.
      easy.
    exfalso.
    eapply I.mul_propagate_r in Hi.
    fold bounds in Hi.
    now rewrite Hm in Hi.
  exists I.
  apply (conj HI).
  rewrite <- is_RInt_unique with (1 := HI).
  apply IT.taylor_integral_naive_intersection_correct ; cycle 2.
    now exists I.
    exact Hu.
    exact Hv.
    apply I.join_correct.
    now left.
    apply I.join_correct.
    now right.
    intros xi x Hx.
    rewrite <- Hm1.
    now apply A.BndValuator.eval_correct_ext'.
  apply A.TaylorValuator.TM.get_tm_correct ; cycle 1.
    exists u.
    apply I.join_correct.
    now left.
  eapply A.TaylorValuator.TM.approximates_ext.
  intros x.
  rewrite <- Hm1.
  easy.
  now apply A.TaylorValuator.eval_correct_aux'.
- clear -H' Hp Hf.
  intros ui u Hu.
  apply RInt_gen_helper ; [typeclasses eauto .. | idtac].
  unfold Fi2.
  destruct I.bounded eqn:Hb ; cycle 1.
    now rewrite I.nai_correct.
  intros Hi.
  apply Hf with (1 := Hu) (4 := Hb).
  + intros t Ht.
    apply A.BndValuator.continuous_eval with (prec := prec) (xi := I.upper_extent ui) (1 := H') (2 := Hp).
    now apply I.upper_extent_correct with (1 := Hu).
    change (I.convert (fi (I.upper_extent ui)) <> Inan).
    contradict Hi.
    now apply I.mul_propagate_l.
  + intros t Ht.
    apply A.BndValuator.eval_correct_ext' with (1 := H').
    now apply I.upper_extent_correct with (1 := Hu).
  + contradict Hi.
    now apply I.mul_propagate_r.
Qed.

Definition eval_RInt_gen_infty prec deg limit hyps mi pg pf pfm pu cg cf cfm cu g :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_infty_init prec deg hyps mi pf pfm pu cf cfm cu in
  let check := check_goal prec hyps pg cg g in
  check (IR.bisect prec limit mid Fi check).

Definition eval_RInt_gen_infty_contains prec deg limit hyps mi pf pfm pu cf cfm cu b :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_infty_init prec deg hyps mi pf pfm pu cf cfm cu in
  let check yi := I.subset yi b in
  check (IR.bisect prec limit mid Fi check).

Definition eval_RInt_gen_infty_plain prec deg limit hyps mi pf pfm pu cf cfm cu w :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_infty_init prec deg hyps mi pf pfm pu cf cfm cu in
  IR.bisect prec limit mid Fi (check_width prec w).

Lemma contains_RInt_gen_infty_bertrand :
  forall prec deg limit check vars hyps alpha beta pf pu cf cu,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  (alpha < -1)%Z ->
  no_floor_prog pf = true ->
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_infty_init prec deg hyps (bertrand_infty_interval alpha beta) pf (bertrand_prog alpha beta pf) pu cf cf cu in
  contains (I.convert (IR.bisect prec limit mid Fi check))
    (Xreal (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * (powerRZ t alpha * pow (ln t) beta))
      (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty))).
Proof.
intros prec deg limit check vars hyps alpha beta pf pu cf cu H' Halpha Hp.
apply contains_RInt_gen_infty ; cycle 2.
- apply bertrand_prog_correct.
- unfold bertrand_prog, no_floor_prog in Hp |- *.
  rewrite <- fold_left_rev_right.
  rewrite rev_app_distr.
  simpl.
  rewrite fold_left_rev_right.
  now rewrite Hp.
- exact Hp.
- exact H'.
- intros fi ui f u Hu Hc Hf Hb.
  unfold bertrand_infty_interval, c1.
  destruct F'.le' eqn:Hul ; cycle 1.
    now rewrite I.nai_correct.
  intros _.
  assert (Hu': (1 <= u)%R).
    apply F'.le'_correct in Hul.
    rewrite F.fromZ_correct in Hul by easy.
    rewrite I.lower_correct in Hul by now exists u.
    destruct (I.convert ui) as [|[|ul] ur] ; try easy.
    now apply Rle_trans with (2 := proj1 Hu).
  eapply IU.integral_interval_mul_infty with (1 := Hu) (2 := Hf) (3 := Hb) (4 := Hc).
  + intros x Hx.
    assert (Hx': (0 < x)%R).
      apply Rlt_le_trans with (1 := Rlt_0_1).
      now apply Rle_trans with u.
    apply @continuous_mult.
    apply @ex_derive_continuous.
    apply ex_derive_powerRZ.
    right.
    now apply Rgt_not_eq.
    apply @ex_derive_continuous.
    apply ex_derive_pow.
    eexists.
    now apply is_derive_ln.
  + intros x Hx.
    apply Stdlib.Rmult_le_pos_pos.
    apply powerRZ_le.
    lra.
    apply pow_le.
    rewrite <- ln_1.
    apply ln_le.
    apply Rlt_0_1.
    now apply Rle_trans with u.
  + apply f_lim_correct with (2 := Halpha).
    now apply Rlt_le_trans with (1 := Rlt_0_1).
  + apply BI.f_int_fast_correct.
    exact Hu.
    now apply Rlt_le_trans with (1 := Rlt_0_1).
    now apply Zlt_not_eq.
Qed.

Theorem eval_RInt_gen_infty_bertrand :
  forall prec deg limit vars hyps alpha beta pg pf pu cg cf cu g,
  (alpha < -1)%Z ->
  no_floor_prog pf = true ->
  eval_RInt_gen_infty prec deg limit hyps (bertrand_infty_interval alpha beta) pg pf (bertrand_prog alpha beta pf) pu cg cf cf cu g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * (powerRZ t alpha * pow (ln t) beta))
        (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty)) :: vars) cg)).
Proof.
intros prec deg limit vars hyps alpha beta pg pf pu cg cf cu g Halpha Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
unfold eval_real'.
simpl.
fold (compute_inputs prec hyps cg).
apply A.BndValuator.eval_correct_ext'.
now apply app_merge_hyps_eval_bnd.
now apply contains_RInt_gen_infty_bertrand.
Qed.

Theorem eval_RInt_gen_infty_contains_bertrand :
  forall prec deg limit vars hyps alpha beta pf pu cf cu b,
  (alpha < -1)%Z ->
  no_floor_prog pf = true ->
  eval_RInt_gen_infty_contains prec deg limit hyps (bertrand_infty_interval alpha beta) pf (bertrand_prog alpha beta pf) pu cf cf cu b = true ->
  eval_hyps hyps vars (
    contains (I.convert b) (Xreal
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * (powerRZ t alpha * pow (ln t) beta))
        (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty)))).
Proof.
intros prec deg limit vars hyps alpha beta pf pu cf cu b Halpha Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
eapply subset_contains.
apply I.subset_correct.
apply H.
now apply contains_RInt_gen_infty_bertrand.
Qed.

Lemma contains_RInt_gen_infty_invxln :
  forall prec deg limit check vars hyps beta pf pu cf cu,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  no_floor_prog pf = true ->
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_infty_init prec deg hyps (invxln_interval beta) pf (invxln_prog beta pf) pu cf cf cu in
  contains (I.convert (IR.bisect prec limit mid Fi check))
    (Xreal (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf / (t * pow (ln t) (S (S beta))))
      (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty))).
Proof.
intros prec deg limit check vars hyps beta pf pu cf cu H' Hp.
apply contains_RInt_gen_infty ; cycle 2.
- apply invxln_prog_correct.
- unfold invxln_prog, no_floor_prog in Hp |- *.
  rewrite <- fold_left_rev_right.
  rewrite rev_app_distr.
  simpl.
  rewrite fold_left_rev_right.
  now rewrite Hp.
- exact Hp.
- exact H'.
- intros fi ui f u Hu Hc Hf Hb.
  unfold invxln_interval, c1.
  destruct F'.lt' eqn:Hul ; cycle 1.
    now rewrite I.nai_correct.
  intros _.
  assert (Hu': (1 < u)%R).
    apply F'.lt'_correct in Hul.
    rewrite F.fromZ_correct in Hul by easy.
    rewrite I.lower_correct in Hul by now exists u.
    destruct (I.convert ui) as [|[|ul] ur] ; try easy.
    now apply Rlt_le_trans with (2 := proj1 Hu).
  eapply IU.integral_interval_mul_infty with (1 := Hu) (2 := Hf) (3 := Hb) (4 := Hc).
  + intros x Hx.
    assert (Hx': (1 < x)%R).
      now apply Rlt_le_trans with u.
    apply (continuous_f_neg x (S (S beta))).
    now apply Rlt_trans with (1 := Rlt_0_1).
    now apply Rgt_not_eq.
  + intros x Hx.
    apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat.
    lra.
    apply (pow_lt (ln x) (S (S beta))).
    rewrite <- ln_1.
    apply ln_increasing.
    apply Rlt_0_1.
    now apply Rlt_le_trans with u.
  + now apply (f_neg_correct_RInt_gen_a_infty u (S beta)).
  + now apply BI.f_neg_int_correct.
Qed.

Theorem eval_RInt_gen_infty_invxln :
  forall prec deg limit vars hyps beta pg pf pu cg cf cu g,
  no_floor_prog pf = true ->
  eval_RInt_gen_infty prec deg limit hyps (invxln_interval beta) pg pf (invxln_prog beta pf) pu cg cf cf cu g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf / (t * pow (ln t) (S (S beta))))
        (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty)) :: vars) cg)).
Proof.
intros prec deg limit vars hyps beta pg pf pu cg cf cu g Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
unfold eval_real'.
simpl.
fold (compute_inputs prec hyps cg).
apply A.BndValuator.eval_correct_ext'.
now apply app_merge_hyps_eval_bnd.
now apply contains_RInt_gen_infty_invxln.
Qed.

Theorem eval_RInt_gen_infty_contains_invxln :
  forall prec deg limit vars hyps beta pf pu cf cu b,
  no_floor_prog pf = true ->
  eval_RInt_gen_infty_contains prec deg limit hyps (invxln_interval beta) pf (invxln_prog beta pf) pu cf cf cu b = true ->
  eval_hyps hyps vars (
    contains (I.convert b) (Xreal
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf / (t * pow (ln t) (S (S beta))))
        (at_point (Prog.eval_real' pu vars cu)) (Rbar_locally p_infty)))).
Proof.
intros prec deg limit vars hyps beta pf pu cf cu b Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
eapply subset_contains.
apply I.subset_correct.
apply H.
now apply contains_RInt_gen_infty_invxln.
Qed.

Definition eval_RInt_gen_zero_init prec deg hyps (mi : I.precision -> I.type -> I.type) pf pfm pv cf cfm cv :=
  let fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai in
  let fmi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cfm in
    fun b => nth 0 (A.BndValuator.eval prec pfm (b :: bounds)) I.nai in
  let vi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cv in
    nth 0 (A.BndValuator.eval prec pv bounds) I.nai in
  let mid u v :=
    match u, v with
    | IR.IBu, IR.IBv => I.midpoint (I.join I.zero vi)
    | IR.IBu, IR.IBp v => I.midpoint (I.bnd F.zero v)
    | IR.IBp u, IR.IBv => I.midpoint (I.join (I.singleton u) vi)
    | IR.IBp u, IR.IBp v => I.midpoint (I.bnd u v)
    | _, _ => F.zero
    end in
  let Fi1 :=
    let bounds := hyps ++ map (T.eval_bnd prec) cfm in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun ui vi =>
      let xi := I.join ui vi in
      let gi :=
        A.TaylorValuator.TM.get_tm (prec, deg) xi
          (nth 0 (A.TaylorValuator.eval prec deg xi pfm (A.TaylorValuator.TM.var :: bounds))
            A.TaylorValuator.TM.dummy) in
      IT.taylor_integral_naive_intersection prec fmi gi xi ui vi in
  let Fi2 :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := map A.TaylorValuator.TM.const bounds in
    fun vi =>
      let yi := fi (I.join I.zero vi) in
      if I.bounded yi then I.mul prec yi (mi prec vi) else I.nai in
  let Fi u v :=
    match u, v with
    | IR.IBu, IR.IBv => Fi2 vi
    | IR.IBu, IR.IBp v => Fi2 (I.singleton v)
    | IR.IBp u, IR.IBv => Fi1 (I.singleton u) vi
    | IR.IBp u, IR.IBp v => Fi1 (I.singleton u) (I.singleton v)
    | _, _ => I.nai
    end in
  (mid, Fi).

Lemma contains_RInt_gen_zero :
  forall prec deg limit check vars hyps mi mp mr pf pv cf cv,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  (forall yi vi f v, contains (I.convert vi) (Xreal v) ->
    (forall t, (0 <= t <= v)%R -> continuous f t) ->
    (forall t, (0 <= t <= v)%R -> contains (I.convert yi) (Xreal (f t))) ->
    I.bounded yi = true ->
    I.convert (mi prec vi) <> Inan ->
    exists I : R,
    is_RInt_gen (fun t : R => f t * mr t) (at_right 0) (at_point v) I /\
    contains (I.convert (I.mul prec yi (mi prec vi))) (Xreal I)) ->
  (forall c t, nth 0 (Prog.eval_real mp (t :: c)) 0 = nth 0 (Prog.eval_real pf (t :: c)) 0 * mr t)%R ->
  no_floor_prog mp = true ->
  no_floor_prog pf = true ->
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_zero_init prec deg hyps mi pf mp pv cf cf cv in
  contains (I.convert (IR.bisect prec limit mid Fi check))
    (Xreal (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * mr t)
      (at_right 0) (at_point (Prog.eval_real' pv vars cv)))).
Proof.
intros prec deg limit check vars hyps mi mp mr pf pv cf cv H' Hf Hm1 Hm2 Hp.
unfold Prog.eval_real'.
simpl.
fold (compute_inputs prec hyps cv).
assert (Hcv := app_merge_hyps_eval_bnd prec _ _ cv H').
generalize (A.BndValuator.eval_correct' prec pv _ _ Hcv 0).
generalize (nth 0 (A.BndValuator.eval prec pv (compute_inputs prec hyps cv)) I.nai).
generalize (nth 0 (Prog.eval_real pv (vars ++ map (fun c => eval c nil) cv)) 0%R).
clear -H' Hf Hm1 Hm2 Hp.
intros v vi Hv.
apply IR.bisect_correct with (uf := at_right 0) (vf := at_point v) ;
  [ typeclasses eauto .. | idtac ].
intros u' v'.
fold (compute_inputs prec hyps cf).
apply (app_merge_hyps_eval_bnd prec _ _ cf) in H'.
set (bounds := compute_inputs prec hyps cf).
set (fi :=
  fun b => nth 0 (A.BndValuator.eval prec pf (b :: bounds)) I.nai).
set (fmi :=
  fun b => nth 0 (A.BndValuator.eval prec mp (b :: bounds)) I.nai).
set (Fi1 :=
  let bounds := map A.TaylorValuator.TM.const bounds in
  fun ui vi =>
    let xi := I.join ui vi in
    let gi :=
      A.TaylorValuator.TM.get_tm (prec, deg) xi
        (nth 0 (A.TaylorValuator.eval prec deg xi mp (A.TaylorValuator.TM.var :: bounds))
          A.TaylorValuator.TM.dummy) in
    IT.taylor_integral_naive_intersection prec fmi gi xi ui vi).
set (Fi2 :=
  let bounds := map A.TaylorValuator.TM.const bounds in
  fun vi =>
    let yi := fi (I.join I.zero vi) in
    if I.bounded yi then I.mul prec yi (mi prec vi) else I.nai).
apply IR.valid_at_mixed' with (u := at_right 0) (v := v)
    (fi1 := Fi1) (fi2 := Fi2) (vi := vi) (u' := u') (v' := v').
- typeclasses eauto.
- exact Hv.
- clear -H' Hf Hm1 Hm2 Hp.
  intros ui vi u v Hu Hv.
  apply RInt_helper.
  intros Hi.
  assert (ex_RInt (fun t => nth 0 (Prog.eval_real pf (t :: vars ++ map (fun c => eval c nil) cf)) 0%R * mr t) u v) as [I HI].
    eapply ex_RInt_ext.
      intros x _.
      apply Hm1.
    apply (A.BndValuator.ex_RInt_eval prec) with (xi := I.join ui vi) (1 := H').
      apply Hm2.
      apply contains_connected.
      apply Rmin_case ; apply I.join_correct.
      now left.
      now right.
      apply Rmax_case ; apply I.join_correct.
      now left.
      now right.
    contradict Hi.
    unfold Fi1, IT.taylor_integral_naive_intersection, fmi. clear -Hi.
    rewrite I.real_correct.
    destruct (I.convert (I.mul _ _ _)) as [|il iu] eqn:Hm.
      easy.
    exfalso.
    eapply I.mul_propagate_r in Hi.
    fold bounds in Hi.
    now rewrite Hm in Hi.
  exists I.
  apply (conj HI).
  rewrite <- is_RInt_unique with (1 := HI).
  apply IT.taylor_integral_naive_intersection_correct ; cycle 2.
    now exists I.
    exact Hu.
    exact Hv.
    apply I.join_correct.
    now left.
    apply I.join_correct.
    now right.
    intros xi x Hx.
    rewrite <- Hm1.
    now apply A.BndValuator.eval_correct_ext'.
  apply A.TaylorValuator.TM.get_tm_correct ; cycle 1.
    exists u.
    apply I.join_correct.
    now left.
  eapply A.TaylorValuator.TM.approximates_ext.
  intros x.
  rewrite <- Hm1.
  easy.
  now apply A.TaylorValuator.eval_correct_aux'.
- clear -H' Hp Hf.
  intros vi v Hv.
  apply RInt_gen_helper ; [typeclasses eauto .. | idtac].
  unfold Fi2.
  destruct I.bounded eqn:Hb ; cycle 1.
    now rewrite I.nai_correct.
  assert (Ht': forall t, (0 <= t <= v)%R -> contains (I.convert (I.join I.zero vi)) (Xreal t)).
    apply contains_connected.
    apply I.join_correct.
    left.
    rewrite I.zero_correct.
    split ; apply Rle_refl.
    apply I.join_correct.
    now right.
  intros Hi.
  apply Hf with (1 := Hv) (4 := Hb).
  + intros t Ht.
    apply A.BndValuator.continuous_eval with (prec := prec) (xi := I.join I.zero vi) (1 := H') (2 := Hp).
    now apply Ht'.
    change (I.convert (fi (I.join I.zero vi)) <> Inan).
    contradict Hi.
    now apply I.mul_propagate_l.
  + intros t Ht.
    apply A.BndValuator.eval_correct_ext' with (1 := H').
    now apply Ht'.
  + contradict Hi.
    now apply I.mul_propagate_r.
Qed.

Definition eval_RInt_gen_zero prec deg limit hyps mi pg pf pfm pv cg cf cfm cv g :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_zero_init prec deg hyps mi pf pfm pv cf cfm cv in
  let check := check_goal prec hyps pg cg g in
  check (IR.bisect prec limit mid Fi check).

Definition eval_RInt_gen_zero_contains prec deg limit hyps mi pf pfm pv cf cfm cv b :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_zero_init prec deg hyps mi pf pfm pv cf cfm cv in
  let check yi := I.subset yi b in
  check (IR.bisect prec limit mid Fi check).

Definition eval_RInt_gen_zero_plain prec deg limit hyps mi pf pfm pv cf cfm cv w :=
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_zero_init prec deg hyps mi pf pfm pv cf cfm cv in
  IR.bisect prec limit mid Fi (check_width prec w).

Lemma contains_RInt_gen_zero_bertrand :
  forall prec deg limit check vars hyps alpha beta pf pv cf cv,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  (-1 < alpha)%Z ->
  no_floor_prog pf = true ->
  let hyps := R.merge_hyps prec hyps in
  let (mid, Fi) := eval_RInt_gen_zero_init prec deg hyps (bertrand_zero_interval alpha beta) pf (bertrand_prog alpha beta pf) pv cf cf cv in
  contains (I.convert (IR.bisect prec limit mid Fi check))
    (Xreal (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * (powerRZ t alpha * pow (ln t) beta))
      (at_right 0) (at_point (Prog.eval_real' pv vars cv)))).
Proof.
intros prec deg limit check vars hyps alpha beta pf pv cf cv H' Halpha Hp.
apply contains_RInt_gen_zero ; cycle 2.
- apply bertrand_prog_correct.
- unfold bertrand_prog, no_floor_prog in Hp |- *.
  rewrite <- fold_left_rev_right.
  rewrite rev_app_distr.
  simpl.
  rewrite fold_left_rev_right.
  now rewrite Hp.
- exact Hp.
- exact H'.
- intros fi vi f v Hv Hc Hf Hb.
  unfold bertrand_zero_interval, c1.
  destruct F'.lt' eqn:Hvl ; cycle 1.
    cbv [andb].
    now rewrite I.nai_correct.
  destruct F'.le' eqn:Hvu ; cycle 1.
    cbv [andb].
    now rewrite I.nai_correct.
  intros _.
  assert (Hv': (0 < v)%R).
    apply F'.lt'_correct in Hvl.
    rewrite F.zero_correct in Hvl.
    rewrite I.lower_correct in Hvl by now exists v.
    destruct (I.convert vi) as [|[|vl] vr] ; try easy.
    now apply Rlt_le_trans with (2 := proj1 Hv).
  eapply IU.integral_interval_mul_zero with (1 := Hv') (2 := Hv) (3 := Hf) (4 := Hb) (5 := Hc).
  + intros x Hx.
    apply @continuous_mult.
    apply @ex_derive_continuous.
    apply ex_derive_powerRZ.
    right.
    now apply Rgt_not_eq.
    apply @ex_derive_continuous.
    apply ex_derive_pow.
    eexists.
    now apply is_derive_ln.
  + destruct (Zeven_odd_dec (Z.of_nat beta)) as [Hbeta|Hbeta] ; [left|right] ; intros x Hx.
      apply Rmult_le_pos_pos.
      now apply powerRZ_le.
      apply IT.TM.TMI.ZEven_pow_le.
      now apply Zeven_equiv.
    apply Rmult_le_pos_neg.
    now apply powerRZ_le.
    apply IT.TM.TMI.ZOdd_pow_le.
    now apply Zodd_equiv.
    rewrite <- ln_1.
    apply ln_le.
    apply Hx.
    apply Rle_trans with (1 := proj2 Hx).
    apply F'.le'_correct in Hvu.
    rewrite F.fromZ_correct in Hvu by easy.
    rewrite I.upper_correct in Hvu by now exists v.
    destruct (I.convert vi) as [|vr [|vu]] ; try easy.
    now apply Rle_trans with (1 := proj2 Hv).
  + now apply f0eps_lim_correct with (1 := Halpha).
  + apply BI.f0eps_correct ; try easy.
    now apply Zgt_not_eq.
Qed.

Theorem eval_RInt_gen_zero_bertrand :
  forall prec deg limit vars hyps alpha beta pg pf pv cg cf cv g,
  (-1 < alpha)%Z ->
  no_floor_prog pf = true ->
  eval_RInt_gen_zero prec deg limit hyps (bertrand_zero_interval alpha beta) pg pf (bertrand_prog alpha beta pf) pv cg cf cf cv g = true ->
  eval_hyps hyps vars (
    eval_goal g (Prog.eval_real' pg (
      (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * (powerRZ t alpha * pow (ln t) beta))
        (at_right 0) (at_point (Prog.eval_real' pv vars cv))) :: vars) cg)).
Proof.
intros prec deg limit vars hyps alpha beta pg pf pv cg cf cv g Halpha Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply (R.eval_goal_bnd_correct prec) with (2 := H).
unfold eval_real'.
simpl.
fold (compute_inputs prec hyps cg).
apply A.BndValuator.eval_correct_ext'.
now apply app_merge_hyps_eval_bnd.
now apply contains_RInt_gen_zero_bertrand.
Qed.

Theorem eval_RInt_gen_zero_contains_bertrand :
  forall prec deg limit vars hyps alpha beta pf pv cf cv b,
  (-1 < alpha)%Z ->
  no_floor_prog pf = true ->
  eval_RInt_gen_zero_contains prec deg limit hyps (bertrand_zero_interval alpha beta) pf (bertrand_prog alpha beta pf) pv cf cf cv b = true ->
  eval_hyps hyps vars (contains (I.convert b)
    (Xreal (RInt_gen (fun t => Prog.eval_real' pf (t :: vars) cf * (powerRZ t alpha * pow (ln t) beta))
       (at_right 0) (at_point (Prog.eval_real' pv vars cv))))).
Proof.
intros prec deg limit vars hyps alpha beta pf pv cf cv b Halpha Hp H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
eapply subset_contains.
apply I.subset_correct.
apply H.
now apply contains_RInt_gen_zero_bertrand.
Qed.

Import Private.

Definition extent e :=
  match e with
  | ie_none => fun v => v
  | ie_lower => I.lower_extent
  | ie_upper => I.upper_extent
  end.

Ltac do_interval fvar bvars prec degree depth native nocheck eval_tac :=
  let prec := eval vm_compute in (F.PtoP prec) in
  let vars := merge_vars fvar bvars in
  let idx := get_var_indices vars bvars in
  massage_goal ;
  reify_full vars ;
  lazymatch eval_tac with
  | itm_naive => apply (eval_bisect_correct prec depth idx)
  | itm_autodiff => apply (eval_bisect_diff_correct prec depth idx)
  | itm_taylor => apply (eval_bisect_taylor_correct prec degree depth idx)
  end ;
  do_reduction nocheck native.

Ltac do_instantiate i extend native yi :=
  let yi :=
    lazymatch native with
    | true => eval native_compute in (extend yi)
    | false => eval vm_compute in (extend yi)
    end in
  instantiate (i := yi).

Ltac do_interval_intro y extend fvar bvars prec degree depth native nocheck eval_tac :=
  let prec := eval vm_compute in (F.PtoP prec) in
  let extend := constr:(extent extend) in
  let vars := merge_vars fvar bvars in
  let idx := get_var_indices vars bvars in
  let i := fresh "__i" in
  evar (i : I.type) ;
  cut (contains (I.convert i) (Xreal y))%R ; cycle 1 ; [
    let vars := get_vars y vars in
    reify_partial y vars ;
    apply (eq_ind _ (fun z => contains (I.convert i) (Xreal z))) ;
    find_hyps vars ;
    lazymatch eval_tac with
    | itm_naive =>
      apply (eval_bisect_contains_correct prec depth idx) ;
      match goal with
      | |- _ ?hyps ?prog ?consts _ = true =>
        do_instantiate i extend native (eval_bisect_plain prec depth extend idx hyps prog consts)
      end
    | itm_autodiff =>
      apply (eval_bisect_contains_diff_correct prec depth idx) ;
      match goal with
      | |- _ ?hyps ?prog ?consts _ = true =>
        do_instantiate i extend native (eval_bisect_diff_plain prec depth extend idx hyps prog consts)
      end
    | itm_taylor =>
      apply (eval_bisect_contains_taylor_correct prec degree depth idx) ;
      match goal with
      | |- _ ?hyps ?prog ?consts _ = true =>
        do_instantiate i extend native (eval_bisect_taylor_plain prec degree depth extend idx hyps prog consts)
      end
    end ;
    do_reduction nocheck native
  | do_interval_generalize I.convert ; clear i ].

Ltac do_integral prec degree fuel native nocheck :=
  let prec := eval vm_compute in (F.PtoP prec) in
  massage_goal ;
  match goal with
  | |- eval_goal ?g' ?y =>
    let g := fresh "__goal" in
    set (g := g') ;
    lazymatch y with
    | context [RInt ?f ?u ?v] =>
      reify_RInt y f u v ;
      apply (eval_RInt_correct prec degree fuel) with (1 := eq_refl true)
    | context [RInt_gen ?fm (at_point ?u) (Rbar_locally p_infty)] =>
      reify_RInt_gen_infty y fm u ;
      lazymatch fm with
      | fun t => (_ / (t * ln t ^ _))%R =>
        apply (eval_RInt_gen_infty_invxln prec degree fuel) with (1 := eq_refl true)
      | fun t => (_ * / (t * ln t ^ _))%R =>
        apply (eval_RInt_gen_infty_invxln prec degree fuel) with (1 := eq_refl true)
      | fun t => (_ * (powerRZ t _ * ln t ^ _))%R =>
        apply (eval_RInt_gen_infty_bertrand prec degree fuel) with (1 := eq_refl Lt) (2 := eq_refl true)
      end
    | context [RInt_gen ?fm (at_right 0) (at_point ?v)] =>
      reify_RInt_gen_zero y fm v ;
      lazymatch fm with
      | fun t => (_ * (powerRZ t _ * ln t ^ _))%R =>
        apply (eval_RInt_gen_zero_bertrand prec degree fuel) with (1 := eq_refl Lt) (2 := eq_refl true)
      end
    | _ => fail "No integral recognized"
    end
  end ;
  do_reduction nocheck native.

Ltac do_integral_intro y extend prec degree fuel width native nocheck :=
  let prec := eval vm_compute in (F.PtoP prec) in
  let extend := constr:(extent extend) in
  let width :=
    match width with
    | (?p, ?b) => constr:((F.scale (F.fromZ 1) (F.ZtoS p), b))
    end in
  let i := fresh "__i" in
  evar (i : I.type) ;
  cut (contains (I.convert i) (Xreal y))%R ; cycle 1 ; [
    lazymatch y with
    | context [RInt ?f ?u ?v] =>
      reify_RInt y f u v ;
      apply (eval_RInt_contains_correct prec degree fuel) with (1 := eq_refl true) ;
      match goal with
      | |- _ ?hyps ?pf ?pu ?pv ?cf ?cu ?cv _ = true =>
        let yi := constr:(eval_RInt_plain prec degree fuel hyps pf pu pv cf cu cv width) in
        do_instantiate i extend native yi
      end
    | context [RInt_gen ?fm (at_point ?u) (Rbar_locally p_infty)] =>
      reify_RInt_gen_infty y fm u ;
      lazymatch fm with
      | fun t => (_ / (t * ln t ^ _))%R =>
        apply (eval_RInt_gen_infty_contains_invxln prec degree fuel) with (1 := eq_refl true)
      | fun t => (_ * / (t * ln t ^ _))%R =>
        apply (eval_RInt_gen_infty_contains_invxln prec degree fuel) with (1 := eq_refl true)
      | fun t => (_ * (powerRZ t _ * ln t ^ _))%R =>
        apply (eval_RInt_gen_infty_contains_bertrand prec degree fuel) with (1 := eq_refl Lt) (2 := eq_refl true)
      end ;
      match goal with
      | |- _ ?hyps ?mi ?pf ?pfm ?pu ?cf ?cfm ?cu _ = true =>
        let yi := constr:(eval_RInt_gen_infty_plain prec degree fuel hyps mi pf pfm pu cf cfm cu width) in
        do_instantiate i extend native yi
      end
    | context [RInt_gen ?fm (at_right 0) (at_point ?v)] =>
      reify_RInt_gen_zero y fm v ;
      lazymatch fm with
      | fun t => (_ * (powerRZ t _ * ln t ^ _))%R =>
        apply (eval_RInt_gen_zero_contains_bertrand prec degree fuel) with (1 := eq_refl Lt) (2 := eq_refl true)
      end ;
      match goal with
      | |- _ ?hyps ?mi ?pf ?pfm ?pv ?cf ?cfm ?cv _ = true =>
        let yi := constr:(eval_RInt_gen_zero_plain prec degree fuel hyps mi pf pfm pv cf cfm cv width) in
        do_instantiate i extend native yi
      end
    | _ => fail "No integral recognized"
    end ;
    do_reduction nocheck native
  | do_interval_generalize I.convert ; clear i ].

End IntervalTacticAux.

Require Tactic_float.

Module IntervalTactic (F : FloatOps with Definition sensible_format := true).

Import Private.

Module Private.

Module IT1 := IntervalTacticAux F.
Module IT2 := IntervalTacticAux Tactic_float.Float.

Ltac do_parse params depth :=
  let rec aux fvar bvars prec degree depth native nocheck itm params :=
    lazymatch params with
    | nil => constr:((fvar, bvars, prec, degree, depth, native, nocheck, itm))
    | cons (i_prec ?p) ?t => aux fvar bvars (Some p) degree depth native nocheck itm t
    | cons (i_degree ?d) ?t => aux fvar bvars prec d depth native nocheck itm t
    | cons (i_bisect ?x) ?t => aux fvar (cons x bvars) prec degree depth native nocheck itm t
    | cons (i_autodiff ?x) ?t => aux (Some x) bvars prec degree depth native nocheck itm_autodiff t
    | cons (i_taylor ?x) ?t => aux (Some x) bvars prec degree depth native nocheck itm_taylor t
    | cons (i_depth ?d) ?t => aux fvar bvars prec degree d native nocheck itm t
    | cons i_native_compute ?t => aux fvar bvars prec degree depth true nocheck itm t
    | cons i_delay ?t => aux fvar bvars prec degree depth native true itm t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@None R) (@nil R) (@None positive) 10%nat depth false false itm_naive params.

Ltac do_interval_parse params :=
  match do_parse params 15%nat with
  | (?fvar, ?bvars, ?prec, ?degree, ?depth, ?native, ?nocheck, ?itm) =>
    lazymatch prec with
    | Some ?p => IT1.do_interval fvar bvars p degree depth native nocheck itm
    | None => IT2.do_interval fvar bvars 53%positive degree depth native nocheck itm
    end
  end.

Ltac do_interval_intro_parse t extend params :=
  match do_parse params 5%nat with
  | (?fvar, ?bvars, ?prec, ?degree, ?depth, ?native, ?nocheck, ?itm) =>
    lazymatch prec with
    | Some ?p => IT1.do_interval_intro t extend fvar bvars p degree depth native nocheck itm
    | None => IT2.do_interval_intro t extend fvar bvars 53%positive degree depth native nocheck itm
    end
  end.

Ltac do_parse' params :=
  let rec aux prec degree fuel width native nocheck params :=
    lazymatch params with
    | nil => constr:((prec, degree, fuel, width, native, nocheck))
    | cons (i_prec ?p) ?t => aux (Some p) degree fuel width native nocheck t
    | cons (i_degree ?d) ?t => aux prec d fuel width native nocheck t
    | cons (i_fuel ?f) ?t => aux prec degree f width native nocheck t
    | cons (i_width ?w) ?t => aux prec degree fuel (w, false) native nocheck t
    | cons (i_relwidth ?w) ?t => aux prec degree fuel (Zneg w, true) native nocheck t
    | cons i_native_compute ?t => aux prec degree fuel width true nocheck t
    | cons i_delay ?t => aux prec degree fuel width native true t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@None positive) 10%nat 100%positive (Zneg 10, true) false false params.

Ltac do_integral_parse params :=
  match do_parse' params with
  | (?prec, ?degree, ?fuel, _, ?native, ?nocheck) =>
    lazymatch prec with
    | Some ?p => IT1.do_integral p degree fuel native nocheck
    | None => IT2.do_integral 53%positive degree fuel native nocheck
    end
  end.

Ltac do_integral_intro_parse y extend params :=
  match do_parse' params with
  | (?prec, ?degree, ?fuel, ?width, ?native, ?nocheck) =>
    lazymatch prec with
    | Some ?p => IT1.do_integral_intro y extend p degree fuel width native nocheck
    | None => IT2.do_integral_intro y extend 53%positive degree fuel width native nocheck
    end
  end.

End Private.

Import Private.

Tactic Notation "interval" :=
  do_interval_parse (@nil interval_tac_parameters).

Tactic Notation "interval" "with" constr(params) :=
  do_interval_parse ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "interval_intro" constr(t) :=
  do_interval_intro_parse t ie_none (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" :=
  do_interval_intro_parse t ie_upper (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "upper"  :=
  do_interval_intro_parse t ie_lower (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "with" constr(params) :=
  do_interval_intro_parse t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) :=
  do_interval_intro_parse t ie_upper ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) :=
  do_interval_intro_parse t ie_lower ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "as" simple_intropattern(H) :=
  do_interval_intro_parse t ie_none (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "as" simple_intropattern(H) :=
  do_interval_intro_parse t ie_upper (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "as" simple_intropattern(H)  :=
  do_interval_intro_parse t ie_lower (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t ie_upper ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t ie_lower ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "integral" :=
  do_integral_parse (@nil interval_tac_parameters).

Tactic Notation "integral" "with" constr(params) :=
  do_integral_parse ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "integral_intro" constr(t) :=
  do_integral_intro_parse t ie_none (@nil interval_tac_parameters) ; intro.

Tactic Notation "integral_intro" constr(t) "lower" :=
  do_integral_intro_parse t ie_upper (@nil interval_tac_parameters) ; intro.

Tactic Notation "integral_intro" constr(t) "upper"  :=
  do_integral_intro_parse t ie_lower (@nil interval_tac_parameters) ; intro.

Tactic Notation "integral_intro" constr(t) "with" constr(params) :=
  do_integral_intro_parse t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "integral_intro" constr(t) "lower" "with" constr(params) :=
  do_integral_intro_parse t ie_upper ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "integral_intro" constr(t) "upper" "with" constr(params) :=
  do_integral_intro_parse t ie_lower ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "integral_intro" constr(t) "as" simple_intropattern(H) :=
  do_integral_intro_parse t ie_none (@nil interval_tac_parameters) ; intros H.

Tactic Notation "integral_intro" constr(t) "lower" "as" simple_intropattern(H) :=
  do_integral_intro_parse t ie_upper (@nil interval_tac_parameters) ; intros H.

Tactic Notation "integral_intro" constr(t) "upper" "as" simple_intropattern(H)  :=
  do_integral_intro_parse t ie_lower (@nil interval_tac_parameters) ; intros H.

Tactic Notation "integral_intro" constr(t) "with" constr(params) "as" simple_intropattern(H) :=
  do_integral_intro_parse t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "integral_intro" constr(t) "lower" "with" constr(params) "as" simple_intropattern(H) :=
  do_integral_intro_parse t ie_upper ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "integral_intro" constr(t) "upper" "with" constr(params) "as" simple_intropattern(H) :=
  do_integral_intro_parse t ie_lower ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

End IntervalTactic.

Require Import Specific_bigint.
Require Import Specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.
Module IT := IntervalTactic SFBI2.
Export IT.
