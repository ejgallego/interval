(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2019, Inria

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

From Coq Require Import Reals Psatz.
From Flocq Require Import Raux.
From Coq Require Import List.

Require Import Xreal.
Require Import Interval.
Require Import Tree.
Require Import Prog.

Inductive hyp : Set :=
  | Hle (b l : bool) (v : expr)
  | Hge (b l : bool) (u : expr)
  | Hlele (l1 l2 : bool) (u v : expr)
  | Habsle (b l : bool) (v : expr).

Definition eval_hyp (h : hyp) (var : R) :=
  match h with
  | Hle true true v => (var <= eval v nil)%R
  | Hle true false v => (var < eval v nil)%R
  | Hle false true v => (eval v nil >= var)%R
  | Hle false false v => (eval v nil > var)%R
  | Hge true true u => (eval u nil <= var)%R
  | Hge true false u => (eval u nil < var)%R
  | Hge false true u => (var >= eval u nil)%R
  | Hge false false u => (var > eval u nil)%R
  | Hlele true true u v => (eval u nil <= var <= eval v nil)%R
  | Hlele true false u v => (eval u nil <= var < eval v nil)%R
  | Hlele false true u v => (eval u nil < var <= eval v nil)%R
  | Hlele false false u v => (eval u nil < var < eval v nil)%R
  | Habsle true true v => (Rabs var <= eval v nil)%R
  | Habsle true false v => (Rabs var < eval v nil)%R
  | Habsle false true v => (eval v nil >= Rabs var)%R
  | Habsle false false v => (eval v nil > Rabs var)%R
  end.

Fixpoint eval_hyps_aux (hyps : list hyp) (var : R) (g : Prop) :=
  match hyps with
  | hh :: th => eval_hyp hh var -> eval_hyps_aux th var g
  | nil => g
  end.

Fixpoint eval_hyps (hyps : list (list hyp)) (vars : list R) (g : Prop) :=
  match hyps, vars with
  | hh :: th, hv :: tv =>
    eval_hyps_aux hh hv (eval_hyps th tv g)
  | nil, nil => g
  | _, _ => True
  end.

Inductive gol : Set :=
  | Gle (b : bool) (v : expr)
  | Gge (b : bool) (u : expr)
  | Glele (u v : expr)
  | Gabsle (b : bool) (v : expr)
  | Glt (v : expr)
  | Ggt (u : expr)
  | Gne (b : bool) (u : expr).

Definition eval_goal (g : gol) (x : R) :=
  match g with
  | Gle true v => (x <= eval v nil)%R
  | Gle false v => (eval v nil >= x)%R
  | Gge true u => (eval u nil <= x)%R
  | Gge false u => (x >= eval u nil)%R
  | Glele u v => (eval u nil <= x <= eval v nil)%R
  | Gabsle true v => (Rabs x <= eval v nil)%R
  | Gabsle false v => (eval v nil >= Rabs x)%R
  | Glt v => (x < eval v nil)%R
  | Ggt u => (eval u nil < x)%R
  | Gne true u => (x <> eval u nil)
  | Gne false u => (eval u nil <> x)
  end.

Ltac massage_goal :=
  let aux a x t :=
    let a := reify a (@nil R) in
    (change (eval_goal (t a) x)) in
  match goal with
  | |- (Rabs ?x <= ?v)%R => aux v x (Gabsle true)
  | |- (?u <= ?x)%R => aux u x (Gge true)
  | |- (?x <= ?v)%R => aux v x (Gle true)
  | |- (?x >= ?u)%R => aux u x (Gge false)
  | |- (?v >= ?x)%R => aux v x (Gle false)
  | |- (?u <= ?x <= ?v)%R =>
    let u := reify u (@nil R) in
    aux v x (Glele u)
  | |- (?u < ?x)%R => aux u x Ggt
  | |- (?x > ?u)%R => aux u x Ggt
  | |- (?x < ?v)%R => aux v x Glt
  | |- (?v > ?x)%R => aux v x Glt
  | |- (?x <> ?u :>R) => aux u x (Gne true)
  | |- (?u <> ?x :>R) => aux u x (Gne false)
  | _ => fail "Goal is not an inequality with constant bounds"
  end.

Ltac find_hyps_aux x known cont :=
  let aux H u t :=
    let u := reify u (@nil R) in
    let k := constr:(cons (t u) known) in
    revert H ;
    find_hyps_aux x k cont in
  match goal with
  | H : (?u <= x <= ?v)%R |- _ =>
    let u := reify u (@nil R) in
    aux H v (Hlele true true u)
  | H : (?u <= x < ?v)%R |- _ =>
    let u := reify u (@nil R) in
    aux H v (Hlele true false u)
  | H : (?u < x <= ?v)%R |- _ =>
    let u := reify u (@nil R) in
    aux H v (Hlele false true u)
  | H : (?u < x < ?v)%R |- _ =>
    let u := reify u (@nil R) in
    aux H v (Hlele false false u)
  | H : (?u <= x)%R |- _ => aux H u (Hge true true)
  | H : (x >= ?u)%R |- _ => aux H u (Hge false true)
  | H : (x <= ?v)%R |- _ => aux H v (Hle true true)
  | H : (?v >= x)%R |- _ => aux H v (Hle false true)
  | H : (Rabs x <= ?v)%R |- _ => aux H v (Habsle true true)
  | H : (?v >= Rabs x)%R |- _ => aux H v (Habsle false true)
  | H : (?u < x)%R |- _ => aux H u (Hge true false)
  | H : (x > ?u)%R |- _ => aux H u (Hge false false)
  | H : (x < ?v)%R |- _ => aux H v (Hle true false)
  | H : (?v > x)%R |- _ => aux H v (Hle false false)
  | H : (Rabs x < ?v)%R |- _ => aux H v (Habsle true false)
  | H : (?v > Rabs x)%R |- _ => aux H v (Habsle false false)
  | _ =>
    cont known
  end.

Ltac find_hyps_aux2 vars cont :=
  match vars with
  | ?h :: ?t =>
    let cont' k :=
      let cont'' k' :=
        let k'' := constr:(cons k' k) in
        cont k'' in
      let k' := constr:(@nil hyp) in
      find_hyps_aux h k' cont'' in
    find_hyps_aux2 t cont'
  | @nil R =>
    let k := constr:(@nil (list hyp)) in
    cont k
  end.

Ltac find_hyps vars :=
  match goal with
  | |- ?g =>
    let cont k :=
      change (eval_hyps k vars g) ;
      clear in
    find_hyps_aux2 vars cont
  end ;
  match goal with
  | |- eval_hyps ?hyps' _ _ =>
    let hyps := fresh "__hyps" in
    set (hyps := hyps')
  end.

Ltac reify_partial y vars :=
  let expr' := reify y vars in
  let expr := fresh "__expr" in
  set (expr := expr') ;
  change y with (eval expr vars) ;
  generalize (extract_correct expr vars) ;
  let decomp := eval lazy in (extract expr (length vars)) in
  change (extract expr (length vars)) with decomp ;
  cbv iota beta ;
  match decomp with
  | Eprog ?prog' ?consts' =>
    let prog := fresh "__prog" in
    set (prog := prog') ;
    let consts := fresh "__consts" in
    set (consts := consts')
  end.

Ltac reify_full vars0 :=
  match goal with
  | |- eval_goal ?g' ?y =>
    let vars := get_vars y vars0 in
    let g := fresh "__goal" in
    set (g := g') ;
    reify_partial y vars ;
    apply eq_ind ;
    find_hyps vars
  end.

Module Bnd (I : IntervalOps).

Module E := Tree.Bnd I.
Module J := IntervalExt I.

Definition eval_hyp_bnd (prec : I.precision) (h : hyp) :=
  match h with
  | Hlele _ _ u v => I.join (E.eval_bnd prec u) (E.eval_bnd prec v)
  | Hle _ _ v => I.lower_extent (E.eval_bnd prec v)
  | Hge _ _ u => I.upper_extent (E.eval_bnd prec u)
  | Habsle _ _ v => let vi := I.lower_extent (E.eval_bnd prec v) in I.meet (I.neg vi) vi
  end.

Theorem eval_hyp_bnd_correct :
  forall prec h var,
  eval_hyp h var ->
  contains (I.convert (eval_hyp_bnd prec h)) (Xreal var).
Proof.
intros prec h var.
destruct h as [b l v|b l u|l1 l2 u v|b l v] ; intros H.
- apply I.lower_extent_correct with (eval v nil).
  apply E.eval_bnd_correct.
  destruct l ; [|apply Rlt_le] ;
    destruct b ; [|apply Rge_le| |] ; apply H.
- apply I.upper_extent_correct with (eval u nil).
  apply E.eval_bnd_correct.
  destruct l ; [|apply Rlt_le] ;
    destruct b ; [|apply Rge_le| |] ; apply H.
- apply J.join_correct with (eval u nil) (eval v nil).
  apply E.eval_bnd_correct.
  apply E.eval_bnd_correct.
  destruct l1, l2 ; split ; try apply H ; apply Rlt_le, H.
- assert (H': (- eval v nil <= var <= eval v nil)%R).
    apply Rabs_le_inv.
    destruct l ; [|apply Rlt_le] ;
      destruct b ; [|apply Rge_le| |] ; apply H.
  apply I.meet_correct.
  rewrite <- (Ropp_involutive var).
  apply J.neg_correct.
  apply I.lower_extent_correct with (eval v nil).
  apply E.eval_bnd_correct.
  lra.
  apply I.lower_extent_correct with (eval v nil).
  apply E.eval_bnd_correct.
  apply H'.
Qed.

Fixpoint merge_hyps_aux (prec : I.precision) (hyps : list hyp) (acc : I.type) :=
  match hyps with
  | h :: t =>
    merge_hyps_aux prec t (I.meet (eval_hyp_bnd prec h) acc)
  | nil => acc
  end.

Fixpoint merge_hyps (prec : I.precision) (hyps : list (list hyp)) :=
  match hyps with
  | h :: t =>
    cons (merge_hyps_aux prec h I.whole) (merge_hyps prec t)
  | nil => nil
  end.

Fixpoint eval_hyps_bnd (hyps : list I.type) (vars : list R) :=
  match hyps, vars with
  | hh :: th, hv :: tv =>
    contains (I.convert hh) (Xreal hv) /\ eval_hyps_bnd th tv
  | nil, nil => True
  | _, _ => False
  end.

Theorem eval_hyps_bnd_correct :
  forall prec hyps vars (g : Prop),
  (eval_hyps_bnd (merge_hyps prec hyps) vars -> g) ->
  eval_hyps hyps vars g.
Proof.
intros prec.
induction hyps as [|h1 t1 IH1].
  intros [|x vars] g H.
  now apply H.
  exact I.
intros [|x vars].
easy.
simpl.
generalize I.whole (I.whole_correct x).
induction h1 as [|h2 t2 IH2] ; intros xi Ix g H.
  apply IH1.
  intros H'.
  now apply H.
simpl.
intros H'.
simpl in H.
apply (IH2 (I.meet (eval_hyp_bnd prec h2) xi)).
apply I.meet_correct with (2 := Ix).
now apply eval_hyp_bnd_correct.
intros H''.
now apply H.
Qed.

Definition eval_goal_bnd (prec : I.precision) (g : gol) : I.type -> bool :=
  match g with
  | Gle _ v =>
    let j := I.lower_complement (E.eval_bnd prec v) in
    fun i => I.subset i j
  | Gge _ u =>
    let j := I.upper_complement (E.eval_bnd prec u) in
    fun i => I.subset i j
  | Glele u v =>
    let u := I.upper_complement (E.eval_bnd prec u) in
    let v := I.lower_complement (E.eval_bnd prec v) in
    let j := I.meet u v in
    fun i => I.subset i j
  | Gabsle _ v =>
    let v := I.lower_complement (E.eval_bnd prec v) in
    let j := I.meet (I.neg v) v in
    fun i => I.subset i j
  | Glt v =>
    let j := E.eval_bnd prec v in
    fun i => match I.sign_strict (I.sub prec i j) with Xlt => true | _ => false end
  | Ggt u =>
    let j := E.eval_bnd prec u in
    fun i => match I.sign_strict (I.sub prec i j) with Xgt => true | _ => false end
  | Gne _ v =>
    let j := E.eval_bnd prec v in
    fun i => match I.sign_strict (I.sub prec i j) with Xlt => true | Xgt => true | _ => false end
  end.

Theorem eval_goal_bnd_correct :
  forall prec g xi x,
  contains (I.convert xi) (Xreal x) ->
  eval_goal_bnd prec g xi = true ->
  eval_goal g x.
Proof.
intros prec g xi x Ix.
destruct g as [b v|b u|u v|b v|v|u|b u] ; simpl ; intros H.
- cut (x <= eval v nil)%R.
    now destruct b ; [|apply Rle_ge].
  apply I.subset_correct, subset_contains in H.
  apply I.lower_complement_correct with (2 := H _ Ix).
  apply E.eval_bnd_correct.
- cut (eval u nil <= x)%R.
    now destruct b ; [|apply Rle_ge].
  apply I.subset_correct, subset_contains in H.
  apply I.upper_complement_correct with (2 := H _ Ix).
  apply E.eval_bnd_correct.
- apply I.subset_correct, subset_contains in H.
  specialize (H _ Ix).
  apply I.meet_correct' in H.
  split.
  apply I.upper_complement_correct with (2 := proj1 H).
  apply E.eval_bnd_correct.
  apply I.lower_complement_correct with (2 := proj2 H).
  apply E.eval_bnd_correct.
- cut (Rabs x <= eval v nil)%R.
    now destruct b ; [|apply Rle_ge].
  apply I.subset_correct, subset_contains in H.
  specialize (H _ Ix).
  apply I.meet_correct' in H.
  apply Rabs_le.
  destruct H as [H1 H2].
  split.
  rewrite <- (Ropp_involutive x) in H1 |- *.
  apply Ropp_le_contravar.
  apply (I.neg_correct' _ (Xreal (-x))) in H1.
  apply I.lower_complement_correct with (2 := H1).
  apply E.eval_bnd_correct.
  apply I.lower_complement_correct with (2 := H2).
  apply E.eval_bnd_correct.
- apply Rminus_lt.
  generalize (I.sign_strict_correct (I.sub prec xi (E.eval_bnd prec v))).
  destruct I.sign_strict ; try easy.
  intros Hd.
  apply (Hd (Xreal (x - eval v nil))).
  apply J.sub_correct with (1 := Ix).
  apply E.eval_bnd_correct.
- apply Rminus_gt.
  generalize (I.sign_strict_correct (I.sub prec xi (E.eval_bnd prec u))).
  destruct I.sign_strict ; try easy.
  intros Hd.
  apply (Hd (Xreal (x - eval u nil))).
  apply J.sub_correct with (1 := Ix).
  apply E.eval_bnd_correct.
- cut (x - eval u nil <> 0)%R.
    destruct b ; lra.
  generalize (I.sign_strict_correct (I.sub prec xi (E.eval_bnd prec u))).
  destruct I.sign_strict ; try easy ; intros Hd.
  apply Rlt_not_eq.
  apply (Hd (Xreal (x - eval u nil))).
  apply J.sub_correct with (1 := Ix).
  apply E.eval_bnd_correct.
  apply Rgt_not_eq.
  apply (Hd (Xreal (x - eval u nil))).
  apply J.sub_correct with (1 := Ix).
  apply E.eval_bnd_correct.
Qed.

End Bnd.
