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

From Coq Require Import Reals List Psatz.
From Flocq Require Import Raux.

Require Import Xreal.
Require Import Interval.
Require Import Tree.
Require Import Prog.

Inductive hyp : Set :=
  | Hle (b : bool) (v : expr)
  | Hge (b : bool) (u : expr)
  | Hlele (u v : expr)
  | Habsle (b : bool) (v : expr).

Fixpoint eval_hyp (h : hyp) (var : R) :=
  match h with
  | Hle true v => (var <= eval v nil)%R
  | Hle false v => (eval v nil >= var)%R
  | Hge true u => (eval u nil <= var)%R
  | Hge false u => (var >= eval u nil)%R
  | Hlele u v => (eval u nil <= var <= eval v nil)%R
  | Habsle true v => (Rabs var <= eval v nil)%R
  | Habsle false v => (eval v nil >= Rabs var)%R
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
  | Gabsle (b : bool) (v : expr).

Definition eval_goal (g : gol) (x : R) :=
  match g with
  | Gle true v => (x <= eval v nil)%R
  | Gle false v => (eval v nil >= x)%R
  | Gge true u => (eval u nil <= x)%R
  | Gge false u => (x >= eval u nil)%R
  | Glele u v => (eval u nil <= x <= eval v nil)%R
  | Gabsle true v => (Rabs x <= eval v nil)%R
  | Gabsle false v => (eval v nil >= Rabs x)%R
  end.

Ltac massage_goal :=
  let aux a x t :=
    match reify a (@nil R) with
    | (?a, @nil R) => change (eval_goal (t a) x)
    end in
  match goal with
  | |- (Rabs ?x <= ?v)%R => aux v x (Gabsle true)
  | |- (?u <= ?x)%R => aux u x (Gge true)
  | |- (?x <= ?v)%R => aux v x (Gle true)
  | |- (?u <= ?x <= ?v)%R =>
    match reify u (@nil R) with
    | (?u, @nil R) => aux v x (Glele u)
    end
  end.

Ltac find_hyps_aux x known cont :=
  let aux H u t :=
    match reify u (@nil R) with
    | (?u, @nil R) =>
      let k := constr:(cons (t u) known) in
      revert H ;
      find_hyps_aux x k cont
    end in
  match goal with
  | H : (?u <= x <= ?v)%R |- _ =>
    match reify u (@nil R) with
    | (?u', @nil R) => aux H v (Hlele u')
    end
  | H : (?u <= x)%R |- _ => aux H u (Hge true)
  | H : (x >= ?u)%R |- _ => aux H u (Hge false)
  | H : (x <= ?v)%R |- _ => aux H v (Hle true)
  | H : (?v >= x)%R |- _ => aux H v (Hle false)
  | H : (Rabs x <= ?v)%R |- _ => aux H v (Habsle true)
  | H : (?v >= Rabs x)%R |- _ => aux H v (Habsle false)
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
  end.

Ltac reify_full vars0 :=
  match goal with
  | |- eval_goal ?g ?x =>
    match reify x vars0 with
    | (?prog, ?vars) =>
      change (eval_goal g (eval prog vars)) ;
      rewrite <- (extract_correct prog vars) ;
      find_hyps vars
    end
  end.

Module Bnd (I : IntervalOps).

Module E := Tree.Bnd I.
Module J := IntervalExt I.

Definition eval_hyp_bnd (prec : I.precision) (h : hyp) :=
  match h with
  | Hlele u v => I.join (E.eval_bnd prec u) (E.eval_bnd prec v)
  | Hle _ v => I.lower_extent (E.eval_bnd prec v)
  | Hge _ u => I.upper_extent (E.eval_bnd prec u)
  | Habsle _ v => let vi := I.lower_extent (E.eval_bnd prec v) in I.meet (I.neg vi) vi
  end.

Theorem eval_hyp_bnd_correct :
  forall prec h var,
  eval_hyp h var ->
  contains (I.convert (eval_hyp_bnd prec h)) (Xreal var).
Proof.
intros prec h var.
destruct h as [b v|b u|u v|b v] ; intros H.
- apply I.lower_extent_correct with (eval v nil).
  apply E.eval_bnd_correct.
  destruct b ; [|apply Rge_le] ; apply H.
- apply I.upper_extent_correct with (eval u nil).
  apply E.eval_bnd_correct.
  destruct b ; [|apply Rge_le] ; apply H.
- apply J.join_correct with (eval u nil) (eval v nil).
  apply E.eval_bnd_correct.
  apply E.eval_bnd_correct.
  apply H.
- assert (H': (- eval v nil <= var <= eval v nil)%R).
    apply Rabs_le_inv.
    destruct b ; [|apply Rge_le] ; apply H.
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

Definition eval_goal_bnd (prec : I.precision) (g : gol) :=
  match g with
  | Gle _ v => I.lower_complement (E.eval_bnd prec v)
  | Gge _ u => I.upper_complement (E.eval_bnd prec u)
  | Glele u v =>
    let u := I.upper_complement (E.eval_bnd prec u) in
    let v := I.lower_complement (E.eval_bnd prec v) in
    I.meet u v
  | Gabsle _ v =>
    let v := I.lower_complement (E.eval_bnd prec v) in
    I.meet (I.neg v) v
  end.

Theorem eval_goal_bnd_correct :
  forall prec g x,
  contains (I.convert (eval_goal_bnd prec g)) (Xreal x) ->
  eval_goal g x.
Proof.
intros prec g x.
destruct g as [b v|b u|u v|b v] ; simpl.
- intros H.
  cut (x <= eval v nil)%R.
    now destruct b ; [|apply Rle_ge].
  apply I.lower_complement_correct with (2 := H).
  apply E.eval_bnd_correct.
- intros H.
  cut (eval u nil <= x)%R.
    now destruct b ; [|apply Rle_ge].
  apply I.upper_complement_correct with (2 := H).
  apply E.eval_bnd_correct.
- intros H.
  apply I.meet_correct' in H.
  split.
  apply I.upper_complement_correct with (2 := proj1 H).
  apply E.eval_bnd_correct.
  apply I.lower_complement_correct with (2 := proj2 H).
  apply E.eval_bnd_correct.
- intros H.
  cut (Rabs x <= eval v nil)%R.
    now destruct b ; [|apply Rle_ge].
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
Qed.

End Bnd.
