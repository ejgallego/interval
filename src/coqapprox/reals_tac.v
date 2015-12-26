Require Import Reals.
Require Import Rbase.
Require Import Psatz.

Lemma Rinv_r_neq0 r ri : (r * ri = 1)%R -> ri <> 0%R.
Proof.
now intros Hri Kri; rewrite Kri, Rmult_0_r in Hri; apply R1_neq_R0; rewrite Hri.
Qed.

(** Tactics inspired by Frédéric Besson's coq-club post on 2015-04-05:
    https://sympa.inria.fr/sympa/arc/coq-club/2012-04/msg00025.html *)

Ltac add_eq expr val :=
  let temp := fresh in
  set (temp := expr) ;
  generalize (refl_equal temp) ;
  unfold temp at 1 ;
  generalize temp ;
  intro val ;
  clear temp.

Ltac elim_rinv :=
  match goal with
  | HX : context [Rinv ?X] |- _ =>
    let r := fresh "r" in
    let ri := fresh "ri" in
    let Hri := fresh "Hri" in
    let Hr := fresh "Hr" in
    revert HX ;
    add_eq X r ; generalize (Rinv_r r) ; generalize (Rinv r) ;
    intros ri Hri Hr; intros
  | |- context [Rinv ?X] =>
    let r := fresh "r" in
    let ri := fresh "ri" in
    let Hri := fresh "Hri" in
    let Hr := fresh "Hr" in
    add_eq X r ; generalize (Rinv_r r) ; generalize (Rinv r) ;
    intros ri Hri Hr; intros
  end.

Ltac simpl_R :=
  unfold Rdiv in * ; repeat elim_rinv.

(* Usage: 'simpl_R; psatzl R' or 'simpl_R; lra' *)
