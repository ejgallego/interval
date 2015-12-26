Require Import Reals.
Require Import Rbase.
Require Import Psatz.

(** Ltac trick posted on coq-club by Frédéric Besson on 2015-04-05:
    https://sympa.inria.fr/sympa/arc/coq-club/2012-04/msg00025.html *)

Ltac add_eq expr val :=
  let temp := fresh in
  set (temp := expr) ; generalize (refl_equal temp) ; unfold temp at 1 ; generalize temp ; intro val ; clear temp.

Ltac elim_rinv :=
 match goal with
     | H : context [Rinv ?X] |- _ =>
         revert H ;
         let x := fresh in
           add_eq X x ; generalize (Rinv_r x) ; generalize (Rinv x) ;
         intros
     | |- context [Rinv ?X] =>
         let x := fresh in
           add_eq X x ; generalize (Rinv_r x) ; generalize (Rinv x) ;
         intros
 end.

Ltac simpl_R :=
 unfold Rdiv in * ; repeat elim_rinv.

(* Usage: 'simpl_R; psatzl R' or 'simpl_R; lra' *)
