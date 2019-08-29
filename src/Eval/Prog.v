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

From Coq Require Import ZArith Reals List Psatz.

Require Import Xreal.
Require Import Tree.

Inductive term : Set :=
  | Forward : nat -> term
  | Unary : unary_op -> nat -> term
  | Binary : binary_op -> nat -> nat -> term.

Set Implicit Arguments.

Record operations (A : Type) : Type :=
  { constant : Z -> A
  ; unary : unary_op -> A -> A
  ; binary : binary_op -> A -> A -> A
  ; sign : A -> Xcomparison }.

Unset Implicit Arguments.

Definition eval_generic_body {A} def (ops : operations A) values op :=
  let nth n := nth n values def in
  match op with
  | Forward u => nth u
  | Unary o u => unary ops o (nth u)
  | Binary o u v => binary ops o (nth u) (nth v)
  end :: values.

Definition eval_generic {A} def (ops : operations A) :=
  fold_left (eval_generic_body def ops).

Lemma rev_formula :
  forall A formula terms def (ops : operations A),
  eval_generic def ops formula terms =
  fold_right (fun y x => eval_generic_body def ops x y) terms (rev formula).
Proof.
intros.
pattern formula at 1 ; rewrite <- rev_involutive.
unfold eval_generic, eval_generic_body.
rewrite <- fold_left_rev_right.
rewrite rev_involutive.
apply refl_equal.
Qed.

Theorem eval_inductive_prop :
  forall A B (P : A -> B -> Prop) defA defB (opsA : operations A) (opsB : operations B),
  P defA defB ->
 (forall o a b, P a b -> P (unary opsA o a) (unary opsB o b)) ->
 (forall o a1 a2 b1 b2, P a1 b1 -> P a2 b2 -> P (binary opsA o a1 a2) (binary opsB o b1 b2)) ->
  forall inpA inpB,
 (forall n, P (nth n inpA defA) (nth n inpB defB)) ->
  forall prog,
  forall n, P (nth n (eval_generic defA opsA prog inpA) defA) (nth n (eval_generic defB opsB prog inpB) defB).
Proof.
intros A B P defA defB opsA opsB Hdef Hun Hbin inpA inpB Hinp prog.
do 2 rewrite rev_formula.
induction (rev prog).
exact Hinp.
intros [|n].
2: apply IHl.
destruct a as [n|o n|o n1 n2] ;
  [ idtac | apply Hun | apply Hbin ] ; apply IHl.
Qed.

Definition real_operations :=
  Build_operations IZR
   unary_real binary_real
   (fun x => Xcmp (Xreal x) (Xreal 0)).

Definition eval_real :=
  eval_generic 0%R real_operations.
