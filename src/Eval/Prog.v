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

Scheme Equality for expr.

Inductive splitted_expr : Set :=
  | Sconst
  | Scomposed (lp lc : list expr).

Fixpoint rcons_unique (e : expr) (l : list expr) :=
  match l with
  | cons h t =>
    if expr_beq e h then l else cons h (rcons_unique e t)
  | nil => cons e nil
  end.

Definition cons_unique (e : expr) (l : list expr) :=
  let fix aux (l' : list expr) :=
    match l' with
    | cons h t =>
      if expr_beq e h then l else aux t
    | nil => cons e l
    end in
  aux l.

Fixpoint split_expr (e : expr) (lp lc : list expr) :=
  match e with
  | Evar n => Scomposed lp lc
  | Econst o => Sconst
  | Eunary o e1 =>
    match split_expr e1 lp lc with
    | Sconst => Sconst
    | Scomposed lp lc => Scomposed (cons_unique e lp) lc
    end
  | Ebinary o e1 e2 =>
    match split_expr e2 lp lc with
    | Sconst =>
      match split_expr e1 lp lc with
      | Sconst => Sconst
      | Scomposed lp lc => Scomposed (cons_unique e lp) (rcons_unique e2 lc)
      end
    | Scomposed lp lc =>
      match split_expr e1 lp lc with
      | Sconst => Scomposed (cons_unique e lp) (rcons_unique e1 lc)
      | Scomposed lp lc => Scomposed (cons_unique e lp) lc
      end
    end
  end.

Theorem split_expr_correct :
  forall vars e lp lc,
  (forall n, eval (nth n lc (Econst (Int 0))) vars = eval (nth n lc (Econst (Int 0))) nil) ->
  match split_expr e lp lc with
  | Sconst => eval e vars = eval e nil
  | Scomposed lp' lc' =>
    forall n, eval (nth n lc' (Econst (Int 0))) vars = eval (nth n lc' (Econst (Int 0))) nil
  end.
Proof.
intros vars.
induction e as [n|o|o e1 IHe1|o e1 IHe1 e2 IHe2] ; intros lp lc Hc ; simpl ; try easy.
  specialize (IHe1 lp lc Hc).
  destruct split_expr as [|lp' lc'].
  now apply f_equal.
  apply IHe1.
specialize (IHe2 lp lc Hc).
assert (H: forall e l,
    eval e vars = eval e nil ->
    (forall n, eval (nth n l (Econst (Int 0))) vars = eval (nth n l (Econst (Int 0))) nil) ->
    forall n,
    eval (nth n (rcons_unique e l) (Econst (Int 0))) vars = eval (nth n (rcons_unique e l) (Econst (Int 0))) nil).
  intros e l He Hl.
  induction l as [|h t IH] ; simpl.
    now intros [|[|n]].
  generalize (internal_expr_dec_bl e h).
  destruct expr_beq.
  intros H [|n].
  simpl.
  now rewrite <- H.
  apply Hl.
  intros _ [|n].
  apply (Hl 0%nat).
  apply IH.
  intros n'.
  apply (Hl (S n')).
destruct split_expr as [|lp2 lc2].
  specialize (IHe1 lp lc Hc).
  destruct split_expr as [|lp1 lc1].
  now apply f_equal2.
  now apply H.
specialize (IHe1 lp2 lc2 IHe2).
destruct split_expr as [|lp1 lc1].
  now apply H.
apply IHe1.
Qed.

Fixpoint find_expr_aux (e : expr) (n : nat) (l : list expr) :=
  match l with
  | cons h t => if expr_beq e h then Some n else find_expr_aux e (S n) t
  | nil => None
  end.

Definition find_expr (e : expr) (vars : nat) (lp lc : list expr) :=
  match e with
  | Evar n =>
    if Nat.ltb n vars then Some (List.length lp + n)%nat else None
  | _ =>
    match find_expr_aux e 0%nat lp with
    | Some n => Some n
    | None => find_expr_aux e (length lp + vars)%nat lc
    end
  end.

Theorem find_expr_correct :
  forall e vars lp lc,
  match find_expr e vars lp lc with
  | Some n => nth n (lp ++ map Evar (seq 0 vars) ++ lc) (Econst (Int 0)) = e
  | None => True
  end.
Proof.
intros e vars lp lc.
assert (H1: forall l n,
    match find_expr_aux e n l with
    | Some k => (n <= k < n + length l)%nat /\ nth (k - n) l (Econst (Int 0)) = e
    | None => True
    end).
  induction l as [|h t IH].
  easy.
  intros n.
  simpl find_expr_aux.
  generalize (internal_expr_dec_bl e h).
  destruct expr_beq.
  intros H.
  split.
  simpl.
  lia.
  rewrite Nat.sub_diag.
  now rewrite H.
  intros _.
  specialize (IH (S n)).
  revert IH.
  destruct find_expr_aux as [k|] ; try easy.
  intros [H1 H2].
  split.
  simpl.
  lia.
  replace (k - n)%nat with (S (k - S n))%nat by lia.
  easy.
unfold find_expr.
set (foo :=
  match find_expr_aux e 0%nat lp with
  | Some n => Some n
  | None => find_expr_aux e (length lp + vars)%nat lc
  end).
assert (H2:
    match foo with
    | Some n => nth n (lp ++ map Evar (seq 0 vars) ++ lc) (Econst (Int 0)) = e
    | None => True
    end).
  unfold foo.
  clear foo.
  generalize (H1 lp 0%nat).
  destruct find_expr_aux as [n1|].
  rewrite Nat.add_0_l, Nat.sub_0_r.
  intros [H2 H3].
  now rewrite app_nth1.
  intros _.
  specialize (H1 lc (length lp + vars)%nat).
  revert H1.
  destruct find_expr_aux as [n2|] ; try easy.
  intros [H1 H2].
  rewrite -> app_nth2 by lia.
  rewrite app_nth2 ; rewrite map_length, seq_length.
  now rewrite <- Nat.sub_add_distr.
  lia.
destruct e as [n|o|o n1|o n1 n2] ; simpl ; try easy.
destruct (Nat.ltb_spec n vars) as [H|H] ; try easy.
rewrite app_nth2 by apply le_plus_l.
rewrite minus_plus.
rewrite app_nth1.
rewrite nth_indep with (d' := Evar 0).
now rewrite map_nth, seq_nth.
now rewrite map_length, seq_length.
now rewrite map_length, seq_length.
Qed.

Fixpoint decompose (vars : nat) (p : list term) (lp lc : list expr) :=
  match lp with
  | nil => Some p
  | cons h t =>
    match h with
    | Evar n => decompose vars (cons (Forward (length t + n)) p) t lc
    | Econst _ => None
    | Eunary o e1 =>
      match find_expr e1 vars t lc with
      | Some n => decompose vars (cons (Unary o n) p) t lc
      | None => None
      end
    | Ebinary o e1 e2 =>
      match find_expr e1 vars t lc with
      | Some n1 =>
        match find_expr e2 vars t lc with
        | Some n2 => decompose vars (cons (Binary o n1 n2) p) t lc
        | None => None
        end
      | None => None
      end
    end
  end.

Theorem decompose_correct :
  forall vars p lp lc,
  (forall vars n, eval (nth n lc (Econst (Int 0))) vars = eval (nth n lc (Econst (Int 0))) nil) ->
  let lc' := map (fun c => eval c nil) lc in
  match decompose (length vars) p lp lc with
  | None => True
  | Some lp' =>
    eval_real lp' (app vars lc') =
    eval_real p (app (map (fun c => eval c (app vars lc')) lp) (app vars lc'))
  end.
Proof.
intros vars p lp lc Hc lc'.
revert p.
induction lp as [|h t IH].
easy.
intros p.
simpl.
assert (H: forall n e,
    nth n (t ++ map Evar (seq 0 (length vars)) ++ lc) (Econst (Int 0)) = e ->
    nth n (map (fun c : expr => eval c (vars ++ lc')) t ++ vars ++ lc') 0%R = eval e (vars ++ lc')).
  intros n e.
  destruct (Nat.lt_ge_cases n (length t)) as [H1|H1].
  rewrite app_nth1 by apply H1.
  intros H.
  rewrite app_nth1 by now rewrite map_length.
  change 0%R with ((fun c => eval c (vars ++ lc')) (Econst (Int 0))).
  rewrite map_nth.
  now rewrite H.
  rewrite app_nth2 by apply H1.
  rewrite (@app_nth2 _ _ _ _ n) ; rewrite map_length.
  2: exact H1.
  destruct (Nat.lt_ge_cases (n - length t) (length vars)) as [H2|H2].
  rewrite app_nth1 by now rewrite map_length, seq_length.
  rewrite app_nth1 by apply H2.
  rewrite nth_indep with (d' := Evar 0) by now rewrite map_length, seq_length.
  rewrite map_nth, seq_nth, plus_0_l by apply H2.
  intros <-.
  simpl.
  now rewrite app_nth1 by apply H2.
  rewrite app_nth2 ; rewrite map_length, seq_length.
  2: exact H2.
  rewrite app_nth2 by apply H2.
  intros H.
  unfold lc'.
  change 0%R with ((fun c => eval c nil) (Econst (Int 0))).
  rewrite map_nth, H.
  rewrite <- H at 2.
  now rewrite Hc, H.
destruct h as [n|o|o e1|o e1 e2] ; try easy.
- specialize (IH (Forward (length t + n) :: p)).
  destruct decompose ; try easy.
  rewrite IH.
  simpl.
  unfold eval_generic_body.
  rewrite app_nth2 ; rewrite map_length.
  apply (f_equal (fun v => eval_real p (nth v _ _ :: _))).
  lia.
  lia.
- generalize (find_expr_correct e1 (length vars) t lc).
  destruct find_expr as [n1|] ; try easy.
  intros H1.
  specialize (IH (Unary o n1 :: p)).
  destruct decompose ; try easy.
  rewrite IH.
  simpl.
  unfold eval_generic_body.
  apply (f_equal (fun v => eval_real p (unary_real o v :: _))).
  now apply H.
- generalize (find_expr_correct e1 (length vars) t lc).
  destruct find_expr as [n1|] ; try easy.
  intros H1.
  generalize (find_expr_correct e2 (length vars) t lc).
  destruct find_expr as [n2|] ; try easy.
  intros H2.
  specialize (IH (Binary o n1 n2 :: p)).
  destruct decompose ; try easy.
  rewrite IH.
  simpl.
  unfold eval_generic_body.
  apply (f_equal2 (fun v1 v2 => eval_real p (binary_real o v1 v2 :: _))).
  now apply H.
  now apply H.
Qed.

Fixpoint max_arity (e : expr) (n : nat) :=
  match e with
  | Evar k => Nat.ltb k n
  | Econst _ => true
  | Eunary o e1 => max_arity e1 n
  | Ebinary o e1 e2 => if max_arity e1 n then max_arity e2 n else false
  end.

Inductive extracted_expr : Set :=
  | Eabort
  | Eprog (lp : list term) (lc : list expr).

Definition extract (e : expr) (vars : nat) :=
  match split_expr e nil nil with
  | Sconst => Eprog (cons (Forward vars) nil) (cons e nil)
  | Scomposed lp lc =>
    let lp' :=
      match lp with
      | cons h t => if expr_beq e h then lp else e :: lp
      | nil => e :: lp
      end in
    match decompose vars nil lp' lc with
    | Some p => if max_arity e vars then Eprog p lc else Eabort
    | None => Eabort
    end
  end.

Definition eval_real' prog vars consts :=
  nth 0 (eval_real prog (vars ++ map (fun c => eval c nil) consts)) 0%R.

Theorem extract_correct :
  forall e vars,
  match extract e (length vars) with
  | Eabort => True
  | Eprog lp lc => eval_real' lp vars lc = eval e vars
  end.
Proof.
intros e vars.
unfold extract.
generalize (fun v => split_expr_correct v e nil nil).
destruct split_expr as [|lp lc].
  unfold eval_real'.
  simpl.
  intros H.
  rewrite app_nth2 by apply le_refl.
  rewrite Nat.sub_diag.
  apply sym_eq, H.
  now intros [|n].
intros H.
assert (exists lp',
    match lp with
    | cons h t => if expr_beq e h then lp else e :: lp
    | nil => e :: lp
    end = e :: lp') as [lp' ->].
  destruct lp as [|h t].
  now exists nil.
  generalize (internal_expr_dec_bl e h).
  destruct expr_beq.
  intros ->.
  now exists t.
  apply eq_refl.
  intros _.
  now exists (h :: t).
simpl in H.
generalize (decompose_correct vars nil (e :: lp') lc).
destruct decompose as [p|] ; try easy.
case_eq (max_arity e (length vars)).
2: easy.
unfold eval_real'.
intros H' ->.
simpl.
clear -H'.
induction e as [n|o|o e1|o e1 IHe1 e2 IHe2] ; simpl ; try easy.
apply app_nth1.
simpl in H'.
now apply Nat.ltb_lt.
now apply f_equal, IHe1.
simpl in H'.
destruct max_arity ; try easy.
apply f_equal2.
now apply IHe1.
now apply IHe2.
intros v.
apply H.
now intros [|n].
Qed.
