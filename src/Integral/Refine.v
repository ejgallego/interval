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

From Coq Require Import BinPos Reals List.
From Coquelicot Require Import Coquelicot.

Require Import Xreal.
Require Import Interval.
Require Import Priority.

Section IterUntil.

Fixpoint iter_until {T} n (step : T -> T) (done : T -> bool) v :=
  match n with
  | xH => step v
  | xO n =>
    let v := iter_until n step done v in
    if done v then v else
    iter_until n step done v
  | xI n =>
    let v := step v in
    if done v then v else
    let v := iter_until n step done v in
    if done v then v else
    iter_until n step done v
  end.

Theorem iter_until_correct :
  forall {T} (P : T -> Prop) n step done,
  (forall v : T, P v -> P (step v)) ->
  forall v : T, P v -> P (iter_until n step done v).
Proof.
intros T P n step done H.
induction n as [n IH|n IH|] ; intros v Hv ; simpl.
- case done.
  now apply H.
  apply H in Hv.
  apply IH in Hv.
  case done.
  exact Hv.
  now apply IH.
- apply IH in Hv.
  case done.
  exact Hv.
  now apply IH.
- now apply H.
Qed.

End IterUntil.

Module IntegralRefiner (I : IntervalOps).

Module J := IntervalExt I.

Inductive piece :=
  Piece (u v : I.bound_type) (i : I.type).

Fixpoint invariant_aux l (u v : I.bound_type) :=
  match l with
  | nil => I.convert_bound u = I.convert_bound v
  | Piece u' v' i :: t =>
    I.convert_bound u = I.convert_bound u' /\
    invariant_aux t v' v
  end.

Definition invariant (f : R -> R) (p : ptree piece) (u v : I.bound_type) :=
  all (fun r =>
    match r with
    | Piece u' v' i =>
      let ur := proj_val (I.convert_bound u') in
      let vr := proj_val (I.convert_bound v') in
      (I.convert i <> Inan -> ex_RInt f ur vr) /\
      contains (I.convert i) (Xreal (RInt f ur vr))
    end) (ptree_to_list p) /\
  exists q, permut (ptree_to_list p) q /\ invariant_aux q u v.

Definition sum prec (p : ptree piece) :=
  ptree_fold (fun acc v => I.add prec acc match v with Piece _ _ i => i end) p I.zero.

Theorem sum_invariant :
  forall prec p u v f,
  let ur := proj_val (I.convert_bound u) in
  let vr := proj_val (I.convert_bound v) in
  let s := sum prec p in
  invariant f p u v ->
  (I.convert s <> Inan -> ex_RInt f ur vr) /\
  contains (I.convert s) (Xreal (RInt f ur vr)).
Proof.
intros prec p u v f ur vr.
unfold sum, invariant.
rewrite ptree_fold_correct.
generalize (ptree_to_list p).
clear p. intros p.
assert (H: (I.convert I.zero <> Inan ->
    all (fun r =>
      match r with
      | Piece ur vr _ =>
        ex_RInt f (proj_val (I.convert_bound ur)) (proj_val (I.convert_bound vr))
      end) nil) /\
    contains (I.convert I.zero)
      (Xreal (fold_right (fun r s => Rplus s
        match r with
        | Piece ur vr _ => RInt f (proj_val (I.convert_bound ur)) (proj_val (I.convert_bound vr))
        end
      ) 0%R nil))).
  simpl.
  apply (conj (fun _ => I)).
  rewrite I.zero_correct.
  split ; apply Rle_refl.
change p with (nil ++ p) at 1 2.
intros [Hp [q [Hq Iq]]].
revert Hq Hp H.
generalize (@nil piece) I.zero.
induction p as [|h t IH] ; simpl ; intros l s Hq Hl [H1 H2].
- clear Hl.
  rewrite app_nil_r in Hq.
  rewrite fold_right_permut with (2 := Hq) in H2 by (intros ; ring).
  case_eq (I.convert s) ; [intros Hs | intros sl su Hs].
  easy.
  cut (ex_RInt f ur vr /\
      RInt f ur vr = fold_right (fun r s => s +
        match r with
        | Piece ur vr _ => RInt f (proj_val (I.convert_bound ur)) (proj_val (I.convert_bound vr))
        end) 0 q).
    intros [H3 H4].
    split.
    intros _.
    apply H3.
    rewrite H4.
    now rewrite <- Hs.
  assert (H1': all (fun r =>
      match r with
      | Piece ur vr _ => ex_RInt f (proj_val (I.convert_bound ur)) (proj_val (I.convert_bound vr))
      end) q).
    apply all_permut with (2 := Hq).
    apply H1.
    now rewrite Hs.
  clear -Iq H1'.
  revert u ur Iq H1'.
  induction q as [|[u' v' i] q IH] ; simpl.
    intros u -> _.
    split.
    apply ex_RInt_point.
    now rewrite RInt_point.
  intros u [-> H6] [H1 H2].
  destruct (IH _ H6 H2) as [H7 H8].
  assert (H9 := ex_RInt_Chasles _ _ _ _ H1 H7).
  assert (H5 := RInt_Chasles _ _ _ _ H1 H7).
  clear IH H1 H2 H6 H7.
  apply (conj H9).
  rewrite <- H5, H8.
  apply Rplus_comm.
- eapply permut_trans in Hq.
  2: apply permut_insert.
  destruct h as [ur' vr' i].
  eapply all_permut in Hl.
  2: apply permut_sym, permut_insert.
  apply (IH (_ :: l) (I.add prec s i) Hq Hl).
  destruct Hl as [H3 _].
  clear -H1 H2 H3.
  split.
    intros H'.
    split.
    apply H3.
    contradict H'.
    now apply I.add_propagate_r.
    apply H1.
    contradict H'.
    now apply I.add_propagate_l.
  simpl.
  apply J.add_correct.
  apply H2.
  apply H3.
Qed.

Definition le_piece (p q : piece) :=
  match p, q with
  | Piece _ _ pi, Piece _ _ qi => I.subset qi pi
  end.

Definition split_piece f p :=
  match ptree_pop le_piece p with
  | (Piece u v _, h) =>
    let m := I.midpoint (I.bnd u v) in
    let p1 := Piece u m (f u m) in
    let p2 := Piece m v (f m v) in
    ptree_insert le_piece (pheap_insert le_piece h p1) p2
  end.

Theorem split_piece_correct :
  forall f fi p u v,
  (forall u' v',
    (I.convert (fi u' v') <> Inan -> ex_RInt f (proj_val (I.convert_bound u')) (proj_val (I.convert_bound v'))) /\
    contains (I.convert (fi u' v')) (Xreal (RInt f (proj_val (I.convert_bound u')) (proj_val (I.convert_bound v'))))) ->
  invariant f p u v ->
  invariant f (split_piece fi p) u v.
Proof.
intros f fi p u v Hfi [H1 [q [H2 H3]]].
unfold split_piece.
generalize (ptree_pop_correct le_piece p).
destruct ptree_pop as [[u' v' i] p1].
intros H4.
set (m := I.midpoint (I.bnd u' v')).
generalize (pheap_insert_correct le_piece p1 (Piece u' m (fi u' m))).
generalize (pheap_insert le_piece p1 (Piece u' m (fi u' m))).
intros p2 H5.
generalize (ptree_insert_correct le_piece p2 (Piece m v' (fi m v'))).
generalize (ptree_insert le_piece p2 (Piece m v' (fi m v'))).
intros p3 H6.
unfold invariant.
split.
- apply permut_sym in H6.
  apply all_permut with (2 := H6).
  split.
  apply Hfi.
  apply permut_sym in H5.
  apply all_permut with (2 := H5).
  split.
  apply Hfi.
  clear -H1 H4.
  apply permut_sym in H4.
  eapply all_permut in H4.
  2: apply H1.
  apply H4.
- assert (H7 := permut_trans _ _ _ H4 H2).
  destruct (permut_remove _ _ _ H7) as [s [t [H8 H9]]].
  exists ((s ++ Piece u' m (fi u' m) :: nil) ++ Piece m v' (fi m v') :: t).
  split.
    apply permut_trans with (1 := H6).
    eapply permut_trans.
    2: apply permut_insert.
    apply permut_cons.
    rewrite <- app_assoc.
    simpl.
    apply permut_trans with (1 := H5).
    eapply permut_trans.
    2: apply permut_insert.
    now apply permut_cons.
  rewrite <- app_assoc.
  simpl.
  revert H3.
  rewrite H8.
  clear.
  revert u.
  induction s as [|[ur vr i'] s IH] ; simpl ; intros u [H1 H2].
  easy.
  apply (conj H1).
  now apply IH.
Qed.

End IntegralRefiner.
