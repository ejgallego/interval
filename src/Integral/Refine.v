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

Require Import Coquelicot.
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

Inductive integral_bound := IBu | IBv | IBp (x : I.bound_type).

Section Bounds.

Variable uf vf : (R -> Prop) -> Prop.
Context (Fuf : ProperFilter' uf) (Fvf : ProperFilter' vf).

Definition convert b :=
  match b with
  | IBu => uf
  | IBv => vf
  | IBp x => at_point (proj_val (I.convert_bound x))
  end.

Local Instance filter_convert :
  forall b, ProperFilter' (convert b).
Proof.
intros [| |p] ; simpl ; try easy.
apply Proper_StrongProper.
apply at_point_filter.
Qed.

Definition valid f u v i :=
  (I.convert i <> Inan -> ex_RInt_gen f (convert u) (convert v)) /\
  contains (I.convert i) (Xreal (RInt_gen f (convert u) (convert v))).

Inductive piece :=
  Piece (u v : integral_bound) (i : I.type).

Fixpoint invariant_aux h l (u : integral_bound) :=
  match h with
  | Piece u' v i => u = u' /\
    match l with
    | nil => v = IBv
    | h :: t =>
      match v with IBp _ => invariant_aux h t v | _ => False end
    end
  end.

Definition invariant (f : R -> R) (p : ptree piece) :=
  all (fun r => match r with Piece uf vf i => valid f uf vf i end) (ptree_to_list p) /\
  exists qh, exists qt, permut (ptree_to_list p) (qh :: qt) /\ invariant_aux qh qt IBu.

Definition sum prec (p : ptree piece) :=
  ptree_fold (fun acc v => I.add prec acc match v with Piece _ _ i => i end) p I.zero.

Theorem sum_invariant :
  forall prec p f,
  invariant f p ->
  valid f IBu IBv (sum prec p).
Proof.
intros prec p f.
unfold sum, invariant, valid.
rewrite ptree_fold_correct.
generalize (ptree_to_list p).
clear p. intros p.
assert (H: (I.convert I.zero <> Inan ->
    all (fun r =>
      match r with
      | Piece ur vr _ => ex_RInt_gen f (convert ur) (convert vr)
      end) nil) /\
    contains (I.convert I.zero)
      (Xreal (fold_right (fun r s => Rplus s
        match r with
        | Piece ur vr _ => RInt_gen f (convert ur) (convert vr)
        end
      ) 0%R nil))).
  simpl.
  apply (conj (fun _ => I)).
  rewrite I.zero_correct.
  split ; apply Rle_refl.
change p with (nil ++ p) at 1 2.
intros [Hp [qh [qt [Hq Iq]]]].
revert Hq Hp H.
generalize (@nil piece) I.zero.
induction p as [|h t IH] ; simpl ; intros l s Hq Hl [H1 H2].
- clear Hl.
  rewrite app_nil_r in Hq.
  rewrite fold_right_permut with (2 := Hq) in H2 by (intros ; ring).
  case_eq (I.convert s) ; [intros Hs | intros sl su Hs].
  easy.
  cut (ex_RInt_gen f uf vf /\
      RInt_gen f uf vf = fold_right (fun r s => s +
        match r with
        | Piece ur vr _ => RInt_gen f (convert ur) (convert vr)
        end) 0 (qh :: qt)).
    intros [H3 H4].
    split.
    intros _.
    apply H3.
    rewrite H4.
    now rewrite <- Hs.
  assert (H1': all (fun r =>
      match r with
      | Piece ur vr _ => ex_RInt_gen f (convert ur) (convert vr)
      end) (qh :: qt)).
    apply all_permut with (2 := Hq).
    apply H1.
    now rewrite Hs.
  clear -Iq H1' Fuf Fvf.
  revert qh Iq H1'.
  change uf with (convert IBu).
  generalize IBu.
  induction qt as [|qh qt IH] ; simpl.
    intros x [u v _] [-> ->] [H _].
    apply (conj H).
    apply eq_sym, Rplus_0_l.
  intros x [u v _] [-> H6] [H1 H2].
  destruct v as [| |x] ; try easy.
  destruct (IH _ _ H6 H2) as [H7 H8].
  assert (H9 := ex_RInt_gen_Chasles _ _ H1 H7).
  assert (H5 := RInt_gen_Chasles _ _ H1 H7).
  clear IH H1 H2 H6 H7.
  apply (conj H9).
  simpl in H8.
  rewrite <- H5, <- H8.
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

Definition split_piece midp fi p :=
  match ptree_pop le_piece p with
  | (Piece u v _, h) =>
    let m := IBp (midp u v) in
    let p1 := Piece u m (fi u m) in
    let p2 := Piece m v (fi m v) in
    ptree_insert le_piece (pheap_insert le_piece h p1) p2
  end.

Theorem split_piece_correct :
  forall midp f fi p,
  (forall u v, valid f u v (fi u v)) ->
  invariant f p ->
  invariant f (split_piece midp fi p).
Proof.
intros midp f fi p Hfi [H1 [qh [qt [H2 H3]]]].
unfold split_piece.
generalize (ptree_pop_correct le_piece p).
destruct ptree_pop as [[u' v' i] p1].
intros H4.
set (m := IBp (midp u' v')).
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
  assert (exists sh st, sh :: st = s ++ Piece u' m (fi u' m) :: nil) as [sh [st Ha]].
    clear.
    destruct s as [|sh st].
    now exists (Piece u' m (fi u' m)), nil.
    now exists sh, (st ++ Piece u' m (fi u' m) :: nil).
  exists sh, (st ++ Piece m v' (fi m v') :: t).
  split.
    change (sh :: st ++ _) with ((sh :: st) ++ Piece m v' (fi m v') :: t).
    rewrite Ha.
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
  revert H3 H8 Ha.
  clear.
  generalize IBu.
  revert qh qt sh st.
  induction s as [|[u v i'] s IH] ; simpl ; intros qh qt sh st x H1 [= -> ->] [= -> ->].
    simpl.
    destruct t as [|th tt].
    now destruct H1.
    now destruct H1.
  destruct s as [|sh st].
    destruct H1 as [H1 H2].
    simpl.
    apply (conj H1).
    destruct v as [| |x'] ; try easy.
    destruct t as [|th tt].
    now destruct H2.
    now destruct H2.
  destruct H1 as [H1 H2].
  simpl.
  apply (conj H1).
  destruct v as [| |x'] ; try easy.
  now apply IH with (1 := H2).
Qed.

End Bounds.

End IntegralRefiner.
