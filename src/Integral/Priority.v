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

From Coq Require Import List Arith ZArith Psatz.
From mathcomp.ssreflect Require Import ssrfun ssrbool fintype.

Section Permut.

Context {T : Type}.

Fixpoint onth n (l : list T) :=
  match l, n with
  | nil, _ => None
  | v :: _, O => Some v
  | _ :: l, S n => onth n l
  end.

Lemma onth_nth :
  forall n p d,
  n < length p ->
  onth n p = Some (nth n p d).
Proof.
induction n as [|n IH] ; intros [|h p] d Hl ; try easy.
simpl.
apply IH.
now apply lt_S_n.
Qed.

Lemma onth_rev :
  forall n p,
  n < length p ->
  onth n (rev p) = onth (length p - S n) p.
Proof.
intros n [|h p].
easy.
intros H.
rewrite 2!onth_nth with (d := h).
now rewrite rev_nth with (1 := H).
lia.
now rewrite rev_length.
Qed.

Lemma onth_app_l :
  forall n p q,
  n < length p ->
  onth n (p ++ q) = onth n p.
Proof.
intros n p q.
revert n.
induction p as [|v p IH].
easy.
intros [|n] ; simpl.
easy.
intros H.
apply lt_S_n in H.
now apply IH.
Qed.

Lemma onth_app_r :
  forall n p q,
  length p <= n ->
  onth n (p ++ q) = onth (n - length p) q.
Proof.
intros n p q.
revert n.
induction p as [|v p IH].
intros n _.
now rewrite Nat.sub_0_r.
intros [|n] ; simpl.
easy.
intros H.
apply le_S_n in H.
now apply IH.
Qed.

Lemma onth_insert :
  forall n v p,
  onth n p = Some v ->
  exists q r, p = q ++ v :: r.
Proof.
intros n v p Hp.
set (f := fix aux n (q : list T) :=
  match n, q with
  | O, _ => nil
  | S n, nil => nil
  | S n, h :: t => h :: aux n t
  end).
set (g := fix aux n (q : list T) :=
  match q, n with
  | nil, _ => nil
  | h :: t, O => t
  | h :: t, S n => aux n t
  end).
exists (f n p), (g n p).
revert p Hp.
induction n as [|n IH] ; simpl ; intros [|h p] Hp ; try easy ; clearbody f g.
  now injection Hp as ->.
simpl.
apply f_equal.
now apply IH.
Qed.

Inductive permut (p q : list T) : Prop :=
  | Permut (Hl : length p = length q)
     (f : ordinal (length p) -> ordinal (length p))
     (Hf : injective f)
     (Hpq : forall n : ordinal _, onth n p = onth (f n) q).

Lemma permut_refl :
  forall p, permut p p.
Proof.
intros p.
now apply Permut with (f := fun n => n).
Qed.

Lemma permut_sym :
  forall p q, permut p q -> permut q p.
Proof.
intros p q [Hl f Hf Hpq].
revert f Hf Hpq.
rewrite Hl.
intros f Hf Hpq.
apply Permut with (f := invF Hf).
now apply eq_sym.
apply can_inj with (g := f).
apply f_invF.
intros n.
rewrite <- (f_invF Hf n) at 1.
apply eq_sym, Hpq.
Qed.

Lemma permut_trans :
  forall q p r,
  permut p q -> permut q r -> permut p r.
Proof.
intros q p r [Hl1 f1 Hf1 Hpq] [Hl2 f2 Hf2 Hqr].
revert f1 Hf1 Hpq f2 Hf2 Hqr.
rewrite <- Hl1.
intros f1 Hf1 Hpq f2 Hf2 Hqr.
apply Permut with (f := fun k => f2 (f1 k)).
now apply eq_trans with (length q).
now apply inj_comp.
intros n.
now rewrite <- Hqr.
Qed.

Lemma permut_rev :
  forall p, permut (rev p) p.
Proof.
intros p.
apply Permut with (f := fun x => rev_ord x).
apply rev_length.
apply rev_ord_inj.
intros n.
simpl.
rewrite <- ssrnat.minusE.
rewrite rev_length at 2.
apply onth_rev.
eapply elimT.
now apply ssrnat.ltP.
now rewrite <- (rev_length p).
Qed.

Lemma injective_split :
  forall n n1 n2 n3 n4 (H1 : n = n1 + n2) (H2 : n3 + n4 = n) f,
  injective f ->
  injective (fun k : ordinal n => cast_ord H2 (unsplit (f (split (cast_ord H1 k))))).
Proof.
intros n n1 n2 n3 n4 H1 H2 f Hf.
apply inj_comp with (f := cast_ord H2).
apply cast_ord_inj.
apply inj_comp with (f := @unsplit _ _).
eapply can_inj.
apply unsplitK.
apply inj_comp with (1 := Hf).
apply inj_comp with (f := @split _ _).
eapply can_inj.
apply splitK.
apply cast_ord_inj.
Qed.

Lemma permut_app_l :
  forall p q r,
  permut q r ->
  permut (p ++ q) (p ++ r).
Proof.
intros p q r [Hl f Hf H1].
assert (H2: length (p ++ q) = length p + length q).
  apply app_length.
simple refine (Permut _ _ _ _ _ _).
- rewrite 2!app_length.
  now apply f_equal.
- intros k.
  apply (cast_ord (esym H2)).
  apply unsplit.
  destruct (split (cast_ord H2 k)) as [k'|k'].
  now left.
  right.
  now apply f.
- apply injective_split with (f := fun k => match k with inl k' => inl k' | inr k' => inr (f k') end).
  clear -Hf.
  intros [k1|k1] [k2|k2] ; try easy.
  intros H.
  apply f_equal.
  injection H.
  apply Hf.
- simpl.
  intros n.
  case splitP ; simpl ; change ssrnat.addn with plus ; intros k ->.
  assert (Hk: k < length p).
    eapply elimT.
    now apply ssrnat.ltP.
    easy.
  now rewrite 2!onth_app_l.
  rewrite 2!onth_app_r by lia.
  rewrite 2!minus_plus.
  apply H1.
Qed.

Lemma permut_app :
  forall p q,
  permut (p ++ q) (q ++ p).
Proof.
intros l1 l2.
assert (H1: length l2 + length l1 = length (l1 ++ l2)).
  rewrite app_length.
  apply plus_comm.
assert (H2: length (l1 ++ l2) = length l1 + length l2).
  apply app_length.
simple refine (Permut _ _ _ _ _ _).
- rewrite 2!app_length.
  apply plus_comm.
- intros k.
  apply (cast_ord H1).
  apply unsplit.
  destruct (split (cast_ord H2 k)) as [k'|k'].
  now right.
  now left.
- apply injective_split with (f := fun k => match k with inl k' => inr k' | inr k' => inl k' end).
  clear.
  intros [k1|k1] [k2|k2] ; try easy ; intros H ; injection H ; apply f_equal.
- simpl.
  intros n.
  case splitP ; simpl ; change ssrnat.addn with plus ; intros k Hk.
  rewrite onth_app_l.
  rewrite onth_app_r by lia.
  rewrite minus_plus.
  now rewrite <- Hk.
  eapply elimT.
  now apply ssrnat.ltP.
  now rewrite Hk.
  rewrite onth_app_r by lia.
  rewrite onth_app_l.
  now rewrite Hk, minus_plus.
  cut (n < length l1 + length l2). lia.
  eapply elimT.
  apply ssrnat.ltP.
  now rewrite <- app_length.
Qed.

Lemma permut_app_r :
  forall p q r,
  permut p r ->
  permut (p ++ q) (r ++ q).
Proof.
intros p q r H.
apply permut_trans with (q ++ r).
apply permut_trans with (q ++ p).
apply permut_app.
now apply permut_app_l.
apply permut_app.
Qed.

Lemma permut_cons :
  forall h p q,
  permut p q ->
  permut (h :: p) (h :: q).
Proof.
intros h p q.
apply (permut_app_l (h :: nil)).
Qed.

Lemma permut_cons_rev :
  forall h p q,
  permut (h :: p) (h :: q) ->
  permut p q.
Proof.
intros h p q [Hl f Hf Hpq].
assert (H2: length (h :: p) = 1 + length p).
  easy.
simple refine (Permut _ _ _ _ _ _).
- now injection Hl.
- intros k.
  destruct (split (cast_ord H2 (f (rshift 1 k)))) as [_|k'].
    destruct (split (cast_ord H2 (f (@ord0 (length p))))) as [_|k'].
    apply k.
    apply k'.
  apply k'.
- set (g := fun (k : ordinal (length p)) =>
    match split (cast_ord H2 (invF Hf (rshift 1 k))) with
    | inl _ =>
      match split (cast_ord H2 (invF Hf (@ord0 (length p)))) with
      | inl _ => k
      | inr k' => k'
      end
    | inr k' => k'
    end).
  apply (@can_inj _ _ _ g).
  intros k.
  unfold g.
  clear g.
  destruct (splitP (cast_ord H2 (f (rshift 1 k)))) as [k1 Hk1|k1 Hk1].
  + replace (nat_of_ord k1) with O in Hk1 by now destruct k1 as [[|k1] H].
    destruct (splitP (cast_ord H2 (f (@ord0 (length p))))) as [k2 Hk2|k2 Hk2].
      replace (nat_of_ord k2) with O in Hk2 by now destruct k2 as [[|k2] H].
      exfalso.
      rewrite <- Hk2 in Hk1.
      apply ord_inj in Hk1.
      apply cast_ord_inj in Hk1.
      now apply Hf in Hk1.
    replace (invF Hf (rshift 1 k2)) with (@ord0 (length p)).
    destruct (splitP (cast_ord H2 (@ord0 (length p)))) as [k3 Hk3|k3 Hk3].
    2: easy.
    replace (invF Hf (@ord0 (length p))) with (rshift 1 k).
    destruct (splitP (cast_ord H2 (rshift 1 k))) as [k4 Hk4|k4 Hk4].
      now destruct k4 as [[|k4] H].
    apply ord_inj.
    now injection Hk4.
    apply Hf.
    rewrite f_invF.
    now apply ord_inj.
    apply Hf.
    rewrite f_invF.
    now apply ord_inj.
  + replace (invF Hf (rshift 1 k1)) with (rshift 1 k).
    destruct (splitP (cast_ord H2 (rshift 1 k))) as [k2 Hk2|k2 Hk2].
      now destruct k2 as [[|k2] H].
    apply ord_inj.
    now injection Hk2.
    apply Hf.
    rewrite f_invF.
    now apply ord_inj.
- intros k.
  destruct (splitP (cast_ord H2 (f (rshift 1 k)))) as [k1 Hk1|k1 Hk1].
  + replace (nat_of_ord k1) with O in Hk1 by now destruct k1 as [[|k1] H].
    destruct (splitP (cast_ord H2 (f (@ord0 (length p))))) as [k2 Hk2|k2 Hk2].
      replace (nat_of_ord k2) with O in Hk2 by now destruct k2 as [[|k2] H].
      exfalso.
      rewrite <- Hk2 in Hk1.
      apply ord_inj in Hk1.
      apply cast_ord_inj in Hk1.
      now apply Hf in Hk1.
    destruct (splitP (cast_ord H2 (f (rshift 1 k)))) as [k3 Hk3|k3 Hk3].
    2: now rewrite Hk1 in Hk3.
    change (onth (rshift 1 k) (h :: p) = onth (ssrnat.addn 1 k2) (h :: q)).
    rewrite Hpq.
    simpl in Hk1, Hk2.
    simpl (length (h :: p)).
    rewrite Hk1, <- Hk2.
    now rewrite <- Hpq.
  + destruct (splitP (cast_ord H2 (f (rshift 1 k)))) as [k2 Hk2|k2 Hk2].
      rewrite Hk1 in Hk2.
      now destruct k2 as [[|k2] H].
    simpl.
    change (onth (rshift 1 k) (h :: p) = onth (ssrnat.addn 1 k2) (h :: q)).
    rewrite <- Hk2.
    apply Hpq.
Qed.

Lemma permut_insert :
  forall v p q,
  permut (v :: p ++ q) (p ++ v :: q).
Proof.
intros v p q.
change (permut (((v :: nil) ++ p) ++ q) (p ++ (v :: nil) ++ q)).
rewrite app_assoc.
apply permut_app_r.
apply permut_app.
Qed.

Lemma permut_remove :
  forall v p q,
  permut (v :: p) q ->
  exists s, exists t,
  q = s ++ v :: t /\ permut p (s ++ t).
Proof.
intros v p q H.
destruct (H) as [Hl f Hf H'].
specialize (H' (@ord0 (length p))).
revert H'.
generalize (nat_of_ord (f (@ord0 (length p)))).
simpl.
intros n.
intros H'.
clear -H H'.
apply eq_sym in H'.
destruct onth_insert with (1 := H') as [r [s Hq]].
exists r, s.
apply (conj Hq).
rewrite Hq in H.
clear -H.
apply permut_cons_rev with v.
apply permut_trans with (1 := H).
apply permut_sym, permut_insert.
Qed.

Lemma Forall_permut :
  forall P p q,
  Forall P p ->
  permut p q ->
  Forall P q.
Proof.
intros P p q.
revert p.
induction q as [|v q IH] ; intros p Hp Hpq.
easy.
assert (Hpv := Hpq).
apply permut_sym, permut_remove in Hpv.
destruct Hpv as [s [t [Hpv Hq]]].
apply permut_sym in Hq.
cut (P v /\ Forall P (s ++ t)).
intros [H1 H2].
apply Forall_cons with (1 := H1).
now apply IH with (2 := Hq).
rewrite Hpv in Hp.
clear -Hp.
induction s as [|h p IH].
simpl in Hp.
now inversion Hp.
inversion_clear Hp.
destruct (IH H0) as [H1 H2].
apply (conj H1).
now apply Forall_cons.
Qed.

Lemma fold_right_permut :
  forall {A} f (acc : A) p q,
  (forall u v w, f u (f v w) = f v (f u w)) ->
  permut p q ->
  fold_right f acc p = fold_right f acc q.
Proof.
intros A f acc p q Hf.
revert acc q.
induction p as [|h p IH] ; intros acc.
  intros [|q].
  easy.
  intros [Hl _ _ _].
  easy.
intros q Hq.
apply permut_remove in Hq.
destruct Hq as [s [t [H1 H2]]].
simpl.
rewrite IH with (1 := H2).
rewrite H1.
clear -Hf.
induction s as [|k s IH].
easy.
simpl.
now rewrite <- IH.
Qed.

Lemma fold_left_permut :
  forall {A} f (acc : A) p q,
  (forall u v w, f (f u v) w = f (f u w) v) ->
  permut p q ->
  fold_left f p acc = fold_left f q acc.
Proof.
intros A f acc p q Hf Hpq.
rewrite <- 2!fold_left_rev_right.
apply fold_right_permut.
now intros u v w.
apply permut_trans with p.
apply permut_rev.
apply permut_trans with (1 := Hpq).
apply permut_sym, permut_rev.
Qed.

End Permut.

Section Pairing.

Context {T : Type}.

Inductive ptree := PTsome (v : T) (l : list ptree).
Inductive pheap := PHnone | PHsome (t : ptree).

Theorem ptree_ind' :
  forall P : ptree -> Prop,
  (forall v l, Forall P l -> P (PTsome v l)) ->
  forall t, P t.
Proof.
intros P H.
fix IH 1.
intros [v l].
apply H.
induction l ; constructor.
apply IH.
apply IHl.
Qed.

Fixpoint ptree_to_list (p : ptree) : list T :=
  match p with
  | PTsome v l => v :: flat_map ptree_to_list l
  end.

Fixpoint pheap_to_list (p : pheap) : list T :=
  match p with
  | PHnone => nil
  | PHsome p => ptree_to_list p
  end.

Variable le : T -> T -> bool.

Definition ptree_meld (p1 p2 : ptree) : ptree :=
  match p1, p2 with
  | PTsome v1 l1, PTsome v2 l2 =>
    if le v1 v2 then PTsome v1 (p2 :: l1)
    else PTsome v2 (p1 :: l2)
  end.

Theorem ptree_meld_correct :
  forall p1 p2,
  permut (ptree_to_list (ptree_meld p1 p2)) (ptree_to_list p1 ++ ptree_to_list p2).
Proof.
intros [v1 l1] [v2 l2].
unfold ptree_meld.
case le ; simpl.
- apply permut_cons.
  apply (permut_app (v2 :: flat_map _ _)).
- apply permut_insert with (p := v1 :: flat_map _ _).
Qed.

Definition ptree_insert (p : ptree) (v : T) :=
  ptree_meld p (PTsome v nil).

Theorem ptree_insert_correct :
  forall p v,
  permut (ptree_to_list (ptree_insert p v)) (v :: ptree_to_list p).
Proof.
intros [v1 l1] v.
unfold ptree_insert.
eapply permut_trans.
apply ptree_meld_correct.
apply (permut_app _ (v :: nil)).
Qed.

Definition pheap_insert (p : pheap) (v : T) : ptree :=
  match p with
  | PHnone => PTsome v nil
  | PHsome p => ptree_insert p v
  end.

Theorem pheap_insert_correct :
  forall p v,
  permut (ptree_to_list (pheap_insert p v)) (v :: pheap_to_list p).
Proof.
intros [|p] v.
apply permut_refl.
apply ptree_insert_correct.
Qed.

Fixpoint ptree_merge_pairs (p1 : ptree) (l : list ptree) : ptree :=
  match l with
  | nil => p1
  | p2 :: nil => ptree_meld p1 p2
  | p2 :: p3 :: l' => ptree_meld (ptree_meld p1 p2) (ptree_merge_pairs p3 l')
  end.

Lemma list_ind2 :
  forall A (P : list A -> Prop),
  P nil ->
  (forall v, P (v :: nil)) ->
  (forall v w l, P l -> P (v :: w :: l)) ->
  forall l, P l.
Proof.
intros A P H0 H1 H12.
fix aux 1.
intros [|v [|w l]].
easy.
easy.
apply H12.
apply aux.
Qed.

Theorem ptree_merge_pairs_correct :
  forall p l,
  permut (ptree_to_list (ptree_merge_pairs p l)) (ptree_to_list p ++ flat_map ptree_to_list l).
Proof.
intros p l.
revert p.
induction l as [|v|v w l IH] using list_ind2 ; simpl ; intros p.
rewrite app_nil_r.
apply permut_refl.
rewrite app_nil_r.
apply ptree_meld_correct.
eapply permut_trans.
apply ptree_meld_correct.
rewrite app_assoc.
eapply permut_trans.
apply permut_app_r.
apply ptree_meld_correct.
now apply permut_app_l.
Qed.

Definition ptree_pop (p : ptree) : T * pheap :=
  match p with
  | PTsome v l => (v,
    match l with
    | nil => PHnone
    | lh :: lt => PHsome (ptree_merge_pairs lh lt)
    end)
  end.

Theorem ptree_pop_correct :
  forall p,
  match ptree_pop p with
  | (v, PHnone) => ptree_to_list p = v :: nil
  | (v, PHsome q) => permut (ptree_to_list p) (v :: ptree_to_list q)
  end.
Proof.
intros [v [|l]].
easy.
simpl.
apply permut_cons.
apply permut_sym.
apply ptree_merge_pairs_correct.
Qed.

Fixpoint ptree_fold {A} (f : A -> T -> A) (p : ptree) (acc : A) : A :=
  match p with
  | PTsome v l => fold_left (fun acc q => ptree_fold f q acc) l (f acc v)
  end.

Theorem ptree_fold_correct :
  forall A (f : A -> T -> A) acc p,
  ptree_fold f p acc = fold_left f (ptree_to_list p) acc.
Proof.
intros A f acc p.
revert acc.
induction p as [v l IH] using ptree_ind'.
simpl.
intros acc.
generalize (f acc v).
clear acc.
induction IH as [|q l H1 _ H2] ; simpl ; intros acc.
easy.
rewrite fold_left_app.
rewrite H2.
now apply f_equal.
Qed.

End Pairing.

Arguments ptree : clear implicits.
Arguments pheap : clear implicits.
