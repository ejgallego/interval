(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2014, ENS de Lyon and Inria.

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

Require Import ZArith.
Require Import NaryFunctions.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype tuple.
Require Import seq_compl.

(** This theory extends [NaryFunctions] (from Coq's standard library),
relying on an SSReflect formalization style. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Arguments nprod_to_list [A n] _.
Arguments nprod_of_list [A] _.
Arguments nuncurry [A B n] _ _.
Arguments ncurry [A B n] _.
Arguments napply_discard _ [B] _ _.

Definition Ttoseq := nprod_to_list.
Definition Tofseq := nprod_of_list.

Section NaryTuple.

Variables (n : nat) (T : Type).

Lemma Ttoseq_inj : injective (@Ttoseq T n).
Proof.
elim: n; first by case; case.
by move=> n' IHn [a1 t1][a2 t2] [H1 H2]; congr pair =>//; apply: IHn.
Qed.

Definition Tsize of (T ^ n) := n.

Lemma size_Tuple (t : T ^ n) : size (Ttoseq t) = n.
Proof. by elim: n t =>[//|n' IHn] t; case: t =>[t1 t2] /=; rewrite IHn. Qed.

End NaryTuple.

(** Close section to generalize w.r.t. [n]. *)

Section NaryTuple1.

Variables (n : nat) (T : Type).

Implicit Type t : T ^ n.

Lemma TofseqK l : Ttoseq (@Tofseq T l) = l.
Proof.
elim: l =>[//|x l IHl]; apply: eq_from_nth @x _ _ _ _; rewrite size_Tuple //.
by case=> [//|i Hi]; rewrite /= IHl.
Qed.

Lemma Tnth_default t : 'I_n -> T.
Proof. by rewrite -(size_Tuple t); case: (Ttoseq t)=>[|//] []. Qed.

Definition Tnth t i := nth (Tnth_default t i) (Ttoseq t) i.

Lemma Tnth_nth (x0 : T) t i : Tnth t i = nth x0 (Ttoseq t) i.
Proof. by apply: set_nth_default; rewrite size_Tuple. Qed.

Lemma map_Tnth_enum t : map (Tnth t) (enum 'I_n) = Ttoseq t.
Proof.
case def_t: {-}(Ttoseq t) => [|x0 t'].
  by rewrite [enum _]size0nil // -cardE card_ord -(size_Tuple t) def_t.
apply: (@eq_from_nth _ x0) => [|i]; rewrite size_map.
  by rewrite -cardE size_Tuple card_ord.
move=> lt_i_e; have lt_i_n: i < n by rewrite -cardE card_ord in lt_i_e.
by rewrite (nth_map (Ordinal lt_i_n)) // (Tnth_nth x0) nth_enum_ord.
Qed.

Lemma eq_from_Tnth (t1 t2 : T ^ n) : Tnth t1 =1 Tnth t2 -> t1 = t2.
Proof.
by move/eq_map=> eq_t; apply: Ttoseq_inj; rewrite /= -!map_Tnth_enum eq_t.
Qed.

End NaryTuple1.

Notation "[ 'Tuple' 'of' s ]" := (Tofseq s)
  (at level 0, format "[ 'Tuple'  'of'  s ]") : form_scope.

Notation "[ 'Tnth' t i ]" := (Tnth t (@Ordinal (Tsize t) i (erefl true)))
  (at level 0, t, i at level 8, format "[ 'Tnth'  t  i ]") : form_scope.

Definition cons_Tuple n T : T -> T ^ n -> T ^ n.+1 := @pair T (T ^ n).

Notation "[ 'Tuple' ]" := (tt : _ ^ 0)
  (at level 0, format "[ 'Tuple' ]") : form_scope.

Notation "[ 'Tuple' x ]" := (cons_Tuple x [Tuple])
  (at level 0, format "[ 'Tuple'  x ]") : form_scope.

Notation "[ 'Tuple' x1 ; .. ; xn ]" := (cons_Tuple x1 ( .. [Tuple xn] .. ))
  (at level 0, format "[ 'Tuple' '['  x1 ; '/'  .. ; '/'  xn ']' ]")
  : form_scope.

Section NaryTupleCast.

Variable (T : Type).

Definition Tcast m n (eq_mn : m = n) t := ecast i (T ^ i) eq_mn t.

Lemma TcastE m n (eq_mn : m = n) t i :
  Tnth (Tcast eq_mn t) i = Tnth t (cast_ord (esym eq_mn) i).
Proof. by case: n / eq_mn in i *; rewrite cast_ord_id. Qed.

Lemma Tcast_id n (eq_nn : n = n) t : Tcast eq_nn t = t.
Proof. by rewrite (eq_axiomK eq_nn). Qed.

Lemma TcastK m n (eq_mn : m = n) : cancel (Tcast eq_mn) (Tcast (esym eq_mn)).
Proof. by case: n / eq_mn. Qed.

Lemma TcastKV m n (eq_mn : m = n) : cancel (Tcast (esym eq_mn)) (Tcast eq_mn).
Proof. by case: n / eq_mn. Qed.

Lemma Tcast_trans m n p (eq_mn : m = n) (eq_np : n = p) t :
  Tcast (etrans eq_mn eq_np) t = Tcast eq_np (Tcast eq_mn t).
Proof. by case: n / eq_mn eq_np; case: p /. Qed.

Lemma TtoseqK n (t : T ^ n) : Tofseq (Ttoseq t) = Tcast (esym (size_Tuple t)) t.
Proof.
case: n t =>[|n]; first by case=>/=; rewrite Tcast_id.
case; fold nprod =>[x0 t']; apply: eq_from_Tnth => i.
by rewrite TcastE !(Tnth_nth x0) /= TofseqK.
Qed.

End NaryTupleCast.

Section NaryTupleMap.

Variables (T rT : Type) (f : T -> rT).

Fixpoint map_Tuple n (t : T ^ n) {struct n} : rT ^ n :=
  match n, t with
  | 0, _ => [Tuple]
  | S n', (x0, t') => cons_Tuple (f x0) (@map_Tuple n' t')
  end.

Lemma Ttoseq_map n (t : T ^ n) :
  Ttoseq (map_Tuple t) = map f (Ttoseq t).
Proof. by elim: n t =>[//|n IHn] [x0 t'] /=; rewrite IHn. Qed.

Lemma Tnth_map_Tuple n (t : T ^ n) i : Tnth (map_Tuple t) i = f (Tnth t i).
Proof.
elim: n t i =>[//|n IHn] t i; first by case i.
rewrite (Tnth_nth (map_Tuple t).1) (Tnth_nth t.1).
by rewrite (Ttoseq_map t) (nth_map t.1) // size_Tuple.
Qed.

End NaryTupleMap.

Section NaryTupleSeq.

Variables (n : nat) (T : Type).

Implicit Type t : T ^ n.

Definition Thead (u : T ^ n.+1) := Tnth u ord0.

Lemma Tnth0 (x : T) t : Tnth (cons_Tuple x t) ord0 = x.
Proof. done. Qed.

Lemma TheadE x t : Thead (cons_Tuple x t) = x.
Proof. done. Qed.

Lemma Tuple0 : all_equal_to ([Tuple] : T ^ 0).
Proof. by move=> t; apply: Ttoseq_inj. Qed.

Lemma Tuple0eq (H : n = 0) : all_equal_to (Tcast (esym H) ([Tuple] : T^0)).
Proof. by case: n H =>[|//] H; rewrite Tcast_id; apply: Tuple0. Qed.

Fixpoint nseq_Tuple n T (x : T) {struct n} : T ^ n :=
  match n with
  | 0 => [Tuple]
  | S n' => cons_Tuple x (nseq_Tuple n' x)
  end.

Lemma Ttoseq_nseq (x : T) : Ttoseq (nseq_Tuple n x) = nseq n x.
Proof. by elim: n =>[//|n' IHn'] /=; rewrite IHn'. Qed.

Fixpoint iota_Tuple p m {struct p} : nat ^ p :=
  match p with
  | 0 => [Tuple]
  | S p' => cons_Tuple m (iota_Tuple p' m.+1)
  end.

Lemma Ttoseq_iota p m : Ttoseq (iota_Tuple p m) = iota m p.
Proof. by elim: p m =>[//|p IHp] m /=; rewrite IHp. Qed.

End NaryTupleSeq.

Section Tuplify.
(** Conversions between [Tuple] and Ssreflect's [tuple]. *)

Variables (T : Type).

Fixpoint tuplify n (t : T ^ n) : n.-tuple T :=
  match n, t with
  | 0, _ => [tuple]
  | S _, (x, t') => cons_tuple x (tuplify t')
  end.

Fixpoint Tuplify n (t : n.-tuple T) : T ^ n :=
  match n, t with
  | 0, _ => [Tuple]
  | S n', _ => cons_Tuple (thead t) (Tuplify (behead_tuple t))
  end.

Lemma tnth_tuplify n (t : T ^ n) i : tnth (tuplify t) i = Tnth t i.
Proof.
elim: n i t =>[|n IHn] i t; first by case: i.
case: t; fold nprod =>[x0 t']; rewrite (tnth_nth x0) (Tnth_nth x0).
case: i =>[i Hi]; case: i x0 t' Hi =>[//=|i] x0 t' Hi /=; rewrite ltnS in Hi.
by rewrite [i]/(val (Ordinal Hi)) -(Tnth_nth x0) -(tnth_nth x0) IHn.
Qed.

Lemma Tnth_Tuplify n (t : n.-tuple T) i : Tnth (Tuplify t) i = tnth t i.
Proof.
elim: n i t =>[|n IHn] i t; first by case: i.
rewrite (tuple_eta t); set x0 := thead t.
rewrite (tnth_nth x0) (Tnth_nth x0).
case: i =>[i Hi]; case: i t @x0 Hi =>[//=|i] t x0 Hi /=; rewrite ltnS in Hi.
rewrite [i]/(val (Ordinal Hi)) -(Tnth_nth x0) -(tnth_nth x0) IHn.
by rewrite [in RHS](tuple_eta t).
Qed.

Lemma tuplifyK n : cancel (@tuplify n) (@Tuplify n).
Proof.
move=> t; apply: eq_from_Tnth => i.
by rewrite Tnth_Tuplify tnth_tuplify.
Qed.

Lemma TuplifyK n : cancel (@Tuplify n) (@tuplify n).
Proof.
move=> t; apply: eq_from_tnth => i.
by rewrite tnth_tuplify Tnth_Tuplify.
Qed.

Lemma Ttoseq_Tuplify n (t : n.-tuple T) :
  Ttoseq (Tuplify t) = val t.
Proof.
elim: n t =>[|n IHn] t /=; [by rewrite tuple0 | rewrite -[t in RHS]TuplifyK].
apply: (@eq_from_nth _ (thead t)); first by rewrite /= size_Tuple size_tuple.
by move=> i Hi /=; rewrite IHn /= TuplifyK.
Qed.

Lemma val_tuplify n (t : T ^ n) :
  val (tuplify t) = Ttoseq t.
Proof.
elim: n t =>[//|n IHn] t; rewrite -[t in RHS]tuplifyK.
apply: (@eq_from_nth _ (Thead t)); first by rewrite /= size_Tuple size_tuple.
by move=> i Hi /=; rewrite -IHn /= TuplifyK -head_cons //; case: (t).
Qed.

End Tuplify.

Section NaryTupleMk.

Variable n : nat.

Definition ord_Tuple : 'I_n ^ n := Tuplify (ord_tuple n).

Lemma Ttoseq_ord_Tuple : Ttoseq (ord_Tuple) = enum 'I_n.
Proof. by rewrite /ord_Tuple Ttoseq_Tuplify. Qed.

Lemma Tnth_ord_Tuple i : Tnth (ord_Tuple) i = i.
Proof.
apply: val_inj; rewrite (Tnth_nth i) -(nth_map _ 0) ?size_Tuple //.
by rewrite Ttoseq_ord_Tuple val_enum_ord nth_iota.
Qed.

Variable U : Type.

Lemma Tuple_map_ord (t : U ^ n) : t = map_Tuple (Tnth t) (ord_Tuple).
Proof.
by apply: Ttoseq_inj; rewrite Ttoseq_map Ttoseq_ord_Tuple map_Tnth_enum.
Qed.

Variable (f : 'I_n -> U).

(** Non-computational function to build a Tuple from an expression. *)
Definition mkTupleO := map_Tuple f (ord_Tuple).

Lemma Tnth_mkTupleO i : Tnth mkTupleO i = f i.
Proof. by rewrite /mkTupleO Tnth_map_Tuple Tnth_ord_Tuple. Qed.

Lemma nth_mkTupleO (x0 : U) (i : 'I_n) : nth x0 (Ttoseq mkTupleO) i = f i.
Proof. by rewrite -Tnth_nth Tnth_mkTupleO. Qed.

End NaryTupleMk.

Section NaryTupleMkNat.

Variables (U : Type) (f : nat -> U) (n : nat).

(** Computational function to build a Tuple from an expression. *)
Definition mkTuple := map_Tuple f (iota_Tuple n 0).

Lemma Tnth_mkTuple (i : 'I_n) : Tnth (mkTuple) i = f i.
Proof.
rewrite /mkTuple; case: n i =>[|p] i; first by case: i.
by rewrite Tnth_map_Tuple (Tnth_nth 0) Ttoseq_iota nth_iota.
Qed.

Lemma nth_mkTuple (x0 : U) (i : nat) : i < n -> nth x0 (Ttoseq mkTuple) i = f i.
Proof. by move=> Hi; rewrite [i]/(val (Ordinal Hi)) -Tnth_nth Tnth_mkTuple. Qed.

End NaryTupleMkNat.

Notation "[ 'Tuple' F | i < n ]" := (mkTupleO (fun i : 'I_n => F))
  (at level 0, i at level 0,
   format "[ '[hv' 'Tuple'  F '/'   |  i  <  n ] ']'") : form_scope.

Notation "[ 'Tuple' F | 0 <= i < n ]" := (mkTuple (fun i : nat => F) n)
  (at level 0, i at level 0,
   format "[ '[hv' 'Tuple'  F '/'   |  0  <=  i  <  n ] ']'") : form_scope.

(** Note that the term represented by the notation [ [Tuple F | 0 <= i < n] ]
can be evaluated: it roughly correspond to [mkseq (fun i => F) n] for Tuples. *)

(* Eval compute in [Tuple 20-i|0<=i<5]. *)

Section takeN_lastN.

Variables (T : Type) (d : T).

Fixpoint takeN (n : nat) (s : seq T) {struct n} : T ^ n :=
  match n with
    | O => [Tuple]
    | S n' =>
      match s with
        | [::] => cons_Tuple d (takeN n' [::])
        | x :: s' => cons_Tuple x (takeN n' s')
      end
  end.

Lemma Ttoseq_takeN (n : nat) (s : seq T) :
  n <= size s -> Ttoseq (takeN n s) = take n s.
Proof.
elim: n s =>[|n IHn] s H; first by rewrite take0.
by case: s H =>[//|x s'] H /=; rewrite IHn.
Qed.

(** Stronger lemma w.r.t. [Ttoseq_takeN]. *)
Lemma Ttoseq_takeN' (n : nat) (s : seq T) :
  Ttoseq (takeN n s) = take n s ++ nseq (n - size s) d.
Proof.
elim: n s =>[|n IHn] s; first by rewrite take0.
by case: s =>[//|x s'] /=; rewrite IHn //= subn0.
Qed.

Lemma takeN_Ttoseq (n : nat) (t : T ^ n) : takeN n (Ttoseq t) = t.
Proof.
elim: n t =>[|n IHn]; first by case.
by case; fold nprod; move=> t0 t'; rewrite /= IHn.
Qed.

Definition lastN (n : nat) (s : seq T) : T ^ n :=
  takeN n (drop (size s - n) s).

Lemma lastN_Ttoseq (n : nat) (t : T ^ n) : lastN n (Ttoseq t) = t.
Proof. by rewrite /lastN size_Tuple subnn drop0 takeN_Ttoseq. Qed.

Lemma Ttoseq_lastN_drop (n : nat) (s : seq T) :
  n <= size s -> Ttoseq (lastN n s) = take n (drop (size s - n) s).
Proof. by move=> H; rewrite /lastN Ttoseq_takeN // size_drop subKn. Qed.

Lemma take_drop_rev (n : nat) (s : seq T) :
  take n (drop (size s - n) s) = rev (take n (rev s)).
Proof.
case: (leqP n (size s)) => Hn.
  apply: (@eq_from_nth _ d).
    rewrite size_rev !size_take_minn size_drop size_rev subKn //.
    by rewrite minnn (minn_idPl Hn).
  move=> i.
  rewrite size_take_minn size_drop subKn // minnn => Hi.
  rewrite nth_rev; last by rewrite size_take_minn size_rev (minn_idPl Hn).
  rewrite !nth_take //; last first.
    rewrite size_take_minn size_rev (minn_idPl Hn); exact: (ltn_subr _ Hi).
  rewrite nth_drop nth_rev size_take_minn size_rev (minn_idPl Hn); last first.
    exact: leq_trans (ltn_subr _ Hi) Hn.
  rewrite subnSK // subnBA; last exact: ltnW.
  by rewrite addnC addnBA // addnC.
rewrite (eqP (ltnW Hn)) drop0 !take_oversize ?revK //.
  by rewrite size_rev ltnW.
exact: ltnW.
Qed.

Lemma Ttoseq_lastN_rev (n : nat) (s : seq T) :
  n <= size s -> Ttoseq (lastN n s) = rev (take n (rev s)).
Proof. by move=> Hn; rewrite Ttoseq_lastN_drop // take_drop_rev. Qed.

(** Stronger lemma w.r.t. [Ttoseq_lastN_drop]. *)
Lemma Ttoseq_lastN_drop' (n : nat) (s : seq T) :
  Ttoseq (lastN n s) = take n (drop (size s - n) s) ++ nseq (n - size s) d.
Proof.
rewrite /lastN Ttoseq_takeN' // size_drop.
case: (leqP (size s) n) => H.
  by rewrite (eqP (_ : (leq (size s) n))) // subn0.
rewrite subKn; last exact: ltnW.
rewrite (eqP (_ : (leq n (size s)))) // ?subnn //; exact: ltnW.
Qed.

(** Stronger lemma w.r.t. [Ttoseq_lastN_rev]. *)
Lemma Ttoseq_lastN_rev' (n : nat) (s : seq T) :
  Ttoseq (lastN n s) = rev (take n (rev s)) ++ nseq (n - size s) d.
Proof. by rewrite Ttoseq_lastN_drop' // take_drop_rev. Qed.

Lemma Tnth_lastN (n : nat) (i : 'I_n) (s : seq T) :
  Tnth (lastN n s) i = nth d s (size s - n + val i).
Proof.
rewrite (Tnth_nth d).
rewrite Ttoseq_lastN_drop'.
rewrite nth_cat size_take_minn size_drop.
case: (leqP (size s) n) => H.
  rewrite (eqP H) subn0 minnr //.
  case: ltnP => H'; first by rewrite nth_take // drop0 add0n.
  by rewrite nth_nseq if_same nth_default.
rewrite (eqP (ltnW H)).
have Hlt := ltn_ord i.
rewrite ifT; last by rewrite -minnE [minn n _]minnl // minnr // ltnW.
by rewrite nth_take // nth_drop.
Qed.

End takeN_lastN.
