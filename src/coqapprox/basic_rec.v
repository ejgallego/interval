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
Require Import Rfunctions. (* for fact_simpl *)
Require Import NaryFunctions.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop tuple.
Require Import seq_compl nary_tuple.

(*
This library defines polymorphic definitions rec1up (resp. rec2up) that
make it possible to compute the list [:: u(0); u(1);...; u(n)] for
a given function u defined by an order-1 (resp. order-2) recurrence.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac flatten := repeat
  first[rewrite<-pred_of_minus in *| rewrite<-plusE in *|rewrite<-minusE in *].
Ltac iomega := intros; flatten; (omega || apply/leP; omega).
Ltac iomega_le := (repeat move/leP=>?); iomega.

Section Defix1.

Variable T : Type.

Variable F : T -> nat -> T.
(** to be instantiated by a function satisfying u(n) = F(u(n-1), n). *)

Fixpoint loop1 (n p : nat) (a : T) (s : seq T) {struct n} : seq T :=
  match n with
    | 0 => s
    | m.+1 => let c := F a p in loop1 m p.+1 c (c :: s)
  end.

Variable a0 : T.

Definition rec1down n := loop1 n 1 a0 [:: a0].

Definition rec1up n := rev (rec1down n).

Lemma loop1SE :
  forall n p a s,
  (loop1 n.+1 p a s) = let c := F a p in loop1 n p.+1 c (c :: s).
Proof. done. Qed.

Lemma loop1E : forall p a s, (loop1 0 p a s) = s.
Proof. done. Qed.

Lemma size_loop1 : forall n p a s, size (loop1 n p a s) = n + size s.
Proof. by elim=> [//|n IHn] *; rewrite IHn addSnnS. Qed.

Lemma size_rec1down : forall n, size (rec1down n) = n.+1.
Proof. by case=> [//|n]; rewrite size_loop1 addn1. Qed.

Lemma size_rec1up n : size (rec1up n) = n.+1.
Proof. by rewrite size_rev size_rec1down. Qed.

Variable d : T.

Lemma head_loop1 :
  forall n s a p, head d s = a ->
  head d (loop1 n.+1 p a s) = F (head d (loop1 n p a s)) (n+p).
Proof.
by elim=> [_ _ _->//|n IHn s a p H]; rewrite !IHn // addSnnS.
Qed.

Lemma head_rec1down n :
  head d (rec1down n.+1) = F (head d (rec1down n)) n.+1.
Proof. by rewrite head_loop1 ?addn1. Qed.

(*
Let co k := nth d (rec1up k) k.
Let co' k := last d (rec1up k).
*)

Lemma rec1up_nth_last k : nth d (rec1up k) k = last d (rec1up k).
Proof. by rewrite (last_nth d) size_rec1up. Qed.

Lemma rec1down_correct k :
  nth d (rec1down k.+1) 0 = F (nth d (rec1down k) 0) k.+1.
Proof. by rewrite !nth0 head_rec1down. Qed.

Lemma rec1up_correct k :
  nth d (rec1up k.+1) k.+1 = F (nth d (rec1up k) k) k.+1.
Proof.
by rewrite !rec1up_nth_last !last_rev head_rec1down.
Qed.

Lemma nth_defaults d1 d2 (s : seq T) n :
    n < size s -> nth d1 s n = nth d2 s n.
Proof. exact: set_nth_default. Qed.

Lemma loop1S_ex :
  forall n p a s, exists c,
  loop1 n.+1 p a s = c :: (loop1 n p a s).
Proof.
elim=> [|n IH] p a s; first by exists (F a p).
remember (S n) as n'; simpl.
case: (IH p.+1 (F a p) (F a p :: s))=> [c Hc].
rewrite Hc {}Heqn' /=.
by exists c.
Qed.

Lemma behead_rec1down n: behead (rec1down n.+1) = rec1down n.
Proof.
rewrite /rec1down.
by case: (loop1S_ex n 1 a0 [:: a0])=> [c ->].
Qed.

Lemma nth_rec1down d1 p q n:
  nth d1 (rec1down (p+q+n)) (p+q) = nth d1 (rec1down (p+n)) p.
Proof.
elim: q=> [|q IH]; first by rewrite addn0.
by rewrite !addnS addSn -nth_behead behead_rec1down.
Qed.

Lemma nth_rec1down_dflt2 d1 d2 p q n:
  nth d1 (rec1down (p+q+n)) (p+q) = nth d2 (rec1down (p+n)) p.
Proof.
rewrite nth_rec1down (nth_defaults d1 d2) // size_rec1down.
by iomega.
Qed.

Lemma rec1down_nth_indep d1 d2 m1 m2 n:
  n <= m1 -> n <= m2 ->
  nth d1 (rec1down m1) (m1 - n) = nth d2 (rec1down m2) (m2 - n).
Proof.
move=> h1 h2.
have h1' := subnKC h1; have h2' := subnKC h2.
case: (ltngtP m1 m2)=> Hm; last first.
- by rewrite Hm (nth_defaults d1 d2) // size_rec1down; iomega.
- set p := m2 - n in h2' *.
  rewrite -h2' addnC.
  pose q := m1 - m2.
  have Hpq : m1 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m1 = p + q + n by rewrite -Hpq subnK.
  exact: nth_rec1down_dflt2.
set p := m1 - n in h1' *.
rewrite -h1' addnC.
pose q := m2 - m1.
have Hpq : m2 - n = p + q.
  rewrite /p /q in h2' *.
  by rewrite addnC addnBA // subnK // ltnW.
rewrite Hpq.
have->: m2 = p + q + n by rewrite -Hpq subnK.
symmetry; exact: nth_rec1down_dflt2.
Qed.

Lemma rec1up_nth_indep d1 d2 m1 m2 n :
  n <= m1 -> n <= m2 ->
  nth d1 (rec1up m1) n = nth d2 (rec1up m2) n.
Proof.
move=> h1 h2.
rewrite !nth_rev; first last.
- by rewrite size_loop1 /=; move: h1 h2; iomega_le.
- by rewrite size_loop1 /=; move: h1 h2; iomega_le.
rewrite !size_loop1 /= !addn1 !subSS.
exact: rec1down_nth_indep.
Qed.

(** For the base case *)

Lemma rec1down_co0 n: nth d (rec1down n) n = a0.
Proof.
elim: n=> [|n IH]; first done.
by rewrite /rec1down; have [c ->] := loop1S_ex n 1 a0 [:: a0].
Qed.

Lemma rec1down_co0' n: last d (rec1down n) = a0.
Proof.
rewrite (last_nth d) size_rec1down.
exact: rec1down_co0.
Qed.

Lemma rec1up_co0 n : nth d (rec1up n) 0 = a0.
Proof.
by rewrite nth_rev size_rec1down // subn1 rec1down_co0.
Qed.

Lemma rec1up_co0' n : head d (rec1up n) = a0.
Proof.
by rewrite -(nth0 d); exact: rec1up_co0.
Qed.

End Defix1.

Section Test1.

Let n_rec (a0 : nat) (n : nat) := n.
(** Eval compute in rec1up n_rec 17 5. *)

Let fact_rec a n := (a * n)%N.
Let fact n := rec1up fact_rec 1%N n.
(** Eval compute in fact 8. *)

Let factz_rec a n := (a * (Z_of_nat n))%Z.
Definition factz n := rec1up factz_rec 1%Z n.
(** Eval compute in factz 100. *)

End Test1.

Section Defix2.

Variable T : Type.

Variable F : T -> T -> nat -> T.
(** to be instantiated by a function satisfying u(n) = F(u(n-2), u(n-1), n). *)

Fixpoint loop2 (n p : nat) (a b : T) (s : seq T) {struct n} : seq T :=
  match n with
    | 0 => s
    | m.+1 => let c := F a b p in loop2 m p.+1 b c (c :: s)
  end.

Variables a0 a1 : T.

Definition rec2down n :=
  if n is n'.+1 then (loop2 n' 2 a0 a1 [:: a1; a0]) else [:: a0].

Definition rec2up n := (rev (rec2down n)).

Lemma loop2E :
  forall n p a b s,
    (loop2 n.+1 p a b s) = let c := F a b p in loop2 n p.+1 b c (c :: s).
Proof. done. Qed.

Lemma size_loop2 : forall n p a b s, size (loop2 n p a b s) = n + size s.
Proof. by elim=> [//|n IHn] *; rewrite IHn !addSnnS. Qed.

Lemma size_rec2down : forall n, size (rec2down n) = n.+1.
Proof. by case=> [//|[//|n]]; rewrite size_loop2 addn2. Qed.

Lemma size_rec2up n : size (rec2up n) = n.+1.
Proof. by rewrite size_rev size_rec2down. Qed.

Variable d : T.

Lemma head_loop2 :
  forall n s a b p, hb d s = a -> head d s = b ->
    let s' := (loop2 n p a b s) in
      head d (loop2 n.+1 p a b s) = F (hb d s') (head d s') (n+p).
Proof.
elim; first by move=> s a b p Ha Hb; rewrite /= Ha Hb.
by move=> n IHn s a b p Ha Hb; rewrite IHn // addSnnS.
Qed.

Lemma head_rec2down :
  forall n, head d (rec2down n.+2) =
    F (hb d (rec2down n.+1)) (head d (rec2down n.+1)) n.+2.
Proof. by case=> [//|n]; rewrite head_loop2 ?addn2. Qed.

Lemma behead_loop2 :
  forall n s a b p, behead (loop2 n.+1 p a b s) = loop2 n p a b s.
Proof. by elim=>// [n IHn s a b p]; rewrite IHn. Qed.

Lemma behead_rec2down :
  forall n, behead (rec2down n.+1) = rec2down n.
Proof.
by case=> [//|n]; rewrite behead_loop2.
Qed.

(* Let coa k := nth d (rec2up k) k.
Let coa' k := last d (rec2up k). *)

Lemma rec2up_nth_last : forall k, nth d (rec2up k) k = last d (rec2up k).
Proof.
by case=> [//|k]; rewrite (last_nth d) size_rec2up.
Qed.

Lemma rec2down_correct k :
  nth d (rec2down k.+2) 0 =
  F (nth d (rec2down k.+1) 1) (nth d (rec2down k.+1) 0) k.+2.
Proof.
by rewrite !nth0 !nth1 head_rec2down.
Qed.

Lemma rec2down_correct' k :
  nth d (rec2down k.+2) 0 =
  F (nth d (rec2down k) 0) (nth d (rec2down k.+1) 0) k.+2.
Proof.
by rewrite !nth0 -[rec2down k]behead_rec2down head_rec2down.
Qed.

(** Relying on rec2down_correct *)
Lemma rec2up_correct k :
    nth d (rec2up k.+2) k.+2 =
    F (nth d (rec2up k.+1) k) (nth d (rec2up k.+1) k.+1) k.+2.
Proof.
by rewrite /rec2up !nth_rev ?size_rec2down // !subnn subSnn rec2down_correct.
Qed.

(** Relying on rec2down_correct' *)
Lemma rec2up_correct' k :
    nth d (rec2up k.+2) k.+2 =
    F (nth d (rec2up k) k) (nth d (rec2up k.+1) k.+1) k.+2.
Proof.
by rewrite /rec2up !nth_rev ?size_rec2down // !subnn rec2down_correct'.
Qed.

Lemma loop2S_ex :
  forall n p a b s, exists c,
  loop2 n.+1 p a b s = c :: (loop2 n p a b s).
Proof.
elim=> [|n IH] p a b s.
  simpl.
  by exists (F a b p).
remember (S n) as n'; simpl.
case: (IH p.+1 b (F a b p) (F a b p :: s))=> [c Hc].
rewrite Hc {}Heqn' /=.
by exists c.
Qed.

Lemma behead_rec2down_again :
  forall n,
  behead (rec2down n.+1) = rec2down n.
Proof.
case=> [|n]; first done.
unfold rec2down.
case: (loop2S_ex n 2 a0 a1 [:: a1; a0])=> [c Hc].
by rewrite Hc.
Qed.

Lemma nth_rec2down d1 p q n :
  nth d1 (rec2down (p+q+n)) (p+q) = nth d1 (rec2down (p+n)) p.
Proof.
elim: q=> [|q IH]; first by rewrite addn0.
by rewrite !addnS addSn -nth_behead behead_rec2down.
Qed.

Lemma nth_rec2down_dflt2 d1 d2 p q n :
  nth d1 (rec2down (p+q+n)) (p+q) = nth d2 (rec2down (p+n)) p.
Proof.
rewrite nth_rec2down (nth_defaults d1 d2) // size_rec2down.
by iomega.
Qed.

Lemma nth_rec2down_indep d1 d2 m1 m2 n : n <= m1 -> n <= m2 ->
  nth d1 (rec2down m1) (m1 - n) = nth d2 (rec2down m2) (m2 - n).
Proof.
move=> h1 h2.
have h1' := subnKC h1; have h2' := subnKC h2.
case: (ltngtP m1 m2)=> Hm; last first.
- rewrite Hm (nth_defaults d1 d2) //.
  by rewrite size_rec2down; iomega.
- set p := m2 - n in h2' *.
  rewrite -h2' addnC.
  pose q := m1 - m2.
  have Hpq : m1 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m1 = p + q + n by rewrite -Hpq subnK.
  exact: nth_rec2down_dflt2.
- set p := m1 - n in h1' *.
  rewrite -h1' addnC.
  pose q := m2 - m1.
  have Hpq : m2 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m2 = p + q + n by rewrite -Hpq subnK.
symmetry; exact: nth_rec2down_dflt2.
Qed.

Lemma nth_rec2up_indep d1 d2 m1 m2 n : n <= m1 -> n <= m2 ->
  nth d1 (rec2up m1) n = nth d2 (rec2up m2) n.
Proof.
move=> h1 h2.
rewrite !nth_rev; first last.
- by rewrite size_rec2down /=; move: h1 h2; iomega_le.
- by rewrite size_rec2down /=; move: h1 h2; iomega_le.
rewrite !size_rec2down /= !subSS.
exact: nth_rec2down_indep.
Qed.

(** For the base case *)

Lemma rec2down_co0 : forall n, nth d (rec2down n) n = a0.
Proof.
elim=> [//|n IH].
case: n IH=> [//|n IH].
rewrite /rec2down.
have [c Hc] := loop2S_ex n 2 a0 a1 [:: a1; a0].
by rewrite Hc.
Qed.

Lemma rec2up_co0 n : nth d (rec2up n) 0 = a0.
Proof.
rewrite nth_rev.
  by rewrite size_rec2down subn1 /= rec2down_co0.
by rewrite size_rec2down.
Qed.

Lemma rec2down_co1 : forall n, nth d (rec2down n.+1) n = a1.
Proof.
elim=> [//|n IH]; case: n IH=> [//|n IH]; rewrite /rec2down.
by have [c ->] := loop2S_ex n.+1 2 a0 a1 [:: a1; a0].
Qed.

Lemma rec2up_co1 n : nth d (rec2up n.+1) 1 = a1.
Proof.
rewrite nth_rev.
  by rewrite size_rec2down subn2 /= rec2down_co1.
by rewrite size_rec2down.
Qed.

End Defix2.

Section Test2.

Let foo2_rec (a b : Z*nat) (n : nat) := (a.1 + b.1, n)%Z.
Let foo2 n := rec2up foo2_rec (Z0,O) (1%Z,1%N) n.
(** Eval compute in foo2 5. *)

Let fibz_rec (a b : Z) (_ : nat) := (a + b)%Z.
Definition fibz n := rec2up fibz_rec 0%Z 1%Z n.
(** Eval compute in fibz 5. *)

End Test2.

(** Define some "aliases" for the purposes of partial-evaluation. *)
Definition snd' := Eval unfold snd in snd.

Fixpoint catrev' T (s1 s2 : seq T) {struct s1} : seq T :=
  match s1 with
  | [::] => s2
  | x :: s1' => catrev' s1' (x :: s2)
  end.
Definition rev' {T} (s : seq T) := nosimpl (catrev' s [::]).

Lemma rev'E T : @rev' T =1 @rev T.
Proof.
rewrite /rev' /rev.
move=> s; elim: s [::] =>[//|x s IHs] s' /=; by rewrite IHs.
Qed.

Definition hide_let (A B : Type) (a : A) (v : A -> B) := let x := a in v x.

(** Define a function to make a Tuple slide, popping the left-most component. *)
Fixpoint slideN_aux (T : Type) (c : T) (n0 : nat) : T ^ n0 -> T ^ S n0 :=
  match n0 return (T ^ n0 -> T ^ S n0) with
    | 0 => fun _ : T ^ 0 => (c, tt)
    | S n1 => fun b0 : T ^ S n1 =>
        let (a, b') := b0 in cons_Tuple a (@slideN_aux T c n1 b')
  end.

Definition slideN (T : Type) (n : nat) (b : T ^ n) (c : T) : T ^ n :=
  snd' (@slideN_aux T c n b).

Section DefixN.

Variable T : Type.

Variable N : nat.

Variable init : T ^ N.

Variable F : T ^^ N --> (nat -> T).
Let F1 := nuncurry F.
(** The variable [F] can be instantiated by a function representing the sequence
[u(n) = F(u(n-N),..., u(n-1), n)]. *)

Fixpoint loopN (n : nat) (p : nat) : (T ^^ N --> (seq T -> seq T)) :=
  match n with
    | O => napply_discard T (fun x : seq T => x) N
    | S n' =>
      ncurry
      (fun (t : T ^ N) (l : seq T) =>
        hide_let (F1 t p) (fun v1 =>
          nuncurry (loopN n' p.+1) (slideN t v1) (v1 :: l)))
  end.

Definition recNdown n :=
  if (n.+1-N) is n'.+1
    then (nuncurry (loopN n'.+1 N) init (rev' (Ttoseq init)))
    else rev (take n.+1 (Ttoseq init)).

Lemma recNdownE (n : nat) :
  recNdown n =
  if n>=N
    then (nuncurry (loopN (n-N).+1 N) init (rev (Ttoseq init)))
    else rev (take n.+1 (Ttoseq init)).
Proof.
rewrite /recNdown; case: (leqP N n) => H; first by rewrite rev'E subSn.
by move: H; rewrite -subn_eq0; move/eqP->.
Qed.

Definition recNup n := rev (recNdown n).

Lemma nuncurry_const (B : Type) (b : B) (n : nat) (d : T ^ n) :
  (nuncurry (napply_discard T b n) d) = b.
Proof. by elim: n d =>[//|n IHn] [d0 d]; rewrite /= IHn. Qed.

Lemma nuncurry_ncurry (A B : Type) (n : nat) (f : A ^ n -> B) (x : A ^ n) :
  nuncurry (ncurry f) x = f x.
Proof. by elim: n f x =>[f[]//|n IHn f x]; case: x=>[x0 x]; rewrite /= IHn. Qed.

Lemma loopNE (n p : nat) t s :
  nuncurry (loopN n.+1 p) t s = let c := F1 t p in
  nuncurry (loopN n p.+1) (slideN t c) (c :: s).
Proof. by rewrite nuncurry_ncurry. Qed.

Lemma size_loopN (n p : nat) t s :
  size (nuncurry (loopN n p) t s) = n + size s.
Proof.
elim: n p t s => [//|n IHn] p t s; first by rewrite /= nuncurry_const.
by rewrite nuncurry_ncurry IHn addSnnS.
Qed.

Lemma size_recNdown : forall n, size (recNdown n) = n.+1.
Proof.
rewrite /recNdown => n.
case E: (n.+1 - N) =>[|k].
  rewrite size_rev size_take size_Tuple.
  move/eqP: E; rewrite subn_eq0 leq_eqVlt.
  case/orP; last by move->.
  move/eqP->; rewrite ifF //.
  by rewrite ltnn.
rewrite nuncurry_ncurry size_loopN /= -addSnnS -E rev'E size_rev size_Tuple.
by rewrite subnK // ltnW // -subn_gt0 E.
Qed.

Lemma size_recNup : forall n, size (recNup n) = n.+1.
Proof. by move=> n; rewrite size_rev size_recNdown. Qed.

End DefixN.

Theorem recNdown_init_correct (T : Type) (N : nat)
  (init : T ^ N) (F : T ^^ N --> (nat -> T)) (F1 := nuncurry F) (n : nat) :
  n < N ->
  recNdown init F n = rev (take n.+1 (Ttoseq init)).
Proof. by rewrite /recNdown -subn_eq0; move/eqP ->. Qed.

Theorem recNup_init_correct (T : Type) (N : nat)
  (init : T ^ N) (F : T ^^ N --> (nat -> T)) (F1 := nuncurry F) (n : nat) :
  n < N ->
  recNup init F n = take n.+1 (Ttoseq init).
Proof.
Proof. by rewrite /recNup /recNdown -subn_eq0; move/eqP ->; rewrite revK. Qed.

Lemma Ttoseq_slideN_aux (m : nat) (T : Type) (t : T ^ m) (c : T) :
  Ttoseq (slideN_aux c t) = rcons (Ttoseq t) c.
Proof.
elim: m t c =>[//|m IHm] t c.
case: t; fold nprod; move=> a t /=.
case E: (slideN_aux c t)=>[a' t']; fold nprod in t'.
by rewrite -IHm; congr cons; rewrite E.
Qed.

Lemma Ttoseq_slideN (m : nat) (T : Type) (t : T ^ m) (c : T) :
  Ttoseq (slideN t c) = behead (rcons (Ttoseq t) c).
Proof. by rewrite -Ttoseq_slideN_aux /slideN; case: slideN_aux. Qed.

Lemma loopNS_ex (T : Type) (m : nat)
  (F : T ^^ m --> (nat -> T)) (F1 := nuncurry F)
  (n p : nat) (t : T ^ m) (s : seq T) :
  exists c, nuncurry (loopN F n.+1 p) t s = c :: (nuncurry (loopN F n p) t s).
Proof.
elim: n p t s => [|n IH] p t s.
  by exists (F1 t p); rewrite nuncurry_ncurry /hide_let !nuncurry_const.
move En' : (S n) => n'; rewrite nuncurry_ncurry /hide_let.
case: (IH p.+1 (slideN t (F1 t p)) (F1 t p :: s))=> [c Hc].
by exists c; rewrite -{}En' Hc nuncurry_ncurry.
Qed.

Lemma behead_rcons (T : Type) (s : seq T) (x : T) :
  s <> [::] -> behead (rcons s x) = rcons (behead s) x.
Proof. by case: s. Qed.

Lemma behead_rev_take (T : Type) (s : seq T) (n : nat) :
  n <= size s -> behead (rev (take n s)) = rev (take n.-1 s).
Proof.
elim: n s =>[//|n IHn] [//|x s] H //.
rewrite ltnS -/size in H.
rewrite /=.
case: n IHn H =>[//|n] /= IHn H; first by rewrite take0 //.
rewrite [in RHS]rev_cons -IHn // rev_cons behead_rcons //.
move/(f_equal size).
fold (@take T); fold (@size T) in H.
rewrite size_rev size_take.
case: leq =>//=.
by move=> top; rewrite top in H.
Qed.

(* Erik: We could also provide a lemma behead_loopN *)

Lemma behead_recNdown (T : Type) (m : nat)
  (init : T ^ m) (F : T ^^ m --> (nat -> T)) (F1 := nuncurry F) (n : nat) :
  behead (recNdown init F n.+1) = recNdown init F n.
Proof.
pose s := rev (Ttoseq init).
rewrite !recNdownE.
case: (leqP m n) => H.
  rewrite leqW // subSn //.
  have [c Hc] := loopNS_ex F (n - m).+1 m init s.
  by rewrite /= Hc /= nuncurry_ncurry /hide_let /=.
rewrite leq_eqVlt in H; case/orP: H; [move/eqP|] => H.
  rewrite -{4}H subnn /= ifT H //.
  rewrite nuncurry_ncurry /hide_let /= nuncurry_const /=.
  by rewrite take_oversize ?size_Tuple.
rewrite ifF 1?leqNgt ?H //.
by rewrite behead_rev_take // size_Tuple.
Qed.

Lemma nth_recNdown (T : Type) (m : nat)
  (init : T ^ m) (F : T ^^ m --> (nat -> T))
  (d1 : T) (p q n : nat) :
  nth d1 (recNdown init F (p+q+n)) (p+q) = nth d1 (recNdown init F (p+n)) p.
Proof.
elim: q=> [|q IHq]; first by rewrite addn0.
rewrite !addnS addSn -nth_behead behead_recNdown; exact: IHq.
Qed.

Lemma nth_recNdown_dflt2 (T : Type) (m : nat)
  (init : T ^ m) (F : T ^^ m --> (nat -> T))
  (d1 d2 : T) (p q n : nat) :
  nth d1 (recNdown init F (p+q+n)) (p+q) = nth d2 (recNdown init F (p+n)) p.
Proof.
rewrite nth_recNdown (nth_defaults d1 d2) // size_recNdown -addSn.
exact: ltn_addr.
Qed.

Section ProofN.

Variables (T : Type) (N : nat)
  (init : T ^ N) (F : T ^^ N --> (nat -> T)).

Theorem nth_recNdown_indep (d1 d2 : T) (m1 m2 n : nat) :
  n <= m1 -> n <= m2 ->
  nth d1 (recNdown init F m1) (m1 - n) = nth d2 (recNdown init F m2) (m2 - n).
Proof.
move=> h1 h2.
have h1' := subnKC h1; have h2' := subnKC h2.
case: (ltngtP m1 m2)=> Hm.
- set p := m1 - n in h1' *.
  rewrite -h1' addnC.
  pose q := m2 - m1.
  have Hpq : m2 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m2 = p + q + n.
    by rewrite -Hpq subnK.
  symmetry; exact: nth_recNdown_dflt2.
- set p := m2 - n in h2' *.
  rewrite -h2' addnC.
  pose q := m1 - m2.
  have Hpq : m1 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m1 = p + q + n.
    by rewrite -Hpq subnK.
  exact: nth_recNdown_dflt2.
- rewrite Hm (nth_defaults d1 d2) // size_recNdown.
  exact: leq_ltn_trans (@leq_subr n m2) _.
Qed.

Theorem nth_recNup_indep (d1 d2 : T) (m1 m2 n : nat) :
  n <= m1 -> n <= m2 ->
  nth d1 (recNup init F m1) n = nth d2 (recNup init F m2) n.
Proof.
move=> h1 h2; rewrite !nth_rev; try by rewrite size_recNdown.
rewrite !size_recNdown !subSS; exact: nth_recNdown_indep.
Qed.

Lemma slideN_lastN (d : T) (t : T ^ N) (c : T) :
  slideN t c = lastN d N (rev (c :: rev (Ttoseq t))).
Proof.
apply: Ttoseq_inj; rewrite Ttoseq_slideN.
rewrite Ttoseq_lastN_drop size_rev /= size_rev size_Tuple //.
rewrite subSn // subnn drop1 take_oversize -rev_rcons revK //.
by rewrite size_behead size_rcons size_Tuple.
Qed.

Lemma head_loopN (d : T) (n p : nat) (s : seq T) :
  init = lastN d N (rev s) ->
  size s >= N ->
  head d (nuncurry (loopN F n.+1 p) init s) =
  nuncurry F
    (lastN d N
      (rev (nuncurry (loopN F n p) init s)))
    (p+n).
Proof.
elim: n {1 5}n p init (erefl (p+n)) s =>[|n IHn] m q t Hqm s Ht Hs.
  rewrite /= /hide_let !nuncurry_ncurry !nuncurry_const /=.
  by rewrite Hqm Ht addn0.
rewrite Hqm.
move En1: n.+1 => n2.
rewrite /= /hide_let !nuncurry_ncurry.
set t' := slideN t _.
rewrite -En1 -addSnnS (IHn n)//.
- by rewrite /= /hide_let !nuncurry_ncurry.
- rewrite /t' (slideN_lastN d) {2}Ht Ttoseq_lastN_rev ?size_rev // !revK.
  apply: eq_from_Tnth => i; have Hi := ltn_ord i.
  rewrite !(Tnth_nth d) !Ttoseq_lastN_drop; first last.
  + rewrite size_rev /= size_take.
    by case: ltnP =>[//|]; move=> _; apply: leq_trans Hs _.
  + by rewrite size_rev /=; apply: leq_trans Hs _.
  rewrite !nth_take // !nth_drop // !rev_cons !nth_rcons.
  rewrite !size_rcons !size_rev !size_take_minn (minn_idPl Hs).
  have->: N.+1 - N + i = i.+1 by rewrite subSn ?subnn.
  have H1: size s - ((size s).+1 - N + i) = N - i.+1.
    rewrite subSn // addSnnS addnC addnBA // addnC -subnBA // subKn //.
    apply: leq_trans _ Hs; exact: leq_subr.
  rewrite -subn_gt0 -[in RHS]subn_gt0 H1.
  case: ltnP => H0.
    rewrite !nth_rev ?nth_take.
    - by rewrite size_take_minn (minn_idPl Hs) [in RHS]subnS H1 subnS.
    - rewrite size_take_minn (minn_idPl Hs) subnS.
      apply: leq_ltn_trans (@leq_pred _) _.
      rewrite subnSK //; exact: leq_subr.
    - by rewrite -subn_gt0 H1.
    by rewrite size_take_minn (minn_idPl Hs) -subn_gt0.
  have Htr : i < size s by apply: leq_trans Hi Hs.
  case: i Hi H1 H0 Htr =>/= i _ Hi H1 H0 Htr.
  case E : (i.+1 == N); [rewrite ifT|rewrite ifF] =>//.
    apply/eqP; move/eqP: E <-.
    rewrite subSn ?addSn // addnC addnBA // addnC subnS -subnBA //.
    rewrite subnn subn0 prednK //; exact: leq_ltn_trans _ Htr.
  apply/eqP; move/eqP in E.
  move=> Keq; apply: E.
  rewrite addnC addnBA 1?ltnW // addnC addSnnS -addnBA in Keq.
    rewrite -{2}[size s]addn0 in Keq.
    move/eqP: Keq; rewrite eqn_add2l; move/eqP; rewrite -{2}[N]addn0 => <-.
    by rewrite subnKC // -subn_eq0 -leqn0.
  by rewrite -subn_eq0 -leqn0.
by rewrite /= ltnW.
Qed.

End ProofN.

Section ProofN'.

Theorem recNdown_correct T (N : nat) (init : T ^ N) (F : T ^^ N --> (nat -> T))
  (d : T) (n : nat) :
  N <= n ->
  head d (recNdown init F n) =
  nuncurry F (lastN d N (rev (recNdown init F n.-1))) n.
Proof.
case: N init F =>[//|N'] init' F'.
  rewrite /recNdown /loopN head_loopN //= rev'E revK; exact: Tuple0.
move=> H.
rewrite /recNdown !take_oversize; first last.
- by rewrite size_Tuple leqW.
- by rewrite size_Tuple; apply: leq_trans _ (leqSpred n).
rewrite (ltn_predK H) !subSn // ?leqW //.
rewrite head_loopN 1?addnC ?addSn ?(subnK H) rev'E //; first last.
- by rewrite size_rev size_Tuple.
- by rewrite revK lastN_Ttoseq.
repeat f_equal; case: (n - N'.+1) =>[|//]; by rewrite nuncurry_const.
Qed.

Theorem recNup_correct T (N : nat) (init : T ^ N) (F : T ^^ N --> (nat -> T))
  (d : T) (n : nat) :
  N <= n ->
  last d (recNup init F n) =
  nuncurry F (lastN d N (recNup init F n.-1)) n.
Proof. by move=> H; rewrite -recNdown_correct // /recNup last_rev. Qed.

End ProofN'.

Arguments recNup [T] _ _ _ _.
Arguments recNdown [T] _ _ _ _.

(** A tactic to partially evaluate recNdown/recNup. See below for an example. *)

Ltac exactN f := let g :=
  eval lazy zeta beta iota
            delta[nuncurry ncurry Ttoseq nprod_to_list napply_discard
                  slideN slideN_aux cons_Tuple snd' rev' catrev'
                  loopN recNdown recNup Tofseq nprod_of_list f]
  in f in let h :=
  eval lazy beta delta[hide_let] in g
  in exact h.

Section TestN.

Let F (a b : Z) (_ : nat) := (a + b)%Z.
Let Fib2 n := rec2up F 0%Z 1%Z n.
(*
Eval vm_compute in Fib2 0.
Eval vm_compute in Fib2 10.
*)

Let FibN := recNup 2 [Tuple 0%Z; 1%Z] F.
Let FibNc := ncurry (recNup 2) 0%Z 1%Z F.
Let FibNs := recNup 2 [Tuple of [:: 0%Z; 1%Z]] F.
(*
Eval vm_compute in FibN 0.
Eval vm_compute in FibN 10.
Eval vm_compute in FibNc 0.
Eval vm_compute in FibNc 10.
Eval vm_compute in FibNs 0.
Eval vm_compute in FibNs 10.
*)

Let FibN' : nat -> seq Z. exactN FibN. Defined.
Let FibNc' : nat -> seq Z. exactN FibNc. Defined.
Let FibNs' : nat -> seq Z. exactN FibNs. Defined.
(*
Print FibN'. Print FibNc'. Print FibNs'.
Time Eval compute in (fun _ => true) (last Z0 (Fib2 1000)).
Time Eval compute in (fun _ => true) (last Z0 (FibN' 1000)).
*)

End TestN.


Section RecZ.

(* Helper functions to compute
[1/0!; p/1!; ...; p*(p-1)*...*(p-n+1)/n!] *)

Definition fact_rec (a : Z) (n : nat) : Z := Z.mul a (Z.of_nat n).
Definition fact_seq := rec1up fact_rec 1%Z.

Theorem fact_seq_correct (d : Z) (n k : nat) :
  k <= n ->
  nth d (fact_seq n) k = Z.of_nat (fact k).
Proof.
elim: k => [|k IHk] Hkn; first by rewrite rec1up_co0.
move/(_ (ltnW Hkn)) in IHk.
move: IHk.
rewrite /fact_seq.
rewrite (@rec1up_nth_indep _ _ _ d d _ k); try exact: ltnW || exact: leqnn.
move => IHk.
rewrite (@rec1up_nth_indep _ _ _ d d _ k.+1) //.
rewrite rec1up_correct IHk /fact_rec.

rewrite fact_simpl.
zify; ring.
Qed.

Definition falling_rec (p : Z) (a : Z) (n : nat) : Z :=
  (a * (p - (Z.of_nat n) + 1))%Z.
Definition falling_seq (p : Z) := rec1up (falling_rec p) 1%Z.

Canonical Zmul_monoid := Monoid.Law Z.mul_assoc Z.mul_1_l Z.mul_1_r.

Theorem falling_seq_correct (d : Z) (p : Z) (n k : nat) :
  k <= n ->
  nth d (falling_seq p n) k =
  \big[Z.mul/1%Z]_(0 <= i < k) (p - Z.of_nat i)%Z.
Proof.
elim: k => [|k IHk] Hkn; first by rewrite rec1up_co0 big_mkord big_ord0.
move/(_ (ltnW Hkn)) in IHk.
move: IHk.
rewrite /falling_seq.
rewrite (@rec1up_nth_indep _ _ _ d d _ k); try exact: ltnW || exact: leqnn.
move => IHk.
rewrite (@rec1up_nth_indep _ _ _ d d _ k.+1) //.
rewrite rec1up_correct IHk /falling_rec.
rewrite big_nat_recr //=.
congr Z.mul.
zify; ring.
Qed.

End RecZ.
