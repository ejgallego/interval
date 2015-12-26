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
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.bigop MathComp.tuple.
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

(** * Additional lemmas about [seq] *)

Notation nth_defaults := set_nth_default. (* for backward compatibility *)

Lemma head_dflt T (d1 d2 : T) (s : seq T) : 0 < size s -> head d1 s = head d2 s.
Proof. by case: s. Qed.

Lemma last_dflt T (d1 d2 : T) (s : seq T) : 0 < size s -> last d1 s = last d2 s.
Proof. by case: s. Qed.

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

(** * Order-1 recurrences *)

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

Lemma loop1SE n p a s :
  loop1 n.+1 p a s = let c := F a p in loop1 n p.+1 c (c :: s).
Proof. done. Qed.

Lemma loop1E p a s : loop1 0 p a s = s.
Proof. done. Qed.

Lemma size_loop1 n p a s : size (loop1 n p a s) = n + size s.
Proof. by elim: n p a s => [//|n IHn] *; rewrite IHn addSnnS. Qed.

Lemma size_rec1down n : size (rec1down n) = n.+1.
Proof. by case: n => [//|n]; rewrite size_loop1 addn1. Qed.

Lemma size_rec1up n : size (rec1up n) = n.+1.
Proof. by rewrite size_rev size_rec1down. Qed.

Variable d : T.

Lemma head_loop1S n s a p :
  head d s = a ->
  head d (loop1 n.+1 p a s) = F (head d (loop1 n p a s)) (n+p).
Proof.
by elim: n s a p => [_ _ _->//|n IHn s a p H]; rewrite !IHn // addSnnS.
Qed.

Theorem head_loop1 (n p : nat) a s :
  head d s = a ->
  head d (loop1 n p a s) = iteri n (fun i c => F c (i + p)) a.
Proof.
elim: n p a s =>[//|n IHn] p a s H.
move E: (n.+1) => n'.
rewrite /= -{}E IHn //.
clear; elim: n =>[//=|n IHn].
by rewrite /= IHn /= addSnnS.
Qed.

Lemma head_rec1downS n :
  head d (rec1down n.+1) = F (head d (rec1down n)) n.+1.
Proof. by rewrite head_loop1S ?addn1. Qed.

Theorem head_rec1down_loop1 n :
  head d (rec1down n) = head d (loop1 n 1 a0 [:: a0]).
Proof. done. Qed.

(*
Let co k := nth d (rec1up k) k.
Let co' k := last d (rec1up k).
*)

Lemma nth_rec1downS k :
  nth d (rec1down k.+1) 0 = F (nth d (rec1down k) 0) k.+1.
Proof. by rewrite !nth0 head_rec1downS. Qed.

Lemma nth_rec1up_last k : nth d (rec1up k) k = last d (rec1up k).
Proof. by rewrite (last_nth d) size_rec1up. Qed.

Lemma last_rec1up k : last d (rec1up k) = head d (loop1 k 1 a0 [:: a0]).
Proof. by rewrite /rec1up /rec1down last_rev. Qed.

Lemma nth_rec1upS k :
  nth d (rec1up k.+1) k.+1 = F (nth d (rec1up k) k) k.+1.
Proof. by rewrite !nth_rec1up_last !last_rev head_rec1downS. Qed.

Lemma loop1S_ex n p a s :
  exists c, loop1 n.+1 p a s = c :: (loop1 n p a s).
Proof.
elim: n p a s=> [|n IH] p a s; first by exists (F a p).
remember (S n) as n'; simpl.
case: (IH p.+1 (F a p) (F a p :: s))=> [c Hc].
rewrite Hc {}Heqn' /=.
by exists c.
Qed.

Lemma behead_rec1down n : behead (rec1down n.+1) = rec1down n.
Proof. by rewrite /rec1down; case: (loop1S_ex n 1 a0 [:: a0])=> [c ->]. Qed.

Lemma nth_rec1downD d1 p q n :
  nth d1 (rec1down (p+q+n)) (p+q) = nth d1 (rec1down (p+n)) p.
Proof.
elim: q=> [|q IH]; first by rewrite addn0.
by rewrite !addnS addSn -nth_behead behead_rec1down.
Qed.

Lemma nth_rec1downD_dflt2 d1 d2 p q n :
  nth d1 (rec1down (p+q+n)) (p+q) = nth d2 (rec1down (p+n)) p.
Proof.
rewrite nth_rec1downD (nth_defaults d1 d2) // size_rec1down.
by iomega.
Qed.

Lemma nth_rec1down_indep d1 d2 m1 m2 n :
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
  exact: nth_rec1downD_dflt2.
set p := m1 - n in h1' *.
rewrite -h1' addnC.
pose q := m2 - m1.
have Hpq : m2 - n = p + q.
  rewrite /p /q in h2' *.
  by rewrite addnC addnBA // subnK // ltnW.
rewrite Hpq.
have->: m2 = p + q + n by rewrite -Hpq subnK.
symmetry; exact: nth_rec1downD_dflt2.
Qed.

Lemma nth_rec1up_indep d1 d2 m1 m2 n :
  n <= m1 -> n <= m2 ->
  nth d1 (rec1up m1) n = nth d2 (rec1up m2) n.
Proof.
move=> h1 h2.
rewrite !nth_rev; first last.
- by rewrite size_loop1 /=; move: h1 h2; iomega_le.
- by rewrite size_loop1 /=; move: h1 h2; iomega_le.
rewrite !size_loop1 /= !addn1 !subSS.
exact: nth_rec1down_indep.
Qed.

(** For the base case *)

Lemma rec1down_co0 n: nth d (rec1down n) n = a0.
Proof.
elim: n=> [//|n IH].
by rewrite /rec1down; have [c ->] := loop1S_ex n 1 a0 [:: a0].
Qed.

Lemma rec1down_co0' n: last d (rec1down n) = a0.
Proof. by rewrite (last_nth d) size_rec1down; apply: rec1down_co0. Qed.

Lemma rec1up_co0 n : nth d (rec1up n) 0 = a0.
Proof. by rewrite nth_rev size_rec1down // subn1 rec1down_co0. Qed.

Lemma rec1up_co0' n : head d (rec1up n) = a0.
Proof. by rewrite -(nth0 d); apply: rec1up_co0. Qed.

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

Section GenDefix1.

Variables A T : Type.

Variable F : A -> nat -> A. (* may involve symbolic differentiation *)
(** to be instantiated by a function satisfying a(n+1)=F(a(n),n+1). *)

Variable G : A -> nat -> T.
(** to be instantiated by a function satisfying u(N+n)=G(a(n),N+n).
Here, N is the size of the list [init]. *)

Fixpoint gloop1 (n p : nat) (a : A) (s : seq T) {struct n} : seq T :=
  match n with
    | 0 => s
    | m.+1 => let r := G a p in
              let p1 := p.+1 in
              let c := F a p1 in gloop1 m p1 c (r :: s)
  end.

Variable a0 : A.

Variable init : seq T.
(** Remark: [init] can be nil *)

Definition grec1down n :=
  if (n.+1 - size init) is n'.+1
    then gloop1 n'.+1 (size init) a0 (rev init)
    else rev (take n.+1 init).

Lemma grec1downE (n : nat) :
  grec1down n =
  if n >= size init
    then gloop1 (n - size init).+1 (size init) a0 (rev init)
    else rev (take n.+1 init).
Proof.
rewrite /grec1down.
case: (leqP (size init) n)=>H; first by rewrite subSn //.
by move: H; rewrite -subn_eq0; move/eqP->.
Qed.

Definition grec1up n := rev (grec1down n).

Lemma gloop1SE n p a s :
  gloop1 n.+1 p a s =
  let r := G a p in let c := F a p.+1 in gloop1 n p.+1 c (r :: s).
Proof. done. Qed.

Lemma gloop1E p a s : gloop1 0 p a s = s.
Proof. done. Qed.

Lemma size_gloop1 n p a s : size (gloop1 n p a s) = n + size s.
Proof. by elim: n p a s => [//|n IHn] *; rewrite IHn addSnnS. Qed.

Lemma size_grec1down n : size (grec1down n) = n.+1.
Proof.
rewrite /grec1down.
case E: (n.+1 - size init) =>[|k].
  rewrite size_rev size_take.
  move/eqP: E; rewrite subn_eq0 leq_eqVlt.
  case/orP; last by move->.
  move/eqP->; rewrite ifF //.
  by rewrite ltnn.
rewrite size_gloop1 /= -E.
by rewrite size_rev subnK // ltnW // -subn_gt0 E.
Qed.

Lemma size_grec1up n : size (grec1up n) = n.+1.
Proof. by rewrite size_rev size_grec1down. Qed.

Theorem grec1down_init n :
  n < size init ->
  grec1down n = rev (take n.+1 init).
Proof. by rewrite /grec1down -subn_eq0; move/eqP ->. Qed.

Theorem grec1up_init n :
  n < size init ->
  grec1up n = take n.+1 init.
Proof. by rewrite /grec1up /grec1down -subn_eq0; move/eqP ->; rewrite revK. Qed.

Theorem head_grec1down (d : T) (n : nat) :
  size init <= n ->
  head d (grec1down n) =
  head d (gloop1 (n - size init).+1 (size init) a0 (rev init)).
Proof. by move=> Hn; rewrite /grec1down subSn. Qed.

Theorem last_grec1up (d : T) (n : nat) :
  size init <= n ->
  last d (grec1up n) =
  head d (gloop1 (n - size init).+1 (size init) a0 (rev init)).
Proof. by move=> Hn; rewrite /grec1up /grec1down subSn // last_rev. Qed.

Theorem head_gloop1 (d : T) (n p : nat) (a : A) (s : seq T):
  head d (gloop1 n.+1 p a s) = G (iteri n (fun i c => F c (i + p).+1) a) (n + p).
Proof.
elim: n p a s =>[//|n IHn] p a s.
move E: (n.+1) => n'.
rewrite /= -{}E IHn.
congr G; last by rewrite addSnnS.
clear; elim: n =>[//=|n IHn].
by rewrite /= IHn /= addSnnS.
Qed.

Lemma gloop1S_ex n p a s :
  exists c, gloop1 n.+1 p a s = c :: (gloop1 n p a s).
Proof.
elim: n p a s => [|n IH] p a s; first by exists (G a p).
remember (S n) as n'; simpl.
case: (IH p.+1 (F a p.+1) (G a p :: s))=> [c Hc].
rewrite Hc {}Heqn' /=.
by exists c.
Qed.

Theorem behead_grec1down (n : nat) :
  behead (grec1down n.+1) = grec1down n.
Proof.
pose s := rev init.
pose m := size init.
rewrite !grec1downE.
case: (leqP (size init) n) => H.
  rewrite leqW // subSn //.
  have [c Hc] := gloop1S_ex (n - m).+1 m a0 s.
  by rewrite Hc.
rewrite leq_eqVlt in H; case/orP: H; [move/eqP|] => H.
  rewrite -H subnn /= ifT H //.
  by rewrite take_oversize.
rewrite ifF 1?leqNgt ?H //.
by rewrite behead_rev_take // size_Tuple.
Qed.

Lemma nth_grec1downD d1 p q n:
  nth d1 (grec1down (p+q+n)) (p+q) = nth d1 (grec1down (p+n)) p.
Proof.
elim: q=> [|q IH]; first by rewrite addn0.
by rewrite !addnS addSn -nth_behead behead_grec1down.
Qed.

Lemma nth_grec1downD_dflt2 d1 d2 p q n:
  nth d1 (grec1down (p+q+n)) (p+q) = nth d2 (grec1down (p+n)) p.
Proof.
rewrite nth_grec1downD (set_nth_default d1 d2) //.
by rewrite size_grec1down ltnS leq_addr.
Qed.

Theorem nth_grec1down_indep (d1 d2 : T) (m1 m2 n : nat) :
  n <= m1 -> n <= m2 ->
  nth d1 (grec1down m1) (m1 - n) = nth d2 (grec1down m2) (m2 - n).
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
  symmetry; exact: nth_grec1downD_dflt2.
- set p := m2 - n in h2' *.
  rewrite -h2' addnC.
  pose q := m1 - m2.
  have Hpq : m1 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m1 = p + q + n.
    by rewrite -Hpq subnK.
  exact: nth_grec1downD_dflt2.
- rewrite Hm (nth_defaults d1 d2) // size_grec1down.
  exact: leq_ltn_trans (@leq_subr n m2) _.
Qed.

Theorem nth_grec1up_indep (d1 d2 : T) (m1 m2 n : nat) :
  n <= m1 -> n <= m2 ->
  nth d1 (grec1up m1) n = nth d2 (grec1up m2) n.
Proof.
move=> h1 h2; rewrite !nth_rev; try by rewrite size_grec1down.
rewrite !size_grec1down !subSS; exact: nth_grec1down_indep.
Qed.

Lemma nth_grec1up_last (d : T) k : nth d (grec1up k) k = last d (grec1up k).
Proof. by rewrite (last_nth d) size_grec1up. Qed.

End GenDefix1.

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

Definition rec2up n := rev (rec2down n).

Lemma loop2SE n p a b s :
  loop2 n.+1 p a b s = let c := F a b p in loop2 n p.+1 b c (c :: s).
Proof. done. Qed.

Lemma loop2E p a b s : loop2 0 p a b s = s.
Proof. done. Qed.

Lemma size_loop2 n p a b s : size (loop2 n p a b s) = n + size s.
Proof. by elim: n p a b s => [//|n IHn] *; rewrite IHn !addSnnS. Qed.

Lemma size_rec2down n : size (rec2down n) = n.+1.
Proof. by case: n => [//|[//|n]]; rewrite size_loop2 addn2. Qed.

Lemma size_rec2up n : size (rec2up n) = n.+1.
Proof. by rewrite size_rev size_rec2down. Qed.

Variable d : T.

Lemma head_loop2S n s a b p :
  hb d s = a -> head d s = b ->
  let s' := (loop2 n p a b s) in
  head d (loop2 n.+1 p a b s) = F (hb d s') (head d s') (n+p).
Proof.
elim: n s a b p => [|n IHn] s a b p Ha Hb; first by rewrite /= Ha Hb.
by rewrite IHn // addSnnS.
Qed.

Lemma head_rec2downSS n :
  head d (rec2down n.+2) =
  F (hb d (rec2down n.+1)) (head d (rec2down n.+1)) n.+2.
Proof. by case: n => [//|n]; rewrite head_loop2S ?addn2. Qed.

Lemma head_rec2down_loop2 n :
  head d (rec2down n.+1) = head d (loop2 n 2 a0 a1 [:: a1; a0]).
Proof. done. Qed.

Lemma head_rec2down0 :
  head d (rec2down 0) = a0.
Proof. done. Qed.

Lemma behead_loop2 n s a b p : behead (loop2 n.+1 p a b s) = loop2 n p a b s.
Proof. by elim: n s a b p => [//|n IHn] s a b p; rewrite IHn. Qed.

Lemma behead_rec2down n : behead (rec2down n.+1) = rec2down n.
Proof. by case: n => [//|n]; rewrite behead_loop2. Qed.

(* Let coa k := nth d (rec2up k) k.
Let coa' k := last d (rec2up k). *)

Lemma nth_rec2up_last k : nth d (rec2up k) k = last d (rec2up k).
Proof. by case: k => [//|k]; rewrite (last_nth d) size_rec2up. Qed.

Theorem last_rec2up k :
  last d (rec2up k.+1) = head d (loop2 k 2 a0 a1 [:: a1; a0]).
Proof. by rewrite /rec2up /rec2down last_rev. Qed.

Lemma nth_rec2downSS k :
  nth d (rec2down k.+2) 0 =
  F (nth d (rec2down k.+1) 1) (nth d (rec2down k.+1) 0) k.+2.
Proof. by rewrite !nth0 !nth1 head_rec2downSS. Qed.

Lemma nth_rec2downSS' k :
  nth d (rec2down k.+2) 0 =
  F (nth d (rec2down k) 0) (nth d (rec2down k.+1) 0) k.+2.
Proof. by rewrite !nth0 -[rec2down k]behead_rec2down head_rec2downSS. Qed.

Lemma nth_rec2upSS k :
  nth d (rec2up k.+2) k.+2 =
  F (nth d (rec2up k.+1) k) (nth d (rec2up k.+1) k.+1) k.+2.
Proof.
by rewrite /rec2up !nth_rev ?size_rec2down // !subnn subSnn nth_rec2downSS.
Qed.

Lemma nth_rec2upSS' k :
  nth d (rec2up k.+2) k.+2 =
  F (nth d (rec2up k) k) (nth d (rec2up k.+1) k.+1) k.+2.
Proof.
by rewrite /rec2up !nth_rev ?size_rec2down // !subnn nth_rec2downSS'.
Qed.

Lemma loop2S_ex n p a b s :
  exists c, loop2 n.+1 p a b s = c :: (loop2 n p a b s).
Proof.
elim: n p a b s => [|n IH] p a b s.
  simpl.
  by exists (F a b p).
remember (S n) as n'; simpl.
case: (IH p.+1 b (F a b p) (F a b p :: s))=> [c Hc].
rewrite Hc {}Heqn' /=.
by exists c.
Qed.

Lemma behead_rec2down_again n :
  behead (rec2down n.+1) = rec2down n.
Proof.
case: n => [//|n]; rewrite /rec2down.
case: (loop2S_ex n 2 a0 a1 [:: a1; a0])=> [c Hc].
by rewrite Hc.
Qed.

Lemma nth_rec2downD d1 p q n :
  nth d1 (rec2down (p+q+n)) (p+q) = nth d1 (rec2down (p+n)) p.
Proof.
elim: q=> [|q IH]; first by rewrite addn0.
by rewrite !addnS addSn -nth_behead behead_rec2down.
Qed.

Lemma nth_rec2downD_dflt2 d1 d2 p q n :
  nth d1 (rec2down (p+q+n)) (p+q) = nth d2 (rec2down (p+n)) p.
Proof.
rewrite nth_rec2downD (nth_defaults d1 d2) // size_rec2down.
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
  exact: nth_rec2downD_dflt2.
- set p := m1 - n in h1' *.
  rewrite -h1' addnC.
  pose q := m2 - m1.
  have Hpq : m2 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m2 = p + q + n by rewrite -Hpq subnK.
symmetry; exact: nth_rec2downD_dflt2.
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

Lemma rec2down_co0 n : nth d (rec2down n) n = a0.
Proof.
elim: n => [//|n IH].
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

Lemma rec2down_co1 n : nth d (rec2down n.+1) n = a1.
Proof.
elim: n => [//|n IH]; case: n IH=> [//|n IH]; rewrite /rec2down.
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
Definition snd' {A B} (ab : A * B) := let (a,b) := ab in b.

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

Lemma size_recNdown n : size (recNdown n) = n.+1.
Proof.
rewrite /recNdown.
case E: (n.+1 - N) =>[|k].
  rewrite size_rev size_take size_Tuple.
  move/eqP: E; rewrite subn_eq0 leq_eqVlt.
  case/orP; last by move->.
  move/eqP->; rewrite ifF //.
  by rewrite ltnn.
rewrite nuncurry_ncurry size_loopN /= -addSnnS -E rev'E size_rev size_Tuple.
by rewrite subnK // ltnW // -subn_gt0 E.
Qed.

Lemma size_recNup n : size (recNup n) = n.+1.
Proof. by rewrite size_rev size_recNdown. Qed.

End DefixN.

Theorem recNdown_init (T : Type) (N : nat)
  (init : T ^ N) (F : T ^^ N --> (nat -> T)) (F1 := nuncurry F) (n : nat) :
  n < N ->
  recNdown init F n = rev (take n.+1 (Ttoseq init)).
Proof. by rewrite /recNdown -subn_eq0; move/eqP ->. Qed.

Theorem recNup_init (T : Type) (N : nat)
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

Lemma nth_recNdownD (T : Type) (m : nat)
  (init : T ^ m) (F : T ^^ m --> (nat -> T))
  (d1 : T) (p q n : nat) :
  nth d1 (recNdown init F (p+q+n)) (p+q) = nth d1 (recNdown init F (p+n)) p.
Proof.
elim: q=> [|q IHq]; first by rewrite addn0.
rewrite !addnS addSn -nth_behead behead_recNdown; exact: IHq.
Qed.

Lemma nth_recNdownD_dflt2 (T : Type) (m : nat)
  (init : T ^ m) (F : T ^^ m --> (nat -> T))
  (d1 d2 : T) (p q n : nat) :
  nth d1 (recNdown init F (p+q+n)) (p+q) = nth d2 (recNdown init F (p+n)) p.
Proof.
rewrite nth_recNdownD (nth_defaults d1 d2) // size_recNdown -addSn.
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
  symmetry; exact: nth_recNdownD_dflt2.
- set p := m2 - n in h2' *.
  rewrite -h2' addnC.
  pose q := m1 - m2.
  have Hpq : m1 - n = p + q.
    rewrite /p /q in h2' *.
    by rewrite addnC addnBA // subnK // ltnW.
  rewrite Hpq.
  have->: m1 = p + q + n.
    by rewrite -Hpq subnK.
  exact: nth_recNdownD_dflt2.
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
apply (f_equal (fun v => nuncurry F' (lastN d N'.+1 (rev v)) n)).
case: (n - N'.+1) =>[|//]; by rewrite nuncurry_const.
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
rewrite (@nth_rec1up_indep _ _ _ d d _ k); try exact: ltnW || exact: leqnn.
move => IHk.
rewrite (@nth_rec1up_indep _ _ _ d d _ k.+1) //.
rewrite nth_rec1upS IHk /fact_rec.
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
rewrite (@nth_rec1up_indep _ _ _ d d _ k); try exact: ltnW || exact: leqnn.
move => IHk.
rewrite (@nth_rec1up_indep _ _ _ d d _ k.+1) //.
rewrite nth_rec1upS IHk /falling_rec.
rewrite big_nat_recr //=.
congr Z.mul.
zify; ring.
Qed.

End RecZ.

(** Refinement proofs for rec1, rec2, grec1 *)

Section rec_proofs.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Hypothesis H0 : Rel dv dt.
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).

Lemma grec1up_correct (A := seq V) Fi (F : A -> nat -> A) Gi (G : A -> nat -> V) ai a si s n :
  (forall qi q m, RelP q qi -> RelP (F q m) (Fi qi m)) ->
  (forall qi q m, RelP q qi -> Rel (G q m) (Gi qi m)) ->
  RelP a ai ->
  RelP s si ->
  size s = size si ->
  RelP (grec1up F G a s n) (grec1up Fi Gi ai si n).
Proof.
move=> HF HG Ha Hs Hsize k.
pose s1 := (size (grec1up F G a s n)).-1.
case: (ltnP n k) => Hnk; first by rewrite !nth_default ?size_grec1up.
have H1 : k = (size (grec1up F G a s k)).-1 by rewrite size_grec1up.
have H2 : k = (size (grec1up Fi Gi ai si k)).-1 by rewrite size_grec1up.
rewrite ?(@nth_grec1up_indep _ _ _ _ _ _ dv dv n k k)
  ?(@nth_grec1up_indep _ _ _ _ _ _ dt dt n k k) //.
case: (ltnP k (size s)) => Hk.
- have Hki : k < size si by rewrite -Hsize.
  rewrite ?(grec1up_init _ _ _ Hk, grec1up_init _ _ _ Hki) ?nth_take_dflt ltnn.
  exact: Hs.
- have Hki : size si <= k by rewrite -Hsize.
  rewrite {4}H2 {2}H1 !nth_last !last_grec1up ?head_gloop1 // Hsize.
  apply: HG => j; set l := k - size si.
  elim: l j => [|l IHl] j /=; by [apply: Ha | apply: HF; apply: IHl].
Qed.

Lemma rec1up_correct fi f fi0 f0 n :
  (forall ai a m, Rel a ai -> Rel (f a m) (fi ai m)) ->
  Rel f0 fi0 ->
  RelP (rec1up f f0 n) (rec1up fi fi0 n).
Proof.
move=> Hf Hf0 k.
case: (ltnP n k) => Hnk; first by rewrite !nth_default ?size_rec1up.
have H1 : k = (size (rec1up f f0 k)).-1 by rewrite size_rec1up.
have H2 : k = (size (rec1up fi fi0 k)).-1 by rewrite size_rec1up.
rewrite (@nth_rec1up_indep _ _ _ dv dv n k k) //
        (@nth_rec1up_indep _ _ _ dt dt n k k) //.
rewrite !(nth_rec1up_last, last_rec1up).
rewrite !head_loop1 //.
elim: k Hnk {H1 H2} => [|k IHk] Hnk //=.
apply: Hf; apply: IHk; exact: ltnW.
Qed.

Lemma rec2up_correct fi f fi0 f0 fi1 f1 n :
  (forall ai bi a b m, Rel a ai -> Rel b bi -> Rel (f a b m) (fi ai bi m)) ->
  Rel f0 fi0 ->
  Rel f1 fi1 ->
  RelP (rec2up f f0 f1 n) (rec2up fi fi0 fi1 n).
Proof.
move=> Hf Hf0 Hf1 k.
case: (ltnP n k) => Hn; first by rewrite !nth_default ?size_rec2up.
have H1 : k = (size (rec2up f f0 f1 k)).-1 by rewrite size_rec2up.
have H2 : k = (size (rec2up fi fi0 fi1 k)).-1 by rewrite size_rec2up.
rewrite (@nth_rec2up_indep _ _ _ _ dv dv n k k) //
        (@nth_rec2up_indep _ _ _ _ dt dt n k k) //.
case: k Hn {H1 H2} => [//|k] Hn.
rewrite !(nth_rec2up_last, last_rec2up).
elim: k {-2}k (leqnn k) Hn => [|k IHk] k' Hk' Hn.
- by rewrite leqn0 in Hk'; move/eqP: Hk'->.
- rewrite leq_eqVlt in Hk'; case/orP: Hk'=> Hk'; last exact: IHk =>//.
  move/eqP: (Hk')->; rewrite !head_loop2S //; apply: Hf.
  + case: k IHk Hn Hk' => [|k] IHk Hn Hk' //.
    rewrite /hb !behead_loop2.
    apply: IHk =>//.
    move/eqP in Hk'; rewrite Hk' in Hn; apply: ltnW; exact: ltnW.
  + apply: IHk =>//.
    move/eqP in Hk'; rewrite Hk' in Hn; exact: ltnW.
Qed.

End rec_proofs.
