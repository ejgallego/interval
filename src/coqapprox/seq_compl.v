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

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Missing results about natural numbers *)

Section NatCompl.

Lemma nat_ind_gen (P : nat -> Prop) :
  (forall x, (forall y, (y < x)%N -> P y) -> P x) -> (forall x, P x).
Proof.
move=> H x.
suff [H1 H2] : P x /\ (forall y, (y < x)%N -> P y) by done.
elim: x =>[|x [Hx IH]]; first by split; [apply: H|] => y Hy.
split; [apply: H|]=> y; rewrite ltnS => Hy; case: (leqP x y) => Hxy.
- suff<-: x = y by done. by apply: anti_leq; rewrite Hxy Hy.
- exact: IH.
- suff<-: x = y by done. by apply: anti_leq; rewrite Hxy Hy.
- exact: IH.
Qed.

Lemma predn_leq (m n : nat) : m <= n -> m.-1 <= n.-1.
Proof. by case: m n =>[//|m] [//|n]; rewrite ltnS. Qed.

Lemma ltn_subr (m n p : nat) : m < n -> n - p.+1 < n.
Proof.
rewrite subnS => Hn.
case Ek: (n-p)=>[//|k] /=; first exact: leq_trans _ Hn.
apply: leq_trans (leq_trans _ (_ : k.+1 <= n - p)) (_ : n - p <= n);
  by [ |rewrite Ek|rewrite leq_subr].
Qed.

Lemma minnl (m n : nat) : m <= n -> minn m n = m.
Proof.
move=> Hmn; rewrite /minn; case: ltnP =>// Hnm.
by apply/eqP; rewrite eqn_leq Hmn Hnm.
Qed.

Lemma minnr (m n : nat) : n <= m -> minn m n = n.
Proof.
move=> Hnm; rewrite /minn; case: ltnP =>// Hmn; exfalso.
have: n < n by exact: leq_ltn_trans Hnm Hmn.
by rewrite ltnn.
Qed.

End NatCompl.

(** Missing results about lists (aka sequences) *)

Section Head_Last.
Variables (T : Type) (d : T).

Lemma head_cons : forall s, s <> [::] -> s = head d s :: behead s.
Proof. by case. Qed.

Definition hb s := head d (behead s).

Lemma nth1 : forall s, nth d s 1 = hb s.
Proof. by move=> s; rewrite /hb -nth0 nth_behead. Qed.

Lemma last_rev : forall s, last d (rev s) = head d s.
Proof. by elim=> [//|s IHs]; rewrite rev_cons last_rcons. Qed.

Definition rmlast (l : seq T) := (belast (head d l) (behead l)).
End Head_Last.

Lemma rmlast_cons T (d e f : T) (s : seq T) :
  s <> [::] -> rmlast e (f :: s) = f :: rmlast d s.
Proof. by case: s. Qed.

Section Take.
Variable (T : Type).

Lemma size_take_minn (n : nat) (s : seq T) : size (take n s) = minn n (size s).
Proof.
rewrite size_take.
case: ltnP =>Hn; symmetry; by [apply/minn_idPl; exact: ltnW | apply/minn_idPr].
Qed.

End Take.

Lemma nth_map_dflt (C : Type) (x0 : C) (f : C -> C) (n : nat) (s : seq C) :
  nth x0 (map f s) n = if size s <= n then x0 else f (nth x0 s n).
Proof.
case: (leqP (size s) n); last exact: nth_map.
by move=> ?; rewrite nth_default // size_map.
Qed.

Section Map2.
Variable C : Type.
Variable x0 : C.
Variable op : C -> C -> C.
Fixpoint map2 (s1 : seq C) (s2 : seq C) : seq C :=
  match s1, s2 with
    | _, [::] => s1
    | [::], _ => s2
    | a :: s3, b :: s4 => op a b :: map2 s3 s4
  end.

Lemma size_map2 s1 s2 : size (map2 s1 s2) = maxn (size s1) (size s2).
Proof.
elim: s1 s2 => [|x1 s1 IHs1] s2; case: s2 => [|x2 s2] //=.
by rewrite IHs1 maxnSS.
Qed.

Lemma nth_map2_dflt (n : nat) (s1 s2 : seq C) :
  nth x0 (map2 s1 s2) n =
    match size s1 <= n, size s2 <= n with
    | true, true => x0
    | true, false => nth x0 s2 n
    | false, true => nth x0 s1 n
    | false, false => op (nth x0 s1 n) (nth x0 s2 n)
    end.
Proof.
elim: s1 s2 n => [|x1 s1 IHs1] s2 n; case: s2 => [|x2 s2] //=.
- by rewrite nth_nil.
- case: (leqP (size (x2 :: s2)) n) =>//.
  by move/(nth_default x0)=>->.
- case: (leqP (size (x1 :: s1)) n) =>//.
  by move/(nth_default x0)=>->.
- case: n =>// n; exact: IHs1.
Qed.
End Map2.

Lemma nth_mkseq_dflt (C : Type) (x0 : C) (f : nat -> C) (n i : nat) :
  nth x0 (mkseq f n) i = if n <= i then x0 else f i.
Proof.
case: (leqP n i); last exact: nth_mkseq.
by move=> ?; rewrite nth_default // size_mkseq.
Qed.

Section Fold.
(* Erik: is this still used in the library ? *)
Variables (A B : Type) (f : A -> B).

Lemma foldr_cons (r : seq A) (s : seq B) :
  foldr (fun x acc => f x :: acc) s r = map f r ++ s.
Proof. by elim: r => [//|x r' IHr]; rewrite /= -IHr. Qed.

Corollary foldr_cons0 (r : seq A) :
  foldr (fun x acc => f x :: acc) [::] r = map f r.
Proof. by rewrite foldr_cons cats0. Qed.

Lemma foldl_cons (r : seq A) (s : seq B) :
  foldl (fun acc x => f x :: acc) s r = (catrev (map f r) s).
Proof. by elim: r s => [//|a r' IHr] s; rewrite /= -IHr. Qed.

Corollary foldl_cons0 (r : seq A) :
  foldl (fun acc x => f x :: acc) [::] r = rev (map f r).
Proof. by rewrite foldl_cons. Qed.
End Fold.

(** Generic results to be instantiated for polynomials' opp, add, sub, mul... *)

Section map_proof.
Variables (V T : Type) (Rel : V -> T -> Prop).
Variables (dv : V) (dt : T).
Let RelP sv st := forall k : nat, Rel (nth dv sv k) (nth dt st k).
Variables (vop : V -> V) (top : T -> T).
Hypothesis H0 : Rel dv dt.
Hypothesis H0t : forall v : V, Rel v dt -> Rel (vop v) dt.
Hypothesis H0v : forall t : T, Rel dv t -> Rel dv (top t).
Hypothesis Hop : forall v t, Rel v t -> Rel (vop v) (top t).
Lemma map_correct :
  forall sv st, RelP sv st -> RelP (map vop sv) (map top st).
Proof.
move=> sv st Hnth k; move/(_ k) in Hnth.
rewrite !nth_map_dflt.
do 2![case:ifP]=> A B //; rewrite ?(nth_default _ A) ?(nth_default _ B) in Hnth.
- exact: H0v.
- exact: H0t.
- exact: Hop.
Qed.
End map_proof.

Section map2_proof.
Variables (V T : Type) (Rel : V -> T -> Prop).
Variables (dv : V) (dt : T).
Let RelP sv st := forall k : nat, Rel (nth dv sv k) (nth dt st k).
Variables (vop : V -> V -> V) (top : T -> T -> T).
Hypothesis H0 : Rel dv dt.
Hypothesis H0eq : forall v, Rel v dt -> v = dv.

Hypothesis H0t1 : forall (v1 v2 : V) (t1 : T), Rel v1 t1 ->
                                               Rel v2 dt ->
                                               Rel (vop v1 v2) t1.
Hypothesis H0t2 : forall (v1 v2 : V) (t2 : T), Rel v1 dt ->
                                               Rel v2 t2 ->
                                               Rel (vop v1 v2) t2.
Hypothesis H0v1 : forall (v1 : V) (t1 t2 : T), Rel v1 t1 ->
                                               Rel dv t2 ->
                                               Rel v1 (top t1 t2).
Hypothesis H0v2 : forall (v2 : V) (t1 t2 : T), Rel dv dt ->
                                               Rel v2 t2 ->
                                               Rel v2 (top t1 t2).
Hypothesis Hop : (forall v1 v2 t1 t2, Rel v1 t1 -> Rel v2 t2 -> Rel (vop v1 v2) (top t1 t2)).

Lemma map2_correct :
  forall sv1 sv2 st1 st2,
    RelP sv1 st1 ->
    RelP sv2 st2 ->
    RelP (map2 vop sv1 sv2) (map2 top st1 st2).
Proof using RelP H0 H0t1 H0t2 H0v1 H0v2 Hop H0eq.
move=> sv1 sv2 st1 st2 H1 H2 k; move/(_ k) in H1; move/(_ k) in H2.
rewrite !nth_map2_dflt.
do 4![case:ifP]=> A B C D; rewrite
  ?(nth_default _ A) ?(nth_default _ B) ?(nth_default _ C) ?(nth_default _ D) //
  in H1 H2; try solve [exact: H0t1|exact: H0t2|exact: H0v1|exact: H0v2|exact: Hop].
- rewrite (H0eq H2); exact: H1.
- rewrite (H0eq H1); exact: H2.
Qed.
End map2_proof.

Section fold_proof.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Hypothesis H0 : Rel dv dt.
(*
Let RelP sv st := forall k : nat, Rel (nth dv sv k) (nth dt st k).
Variables (vadd : V -> V -> V) (tadd : T -> T -> T).
Variables (vmul : V -> V -> V) (tmul : T -> T -> T).
*)
Lemma fold_correct A fv ft (s : seq A) :
  (forall a v t, Rel v t -> Rel (fv a v) (ft a t)) ->
  Rel (foldr fv dv s) (foldr ft dt s).
Proof.
move=> Hf.
elim: s => [ | a s IHs]; first exact: H0.
apply: Hf.
exact: IHs.
Qed.
End fold_proof.

Section mkseq_proof.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Let RelP sv st := forall k : nat, Rel (nth dv sv k) (nth dt st k).
Hypothesis H0 : Rel dv dt.
Lemma mkseq_correct fv ft n :
  (forall k : nat, Rel (fv k) (ft k)) ->
  RelP (mkseq fv n) (mkseq ft n).
Proof.
move=> Hk k; rewrite /RelP !nth_mkseq_dflt.
case: ifP=> _.
- exact: H0.
- exact: Hk.
Qed.
End mkseq_proof.
