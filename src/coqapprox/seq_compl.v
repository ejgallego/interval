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

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq MathComp.bigop.

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

Lemma leq_subnK: forall m n : nat, n <= (n - m) + m.
Proof. elim=> [|n IHn] m; first by rewrite addn0 subn0.
rewrite subnS -addSnnS.
move/(_ m) in IHn.
have H := leqSpred (m - n).
apply: leq_trans IHn _.
exact: leq_add H _.
Qed.

Lemma leq_addLR m n p : n <= p -> (m + n <= p) = (m <= p - n).
Proof. by move => H; rewrite -!subn_eq0 subnBA. Qed.

Lemma leq_addLRI m n p : (m + n <= p) -> (m <= p - n).
Proof.
move=> Hmnp.
- have Hnp : n <= p by exact: leq_trans (leq_addl _ _) Hmnp.
- move: Hmnp; rewrite -!subn_eq0 subnBA //.
Qed.

Lemma leq_ltnN m n : m <= n < m = false.
Proof. by apply/andP=> [[_n n_]]; have := leq_trans n_ _n; rewrite ltnn. Qed.

Lemma ltn_leqN m n : m < n <= m = false.
Proof. by apply/andP=> [[_n n_]]; have:= leq_ltn_trans n_ _n; rewrite ltnn. Qed.

End NatCompl.

(** Missing result(s) about bigops *)

Section bigops.
Lemma big_nat_leq_idx :
  forall (R : Type) (idx : R) (op : Monoid.law idx) (m n : nat) (F : nat -> R),
  n <= m -> (forall i : nat, n <= i < m -> F i = idx) ->
  \big[op/idx]_(0 <= i < n) F i = \big[op/idx]_(0 <= i < m) F i.
Proof.
move=> R idx op m n F Hmn H.
rewrite [RHS](big_cat_nat _ (n := n)) //.
rewrite [in X in _ = op _ X]big_nat_cond.
rewrite [in X in _ = op _ X]big1 ?Monoid.mulm1 //.
move=> i; rewrite andbT; move=> *; exact: H.
Qed.
End bigops.

(** Missing results about lists (aka sequences) *)

Section Head_Last.
Variables (T : Type) (d : T).

Lemma head_cons : forall s, s <> [::] -> s = head d s :: behead s.
Proof. by case. Qed.

Definition hb s := head d (behead s).

Lemma nth1 : forall s, nth d s 1 = hb s.
Proof. by move=> s; rewrite /hb -nth0 nth_behead. Qed.

Lemma nth_behead s n : nth d (behead s) n = nth d s n.+1.
Proof. by case: s =>//; rewrite /= nth_nil. Qed.

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
Variable op' : C -> C. (* will be [id] or [opp] *)
Fixpoint map2 (s1 : seq C) (s2 : seq C) : seq C :=
  match s1, s2 with
    | _, [::] => s1
    | [::], b :: s4 => op' b :: map2 [::] s4
    | a :: s3, b :: s4 => op a b :: map2 s3 s4
  end.

Lemma size_map2 s1 s2 : size (map2 s1 s2) = maxn (size s1) (size s2).
Proof.
elim: s1 s2 => [|x1 s1 IHs1] s2; elim: s2 => [|x2 s2 IHs2] //=.
- by rewrite IHs2 !max0n.
- by rewrite IHs1 maxnSS.
Qed.

Lemma nth_map2_dflt (n : nat) (s1 s2 : seq C) :
  nth x0 (map2 s1 s2) n =
    match size s1 <= n, size s2 <= n with
    | true, true => x0
    | true, false => op' (nth x0 s2 n)
    | false, true => nth x0 s1 n
    | false, false => op (nth x0 s1 n) (nth x0 s2 n)
    end.
Proof.
elim: s1 s2 n => [|x1 s1 IHs1] s2 n.
  elim: s2 n => [|x2 s2 /= IHs2] n //=; first by rewrite nth_nil.
  by case: n =>[|n] //=; rewrite IHs2.
case: s2 => [|x2 s2] /=.
  by case: leqP => H; last rewrite nth_default.
case: n => [|n] //=.
by rewrite IHs1.
Qed.
End Map2.

Lemma nth_mkseq_dflt (C : Type) (x0 : C) (f : nat -> C) (n i : nat) :
  nth x0 (mkseq f n) i = if n <= i then x0 else f i.
Proof.
case: (leqP n i); last exact: nth_mkseq.
by move=> ?; rewrite nth_default // size_mkseq.
Qed.

Lemma nth_take_dflt (n0 : nat) (T : Type) (x0 : T) (i : nat) (s : seq T) :
  nth x0 (take n0 s) i = if n0 <= i then x0 else nth x0 s i.
Proof.
case: (leqP n0 i) => Hi; last by rewrite nth_take.
by rewrite nth_default // size_take; case: ltnP=>// H'; apply: leq_trans H' Hi.
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

Lemma eq_foldr (T0 T1 T2 : Type)
  (f0 : T1 -> T0 -> T0)
  (g : T2 -> T0 -> T0) (ftog : T1 -> T2) :
  (forall x y, f0 x y = g (ftog x) y) ->
  forall s x0, foldr f0 x0 s = foldr g x0 (map ftog s).
Proof. by move=> Hfg; elim=> [//| a l IHl] x0 /=; rewrite IHl Hfg. Qed.

(** Generic results to be instantiated for polynomials' opp, add, sub, mul... *)

Section map_proof.
Variables (V T : Type) (Rel : V -> T -> Prop).
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
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
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Variables (vop : V -> V -> V) (vop' : V -> V).
Variables (top : T -> T -> T) (top' : T -> T).
Hypothesis H0 : Rel dv dt.

Hypothesis H0t : forall v : V, Rel v dt -> Rel (vop' v) dt.
Hypothesis H0v : forall t : T, Rel dv t -> Rel dv (top' t).
Hypothesis Hop' : forall v t, Rel v t -> Rel (vop' v) (top' t).

Hypothesis H0eq : forall v, Rel v dt -> v = dv.

Hypothesis H0t1 : forall (v1 v2 : V) (t1 : T), Rel v1 t1 ->
                                               Rel v2 dt ->
                                               Rel (vop v1 v2) t1.
Hypothesis H0t2 : forall (v1 v2 : V) (t2 : T), Rel v1 dt ->
                                               Rel v2 t2 ->
                                               Rel (vop v1 v2) (top' t2).
Hypothesis H0v1 : forall (v1 : V) (t1 t2 : T), Rel v1 t1 ->
                                               Rel dv t2 ->
                                               Rel v1 (top t1 t2).
Hypothesis H0v2 : forall (v2 : V) (t1 t2 : T), Rel dv t1 ->
                                               Rel v2 t2 ->
                                               Rel (vop' v2) (top t1 t2).
Hypothesis Hop : forall v1 v2 t1 t2, Rel v1 t1 -> Rel v2 t2 -> Rel (vop v1 v2) (top t1 t2).

Lemma map2_correct :
  forall sv1 sv2 st1 st2,
    RelP sv1 st1 ->
    RelP sv2 st2 ->
    RelP (map2 vop vop' sv1 sv2) (map2 top top' st1 st2).
Proof using H0 H0t H0v Hop' H0eq H0t1 H0t2 H0v1 H0v2 Hop.
move=> sv1 sv2 st1 st2 H1 H2 k; move/(_ k) in H1; move/(_ k) in H2.
rewrite !nth_map2_dflt.
do 4![case:ifP]=> A B C D; rewrite
  ?(nth_default _ A) ?(nth_default _ B) ?(nth_default _ C) ?(nth_default _ D) //
  in H1 H2; try solve
  [exact: H0t1|exact: H0t2|exact: H0v1|exact: H0v2|exact: Hop'|exact: Hop|exact: H0t|exact: H0v].
- rewrite (H0eq (H0t H2)); exact: H1.
- rewrite (H0eq H1); apply: H0v; exact: H2.
Qed.
End map2_proof.

Section fold_proof.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Hypothesis H0 : Rel dv dt.
Lemma foldr_correct fv ft sv st :
  RelP sv st ->
  (forall xv yv, Rel xv dt -> Rel yv dt -> Rel (fv xv yv) dt) ->
  (forall xt yt, Rel dv xt -> Rel dv yt -> Rel dv (ft xt yt)) ->
  (forall xv xt yv yt, Rel xv xt -> Rel yv yt -> Rel (fv xv yv) (ft xt yt)) ->
  Rel (foldr fv dv sv) (foldr ft dt st).
Proof.
move=> Hs H0t H0v Hf.
elim: sv st Hs => [ | xv sv IH1] st Hs /=.
- elim: st Hs => [ | xt st IH2] Hs //=.
  apply: H0v; first by move/(_ 0): Hs.
  by apply: IH2 => k; move/(_ k.+1): Hs; rewrite /= nth_nil.
- case: st Hs => [ | xt st] Hs /=.
  + apply: H0t; first by move/(_ 0): Hs.
    change dt with (foldr ft dt [::]).
    apply/IH1 => k.
    by move/(_ k.+1): Hs; rewrite /= nth_nil.
  + apply: Hf; first by move/(_ 0): Hs.
    apply: IH1.
    move=> k; by move/(_ k.+1): Hs.
Qed.

Lemma seq_foldr_correct fv ft sv st (zv := [::]) (zt := [::]) :
  RelP sv st ->
  (forall xv yv, Rel xv dt -> RelP yv zt -> RelP (fv xv yv) zt) ->
  (forall xt yt, Rel dv xt -> RelP zv yt -> RelP zv (ft xt yt)) ->
  (forall xv xt yv yt, Rel xv xt -> RelP yv yt -> RelP (fv xv yv) (ft xt yt)) ->
  RelP (foldr fv zv sv) (foldr ft zt st).
Proof.
move=> Hs H0t H0v Hf.
elim: sv st Hs => [ | xv sv IH1] st Hs /=.
- elim: st Hs => [ | xt st IH2] Hs //=.
  apply: H0v; first by move/(_ 0): Hs.
  by apply: IH2 => k; move/(_ k.+1): Hs; rewrite /= nth_nil.
- case: st Hs => [ | xt st] Hs /=.
  + apply: H0t; first by move/(_ 0): Hs.
    change zt with (foldr ft zt [::]).
    apply/IH1 => k.
    by move/(_ k.+1): Hs; rewrite /= nth_nil.
  + apply: Hf; first by move/(_ 0): Hs.
    apply: IH1.
    move=> k; by move/(_ k.+1): Hs.
Qed.
(*
Lemma foldr_correct A fv ft (s : seq A) :
  (forall a v t, Rel v t -> Rel (fv a v) (ft a t)) ->
  Rel (foldr fv dv s) (foldr ft dt s).
Proof.
move=> Hf.
elim: s => [ | a s IHs]; first exact: H0.
apply: Hf.
exact: IHs.
Qed.
Lemma foldl_correct A fv ft (s : seq A) :
  (forall a v t, Rel v t -> Rel (fv v a) (ft t a)) ->
  Rel (foldl fv dv s) (foldl ft dt s).
Proof.
move=> Hf.
rewrite -(revK s) !foldl_rev.
apply: foldr_correct.
exact: Hf.
Qed.
*)
End fold_proof.

Section Foldri.
Variables (T R : Type) (f : T -> nat -> R -> R) (z0 : R).

Fixpoint foldri (s : seq T) (i : nat) : R :=
  match s with
  | [::] => z0
  | x :: s' => f x i (foldri s' i.+1)
  end.
End Foldri.

Section foldri_proof.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Hypothesis H0 : Rel dv dt.
Lemma seq_foldri_correct fv ft sv st (zv := [::]) (zt := [::]) i :
  RelP sv st ->
  (* RelP zv zt -> *)
  (forall xv yv i, Rel xv dt -> RelP yv zt -> RelP (fv xv i yv) zt) ->
  (forall xt yt i, Rel dv xt -> RelP zv yt -> RelP zv (ft xt i yt)) ->
  (forall xv xt yv yt i, Rel xv xt -> RelP yv yt -> RelP (fv xv i yv) (ft xt i yt)) ->
  RelP (foldri fv zv sv i) (foldri ft zt st i).
Proof.
move=> Hs H0t H0v Hf.
elim: sv st Hs i => [ | xv sv IH1] st Hs i /=.
- elim: st Hs i => [ | xt st IH2] Hs i //=.
  apply: H0v; first by move/(_ 0): Hs.
  by apply: IH2 => k; move/(_ k.+1): Hs; rewrite /= nth_nil.
- case: st Hs => [ | xt st] Hs /=.
  + apply: H0t; first by move/(_ 0): Hs.
    change zt with (foldri ft zt [::] i.+1).
    apply/IH1 => k.
    by move/(_ k.+1): Hs; rewrite /= nth_nil.
  + apply: Hf; first by move/(_ 0): Hs.
    apply: IH1.
    move=> k; by move/(_ k.+1): Hs.
Qed.
End foldri_proof.

Section mkseq_proof.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Hypothesis H0 : Rel dv dt.
Lemma mkseq_correct fv ft (mv mt : nat) :
  (forall k : nat, Rel (fv k) (ft k)) ->
  (* the following 2 hyps hold if mv <> mt *)
  (forall k : nat, mv <= k < mt -> fv k = dv) ->
  (forall k : nat, mt <= k < mv -> fv k = dv) ->
  RelP (mkseq fv mv) (mkseq ft mt).
Proof.
move=> Hk Hv1 Hv2 k; rewrite !nth_mkseq_dflt.
do 2![case: ifP]=> A B.
- exact: H0.
- by rewrite -(Hv1 k) // B ltnNge A.
- by rewrite (Hv2 k) // A ltnNge B.
- exact: Hk.
Qed.
End mkseq_proof.

Section misc_proofs.
Variables (V T : Type).
Variable Rel : V -> T -> Prop.
Variables (dv : V) (dt : T).
Local Notation RelP sv st := (forall k : nat, Rel (nth dv sv k) (nth dt st k)) (only parsing).
Lemma set_nth_correct sv st bv bt n :
  RelP sv st ->
  Rel bv bt ->
  RelP (set_nth dv sv n bv) (set_nth dt st n bt).
Proof. by move=> Hs Hb k; rewrite !nth_set_nth /=; case: ifP. Qed.

Lemma drop_correct sv st n :
  RelP sv st ->
  RelP (drop n sv) (drop n st).
Proof. by move=> Hs k; rewrite !nth_drop; apply: Hs. Qed.

Hypothesis H0 : Rel dv dt.
Lemma ncons_correct sv st n :
  RelP sv st ->
  RelP (ncons n dv sv) (ncons n dt st).
Proof. by move=> Hs k; rewrite !nth_ncons; case: ifP. Qed.

End misc_proofs.
