(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (c) 2010-2013, ENS de Lyon and Inria.

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
Require Import Interval_definitions.
Require Import Interval_specific_ops.
Require Import Interval_float_sig.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Interval_interval.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop ssralg.
Require Import seq_compl.
Require Import nary_tuple.
Require Import poly_datatypes.
Require Import basic_rec.
Require Import coeff_inst.
Require Import rpa_inst.

(** Implementation of PolyOps with sequences and operations in monomial basis *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Lemma eq_foldr (T0 T1 T2 : Type)
  (f0 : T1 -> T0 -> T0)
  (g : T2 -> T0 -> T0) (ftog : T1 -> T2) :
  (forall x y, f0 x y = g (ftog x) y) ->
  forall s x0, foldr f0 x0 s = foldr g x0 (map ftog s).
Proof. by move=> Hfg; elim=> [//| a l IHl] x0 /=; rewrite IHl Hfg. Qed.

Lemma rev_iota k: map (subn k) (iota 0 k.+1)= rev (iota 0 k.+1).
Proof.
have sameS : size (map (subn k) (iota 0 k.+1)) = size (rev (iota 0 k.+1))
  by rewrite size_map size_rev.
apply: (@eq_from_nth _ 0) => // i.
rewrite size_map size_iota => iLs.
rewrite (nth_map 0) ?(nth_rev 0) ?(nth_iota 0) ?size_iota //.
by rewrite subSS ltnS leq_subr.
Qed.

Module SeqPolyMonomUp (Import C : MaskBaseOps) <: PolyOps C <: MonomPolyOps C.

Definition U := C.U.
(* Definition fromU := @id U. *)

Definition T := seq C.T.
Definition tzero := [::] : T.
Definition tone := [:: C.tone].
Fixpoint topp (p : T) :=
  match p with
    | [::] => [::]
    | a :: p1 => C.topp a :: topp p1
  end.

Lemma size_topp : forall p, size (topp p) = size p.
Proof. by elim; rewrite //=; move=> _ l ->. Qed.

Section PrecIsPropagated.
Variable u : U.

Fixpoint tadd (p1 p2 : T) :=
  match p1 with
    | [::] => p2
    | a1 :: p3 => match p2 with
                    | [::] => p1
                    | a2 :: p4 => C.tadd u a1 a2 :: tadd p3 p4
                  end
  end.

Fixpoint tsub (p1 p2 : T) :=
  match p1 with
    | [::] => topp p2
    | a1 :: p3 => match p2 with
                    | [::] => p1
                    | a2 :: p4 => C.tsub u a1 a2 :: tsub p3 p4
                  end
  end.

Lemma size_tsub :
 forall p1 p2, size (tsub p1 p2) = maxn (size p1) (size p2).
Proof.
elim; first by move=> p2; rewrite size_topp max0n.
move=> a l IH1;elim; first by rewrite maxn0.
move=> b m IH2; rewrite /= IH1 -add1n -(add1n (size l)) -(add1n (size m)).
by apply addn_maxr.
Qed.

Definition mul_coeff (p q : T) (n : nat) : C.T :=
  foldl (fun x i => C.tadd u
    (C.tmul u (nth C.tzero p i) (nth C.tzero q (n - i))) x)
  (C.tzero) (iota 0 n.+1).

Lemma mul_coeffE' p1 p2 k : mul_coeff p1 p2 k =
         \big[C.tadd u/C.tzero]_(i < k.+1) C.tmul u (nth C.tzero p1 (k - i))
                                                (nth C.tzero p2 i).
Proof.
rewrite BigOp.bigopE /reducebig /mul_coeff.
have {1} ->: (iota 0 k.+1) = (rev (rev (iota 0 k.+1))) by rewrite revK.
rewrite foldl_rev.
apply: sym_eq; set f0 := (fun _ => _); set g0 := (fun _ => _).
rewrite (@eq_foldr _ _ _ _ g0 (fun (i: 'I_k.+1) => k -(val i))); first last.
  by move=> x y; rewrite /f0 /g0 sub_ordK.
rewrite /index_enum /= -enumT map_comp.
have->: (map (nat_of_ord (n:=k.+1)) (enum 'I_k.+1)) = iota 0 k.+1.
  by rewrite -val_ord_enum enumT unlock //=.
congr foldr; rewrite /= -map_cons.
change (0 :: iota 1 k) with (iota 0 k.+1).
by rewrite rev_iota.
Qed.

Definition tmul_trunc n p q := mkseq (mul_coeff p q) n.+1.

Definition tmul_tail n p q :=
  mkseq (fun i => mul_coeff p q (n.+1+i)) ((size p).-1 + (size q).-1 - n).

Definition tmul p q := mkseq (mul_coeff p q) (size p + size q).-1.

(* Old definitions

Definition tpolyC (c : C.T) : T := [:: c].

Definition tpolyX := [:: C.tzero; C.tone].

Fixpoint teval' (p : T) (x : C.T) :=
  match p with
    | [::] => C.tzero
    | c :: p' => C.tadd u (C.tmul u (teval' p' x) x) c
  end.
*)

Definition tnth := nth C.tzero.
Definition trec1 := @rec1up C.T.
Definition trec2 := @rec2up C.T.
Definition trecN := @recNup C.T.
Definition tsize := @size C.T.

Definition tfold := @foldr C.T.
Definition teval p x :=
  @tfold C.T (fun a b => C.tadd u (C.tmul u b x) a) (C.tcst C.tzero x) p.
Definition tset_nth := @set_nth C.T C.tzero.
Definition tmap := @map C.T C.T.
Lemma tsize_map :
  forall (f : C.T -> C.T) (p : T),
  tsize (tmap f p) = tsize p.
Proof. by move=> *; rewrite /tsize /tmap size_map. Qed.

Lemma tnth_map :
  forall (f : C.T -> C.T) (i : nat) (p : T),
  i < tsize p -> tnth (tmap f p) i = f (tnth p i).
Proof. by move=> f i p Hip; apply: nth_map. Qed.

Lemma tsize_tadd :
 forall p1 p2, tsize (tadd p1 p2) = maxn (tsize p1) (tsize p2).
Proof.
elim; first by move=>l;rewrite /= max0n.
move=> a l IH1;elim; first by rewrite maxn0.
move=> b m IH2.
rewrite /= IH1 -add1n -(add1n (size l)) -(add1n (size m)).
by apply:addn_maxr.
Qed.

Lemma tnth_tadd p1 p2 k :
  k < minn (tsize p1) (tsize p2) ->
  tnth (tadd p1 p2) k = C.tadd u (tnth p1 k) (tnth p2 k).
Proof.
elim: p1 p2 k =>[//|c1 p1 IHp] p2 k; first by rewrite /= min0n.
case: p2 k =>[//|c2 p2] k.
case: k IHp =>[//|k] IHp Hk.
apply: IHp.
by rewrite /= minnSS ltnS in Hk.
Qed.

Notation Local "a + b" := (C.tadd a b).
Notation Local "a * b" := (C.tmul a b).

Lemma tsize_trec1 F x n: tsize (trec1 F x n) = n.+1.
Proof. by apply size_rec1up. Qed.

Lemma tsize_trec2 F x y n: tsize (trec2 F x y n) = n.+1.
Proof. by apply size_rec2up. Qed.

Lemma trec1_spec0 :
  forall (F : C.T -> nat -> C.T) F0 k,
    tnth (trec1 F F0 k) 0 = F0.
Proof. by move=> F F0 k; exact: rec1up_co0. Qed.

Lemma trec1_spec :
  forall (F : C.T -> nat -> C.T) F0 p k, k < p ->
    tnth (trec1 F F0 p) k.+1 = F (tnth (trec1 F F0 k) k) k.+1.
Proof.
move=> F F0 p k Hkp.
rewrite /tnth (rec1up_nth_indep _ _ _ C.tzero Hkp (leqnn k.+1)).
exact: rec1up_correct.
Qed.

(** For trec2 *)

Lemma trec2_spec0 :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 k,
    tnth (trec2 F F0 F1 k) 0 = F0.
Proof. by move=> F F0 F1 k; exact: rec2up_co0. Qed.

Lemma trec2_spec1 :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 k,
    tnth (trec2 F F0 F1 k.+1) 1 = F1.
Proof. move=> F F0 F1 k; exact: rec2up_co1. Qed.

Lemma trec2_spec :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 p k, k.+1 < p ->
  tnth (trec2 F F0 F1 p) k.+2 =
  F (tnth (trec2 F F0 F1 k) k) (tnth (trec2 F F0 F1 k.+1) k.+1) k.+2.
Proof.
move=> F F0 F1 p k Hkp.
move : (nth_rec2up_indep F F0 F1 C.tzero C.tzero Hkp (leqnn k.+2)).
by rewrite rec2up_correct'.
Qed.

(** For trecN *)

Lemma trecN_spec0 :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
  (d : C.T),
  k <= n -> k < N -> tnth (trecN L0 F n) k = nth d (Ttoseq L0) k.
Proof.
move=> N L0 F n k d Hp Hlt; rewrite /tnth /trecN.
rewrite (@nth_recNup_indep _ _ _ _ C.tzero d n k k) //.
by rewrite /trecN recNup_init_correct /tnth // nth_take.
Qed.

Definition tlastN : C.T -> forall N : nat, T -> C.T ^ N := @lastN C.T.
Lemma tlastN_spec :
  forall (d := C.tzero) N (p : T) (i : 'I_N),
  Tnth (tlastN d N p) i = tnth p (tsize p - N + val i).
Proof. by move=> d N p i; rewrite /tlastN Tnth_lastN. Qed.

Lemma trecN_spec :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
         (d : C.T),
  k <= n -> k >= N ->
  tnth (trecN L0 F n) k =
  (nuncurry F) (tlastN d N (trecN L0 F k.-1)) k.
Proof.
move=> N L0 F n k d Hk Hge; rewrite /tnth /trecN.
rewrite (@nth_recNup_indep _ _ _ _ C.tzero d n k k) //.
have{2}->: k = (size (recNup N L0 F k)).-1 by rewrite size_recNup.
by rewrite (nth_last d) recNup_correct.
Qed.

Lemma tsize_trecN :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
         (d : C.T),
  tsize (trecN L0 F n) = n.+1.
Proof. by move=> *; rewrite [tsize _]size_recNup. Qed.

Definition tpolyCons := @Cons C.T.

Lemma tsize_polyCons : forall a p, tsize (tpolyCons a p) = (tsize p).+1.
Proof. by []. Qed.

Lemma tnth_polyCons : forall a p k, k <= tsize p ->
  tnth (tpolyCons a p) k = if k is k'.+1 then tnth p k' else a.
Proof. by move=> a p; case. Qed.

Definition tpolyNil := @Nil C.T.

Lemma tpoly_ind : forall (f : T -> Type),
  f tpolyNil ->
  (forall a p, f p -> f (tpolyCons a p)) ->
  forall p, f p.
Proof.
by move=> f h1 hrec; elim =>//= a e; apply:hrec.
Qed.

Lemma tnth_polyNil n: tnth tpolyNil n = C.tzero.
Proof. by rewrite /tnth nth_default. Qed.

Lemma tsize_polyNil : tsize tpolyNil = 0.
Proof. done. Qed.

Lemma tsize_mul_trunc n p q: tsize (tmul_trunc n p q) = n.+1.
Proof. by rewrite /tsize size_mkseq. Qed.

Lemma tsize_mul_tail n p q:
     tsize (tmul_tail n p q) = ((tsize p).-1 + (tsize q).-1 - n).
Proof. by rewrite /tsize size_mkseq. Qed.

Lemma tfold_polyNil : forall U f iv, @tfold U f iv tpolyNil = iv.
Proof. done. Qed.

Lemma tfold_polyCons : forall U f iv c p,
  @tfold U f iv (tpolyCons c p) = f c (@tfold U f iv p).
Proof. done. Qed.

Lemma tsize_set_nth p n val :
  tsize (tset_nth p n val) = maxn n.+1 (tsize p).
Proof. by rewrite /tsize size_set_nth. Qed.

Lemma tnth_set_nth p n val k :
  tnth (tset_nth p n val) k = if k == n then val else tnth p k.
Proof. by rewrite /tnth nth_set_nth. Qed.

Lemma teval_polyNil : forall x, teval tpolyNil x = C.tcst C.tzero x.
Proof. done. Qed.

Lemma teval_polyCons : (* Erik: this spec is probably too low-level *)
  forall c p x, teval (tpolyCons c p) x = C.tadd u (C.tmul u (teval p x) x) c.
Proof. done. Qed.

Lemma tnth_out p n: tsize p <= n -> tnth p n = C.tzero.
Proof. by move=> H; rewrite /tnth nth_default. Qed.

End PrecIsPropagated.

Lemma tsize_opp p1 :
  tsize (topp p1) = tsize p1.
Proof. by elim: p1 =>[//|c1 p1]; move=>/=->. Qed.

Lemma tnth_opp p1 k :
  k < tsize p1 ->
  tnth (topp p1) k = C.topp (tnth p1 k).
Proof.
elim: p1 k =>[//|c1 p1 IHp] [|k] // Hk.
rewrite /= ltnS in Hk.
by rewrite /= IHp.
Qed.

Lemma tsize_sub u p1 p2 :
  tsize (tsub u p1 p2) = maxn (tsize p1) (tsize p2).
Proof.
elim: p1 p2 =>[/=|c1 p1 IHp] p2; first by rewrite tsize_opp max0n.
case: p2 IHp =>[//|c2 p2] IHp.
by rewrite /= IHp maxnSS.
Qed.

Lemma tnth_sub u p1 p2 k :
  k < minn (tsize p1) (tsize p2) ->
  tnth (tsub u p1 p2) k = C.tsub u (tnth p1 k) (tnth p2 k).
Proof.
elim: p1 p2 k =>[//|c1 p1 IHp] p2 k; first by rewrite /= min0n.
case: p2 k =>[//|c2 p2] k.
case: k IHp =>[//|k] IHp Hk.
apply: IHp.
by rewrite /= minnSS ltnS in Hk.
Qed.

End SeqPolyMonomUp.

Module SeqPolyPowDivMonomUp (Import C : PowDivOps) <: PowDivMonomPolyOps C.

Include SeqPolyMonomUp C.

Fixpoint tdotmuldiv (u : U) (a b : seq Z) (p : T) : T :=
match a, b, p with
| a0 :: a1, b0 :: b1, p0 :: p1 =>
  C.tmul u (C.tdiv u (C.tfromZ a0) (C.tfromZ b0)) p0 ::
  tdotmuldiv u a1 b1 p1
| _, _, _ => [::] (* e.g. *)
end.

Lemma tsize_dotmuldiv (n : nat) (u : U) a b p :
  tsize p = n -> size a = n -> size b = n ->
  tsize (tdotmuldiv u a b p) = n.
Proof.
move: a b p n; elim=> [|a0 a1 IH] [|b0 b1] [|p0 p1] =>//.
move=> /= n Hp Ha Hb /=.
rewrite (IH _ _ n.-1) //.
by rewrite -Hp.
by rewrite -Hp.
by rewrite -Ha.
by rewrite -Hb.
Qed.

Lemma tnth_dotmuldiv :
  (* Erik: We might replace this spec with a parameter in rpa_inst.LinkIntX *)
  forall u a b p n, n < tsize (tdotmuldiv u a b p) ->
  tnth (tdotmuldiv u a b p) n =
  C.tmul u (C.tdiv u (C.tfromZ (nth 1%Z a n))
                     (C.tfromZ (nth 1%Z b n)))
         (tnth p n).
Proof.
move=> u; elim=> [|a0 a1 IH] [|b0 b1] [|p0 p1] =>//.
move=> /= [|n] Hn //=.
rewrite ltnS in Hn.
by rewrite IH.
Qed.

End SeqPolyPowDivMonomUp.

Module ExactSeqPolyMonomUp (C : ExactFullOps) <: ExactMonomPolyOps C.
Include SeqPolyPowDivMonomUp C.

Canonical Cadd_monoid := Monoid.Law C.tadd_assoc C.tadd_zerol C.tadd_zeror.
Canonical Cadd_comm := Monoid.ComLaw C.tadd_comm.
Canonical Cmul_monoid := Monoid.Law C.tmul_assoc C.tmul_onel C.tmul_oner.
Canonical Cmul_comm := Monoid.ComLaw C.tmul_comm.
Canonical Cadd_addlaw := Monoid.AddLaw C.tmul_distrl C.tmul_distrr.

(* Note that [Monoid.MulLaw] cannot be defined *)

Lemma mask_big_helper :
  forall x n F, \big[C.tadd tt/C.tcst C.tzero x]_(i < n) F i =
  C.tcst (\big[C.tadd tt/C.tzero]_(i < n) F i) x.
Proof.
move=> x; elim=> [|n IHn] F; first by rewrite !big_ord0.
by rewrite !big_ord_recl IHn C.mask_add_r.
Qed.

Ltac magic_mask :=
 rewrite -!(C.mask_mul_l,C.mask_mul_r,C.mask_add_l,C.mask_add_r) !C.mask_idemp.

Local Notation Ctpow prec x n := (C.tpower_int prec x (Z_of_nat n)).

Lemma is_horner p x:
  teval tt p x =
  \big[C.tadd tt/C.tcst C.tzero x]_(i < tsize p)
  C.tmul tt (tnth p i) (Ctpow tt x i).
Proof.
transitivity (C.tcst (\big[C.tadd tt/C.tzero]_(i < tsize p)
  C.tmul tt (tnth p i) (Ctpow tt x i)) x); last by rewrite mask_big_helper.
elim: p; first by rewrite big_ord0.
move=> t p /= ->.
rewrite big_ord_recl -C.mask_mul_l -C.mask_add_l C.tpow_0.
magic_mask.
rewrite C.tmul_oner C.tadd_comm.
case: (tsize p)=> [|n].
  by rewrite !big_ord0 C.mask0mul_l; magic_mask.
rewrite C.tmul_comm C.big_distrr_spec //;congr C.tcst; congr C.tadd.
apply: eq_bigr => i _; rewrite C.tpow_S.
by rewrite ![_ x _]C.tmul_comm ![C.tmul tt x _]C.tmul_comm C.tmul_assoc.
Qed.

Lemma trunc_inc m p1 p2 : tmul_trunc tt m.+1 p1 p2 =
   tmul_trunc tt m p1 p2 ++ [:: tnth (tmul_trunc tt m.+1 p1 p2) m.+1].
Proof.
rewrite /tmul_trunc; set f := (mul_coeff tt p1 p2);rewrite /mkseq.
have {1}-> :(iota 0 m.+2) =((iota 0 m.+1) ++ [:: m.+1])
  by rewrite -addn1 iota_add.
rewrite {1}map_cat /= -map_cons.
change (1 :: iota 2 m) with (iota 1 m.+1).
by rewrite /tnth (nth_map 0) ?size_iota // nth_iota.
Qed.

Lemma trunc_leq p1 p2 n m : n <= m -> forall k, k < n.+1 ->
  tnth (tmul_trunc tt n p1 p2) k = tnth (tmul_trunc tt m p1 p2) k.
Proof.
elim : m n => m.
  by rewrite leqn0 =>/eqP -> => k; rewrite ltnS leqn0=>/eqP ->.
move=> Hm n;rewrite leq_eqVlt;case/orP; first by move/eqP => ->.
move=> Hnm k Hk.
rewrite trunc_inc /tnth nth_cat.
suff ->: k < size (tmul_trunc tt m p1 p2); first by apply:Hm.
move: (tsize_mul_trunc tt m p1 p2); rewrite /tsize => ->.
by apply:(@leq_ltn_trans n) => //.
Qed.

(* the dual version of mul_coeffE' *)
Lemma mul_coeffE p1 p2 k : mul_coeff tt p1 p2 k =
  \big[C.tadd tt /C.tzero]_(i < k.+1) C.tmul tt (nth C.tzero p1 i)
                                                (nth C.tzero p2 (k - i)).
Proof.
rewrite mul_coeffE'.
have h: forall (i: 'I_k.+1), k -i < k.+1 by move=>i;rewrite ltnS leq_subr.
rewrite (reindex (fun (i: 'I_k.+1) => Ordinal (h i))).
  by apply:eq_bigr=> i _; rewrite subKn // -ltnS.
apply:onW_bij; apply: injF_bij=> [] [n Hn] [m Hm].
move/val_eqP => /= Hnm; apply/val_eqP => /=;move:Hnm.
rewrite -(eqn_add2r (n + m)) addnA subnK // (addnC n m).
by rewrite addnA subnK // eqn_add2l eq_sym.
Qed.

Lemma tmul_trunc_nth p1 p2 n k :
  k < n.+1 ->
  tnth (tmul_trunc tt n p1 p2) k =
  \big[C.tadd tt/C.tzero]_(i < k.+1) C.tmul tt (tnth p1 i) (tnth p2 (k - i)).
Proof.
by move=> Hk; rewrite /tmul_trunc /tnth nth_mkseq // mul_coeffE.
Qed.

Lemma tmul_tail_nth p1 p2 n k :
  k < ((tsize p1).-1 + (tsize p2).-1 - n) ->
  tnth (tmul_tail tt n p1 p2) k =
  (* \big[C.tadd/C.tzero]_(i < n - k)
     C.tmul (tnth p1 (i + k)) (tnth p2 (n - i)) *)
  \big[C.tadd tt/C.tzero]_(i < (k+n.+1).+1)
  C.tmul tt (tnth p1 i) (tnth p2 ((k + n.+1) - i)).
Proof.
by move=> Hk; rewrite /tmul_trunc /tnth nth_mkseq // mul_coeffE addnC.
Qed.

End ExactSeqPolyMonomUp.

(* Formalization choice: the following two modules inline a functor application
rather than taking it as an additional module parameter. *)
Module SeqPolyMonomUpInt (I : IntervalOps).
Module Int := FullInt I.
Include SeqPolyPowDivMonomUp Int.
End SeqPolyMonomUpInt.

Module SeqPolyMonomUpFloat (F : FloatOps with Definition even_radix := true).
Module Fl := MaskBaseF F.
Include SeqPolyMonomUp Fl.
End SeqPolyMonomUpFloat.

Module Type LinkIntXPr (I : IntervalOps).
Module Pol := SeqPolyMonomUpInt I.
Module PolX := ExactSeqPolyMonomUp FullXR.
Include LinkIntX I Pol PolX.
End LinkIntXPr.

Module LinkSeqPolyMonomUp (I : IntervalOps) <: LinkIntXPr I.
Module Import Pol := SeqPolyMonomUpInt I.
Module PolX := ExactSeqPolyMonomUp FullXR.

Local Coercion I.convert : I.type >-> interval. (* for readability *)
Definition contains_pointwise_until fi fx n : Prop :=
  forall k, k < n ->
  contains (I.convert (Pol.tnth fi k)) (PolX.tnth fx k).
Definition contains_pointwise fi fx : Prop :=
  Pol.tsize fi = PolX.tsize fx /\
  contains_pointwise_until fi fx (Pol.tsize fi).

Lemma link_tmul_trunc u fi gi fx gx:
  contains_pointwise fi fx ->
  contains_pointwise gi gx ->
  forall n, n < tsize fi -> n < tsize gi ->
  contains_pointwise_until
  (tmul_trunc u n fi gi) (PolX.tmul_trunc tt n fx gx) n.+1.
Proof.
move=> [Hsizef Hf] [Hsizeg Hg] n Hnf Hng k Hkn.
rewrite /tmul_trunc /PolX.tmul_trunc /tnth /PolX.tnth !nth_mkseq //.
rewrite mul_coeffE' PolX.mul_coeffE'.
apply big_ind2 with (id1 := Int.tzero) (R2 := Interval_xreal.ExtendedR).
- by apply: Int.zero_correct.
- by move=> x1 x2 y1 y2 Hx Hy; apply: I.add_correct.
move=> i _; apply:I.mul_correct;[apply: Hf| apply: Hg];case: i=> [i Hi] /=.
  by apply:(@leq_ltn_trans k); rewrite ?leq_subr //; apply: (@leq_ltn_trans n).
move: Hi Hkn; rewrite !ltnS=> Hi Hkn.
by apply:(leq_ltn_trans Hi); apply:(leq_ltn_trans Hkn).
Qed.

Lemma link_tmul_tail u fi gi fx gx:
  contains_pointwise fi fx ->
  contains_pointwise gi gx ->
  forall n,
  contains_pointwise_until (tmul_tail u n fi gi) (PolX.tmul_tail tt n fx gx)
  ((tsize fi).-1 + (tsize gi).-1 - n).
Proof.
move=> [Hsizef Hf] [Hsizeg Hg] n k Hkn.
rewrite /tmul_tail /PolX.tmul_tail /tnth /PolX.tnth /= !nth_mkseq //; last first.
  by rewrite Hsizef Hsizeg /PolX.tsize in Hkn.
rewrite mul_coeffE' PolX.mul_coeffE' /=.
apply big_ind2 with (id1 := Int.tzero) (R2 := Interval_xreal.ExtendedR) => //.
- exact: Int.zero_correct.
- by move=> x1 x2 y1 y2 Hx Hy; apply:I.add_correct.
move=> [i Hi] _.
case (boolP (n < (tsize fi).-1 + (tsize gi).-1)) => Hn; last first.
  rewrite -leqNgt -subn_eq0 in Hn.
  by rewrite (eqP Hn) in Hkn.
case: (boolP (i < tsize gi))=> Hig /=.
  case :(boolP (n.+1 + k - i < tsize fi)) => Hif.
    by apply:I.mul_correct;[apply: Hf| apply: Hg].
  rewrite -ltnNge ltnS in Hif.
  rewrite nth_default; last by rewrite /tsize in Hif.
  set gii := (nth Int.tzero gi i).
  rewrite nth_default; last by move: Hif; rewrite Hsizef /PolX.tsize.
  apply: I.mul_correct; first by apply: Int.zero_correct.
  rewrite /gii; apply:Hg => //.
rewrite -ltnNge ltnS in Hig.
case :(boolP (n.+1 + k - i < tsize fi)) => Hif.
  set s := (nth Int.tzero fi _).
  rewrite nth_default; last by rewrite /tsize in Hig.
  set t:= nth FullXR.tzero fx _.
  rewrite nth_default; last by move: Hig; rewrite Hsizeg.
  apply: I.mul_correct; last by apply: Int.zero_correct.
  by apply:Hf.
rewrite -ltnNge ltnS in Hif.
move: (Hig) (Hif); rewrite Hsizef Hsizeg.
move : Hig Hif; rewrite /tsize /PolX.tsize=>*; rewrite !nth_default =>//.
by apply: I.mul_correct; apply: Int.zero_correct.
Qed.

Lemma link_tsize_set_nth_nil n a b:
  PolX.tsize (PolX.tset_nth PolX.tpolyNil n a) =
  tsize (tset_nth tpolyNil n b).
Proof.
by rewrite [PolX.tsize _]size_set_nth [tsize _]size_set_nth.
Qed.

Lemma link_tnth_set_nth_nil a b :
  contains (I.convert a) b ->
  forall k, k < tsize (tset_nth tpolyNil 0 a) ->
  contains (I.convert (tnth (tset_nth tpolyNil 0 a) k))
  (PolX.tnth (PolX.tset_nth PolX.tpolyNil 0 b) k).
Proof.
move=> Hab k Hk.
rewrite /tsize /tset_nth /= /leq subn1 /= in Hk.
by move/eqP: Hk => ->.
Qed.

End LinkSeqPolyMonomUp.
