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
Require Import Reals.
Require Import NaryFunctions.
Require Import Flocq.Core.Fcore.
Require Import Interval_interval.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_specific_ops.
Require Import Interval_float_sig.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.bigop.
(* Require Import CoqEAL_theory.hrel CoqEAL_refinements.refinements. *)
Require Import Rstruct interval_compl nary_tuple basic_rec seq_compl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "--> e"
  (at level 10, e at level 8, no associativity, format "-->  e").
Reserved Notation "i >: x"
  (at level 70, no associativity, format "i  >:  x").
Reserved Notation "i >:: x"
  (at level 70, no associativity, format "i  >::  x").

Module Type BaseOps.
Parameter U : Type.
Parameter T : Type.
Parameter Inline zero : T.
Parameter Inline one : T.
Parameter Inline opp : T -> T.
Parameter Inline add : U -> T -> T -> T.
Parameter Inline sub : U -> T -> T -> T.
Parameter Inline mul : U -> T -> T -> T.
End BaseOps.

(* REM: We may use the new notation features of Coq 8.4 w.r.t. modules. *)

Module Type PowDivOps.
Include BaseOps.
(** [mask c x] is the constant fonction [c], except if [T = I.type]
and [x] contains [Xnan], implying that [mask c x] contains [Xnan]. *)
Parameter Inline mask : T -> T -> T.
Parameter Inline from_nat : nat -> T.
Parameter Inline fromZ : Z -> T.
Parameter Inline power_int : U -> T -> Z -> T.
Parameter Inline sqr : U -> T -> T.
Parameter Inline inv : U -> T -> T.
Parameter Inline div : U -> T -> T -> T.
End PowDivOps.

Module Type FullOps.
Include PowDivOps.
Parameter Inline sqrt : U -> T -> T.
Parameter Inline invsqrt : U -> T -> T.
Parameter Inline exp : U -> T -> T.
Parameter Inline sin : U -> T -> T.
Parameter Inline cos : U -> T -> T.
Parameter Inline ln : U -> T -> T.
Parameter Inline atan : U -> T -> T.
Parameter Inline tan : U -> T -> T.
End FullOps.

Module Type ExactFullOps.
Include FullOps with Definition U := unit.
Parameter maskE : forall c x, mask c x = c.
Definition pow x n := (power_int tt x (Z_of_nat n)).
Parameter pow_0 : forall x, pow x 0 = one.
Parameter pow_S : forall x n, pow x n.+1 = mul tt x (pow x n).
Parameter pow_opp :
  forall x n, x <> zero -> power_int tt x (-n) = inv tt (power_int tt x n).
End ExactFullOps.

Module FullInt (I : IntervalOps) <: FullOps.
Definition U := I.precision.
Definition T := I.type.
Definition zero := I.zero.
Definition one := I.fromZ 1.
Definition opp := I.neg.
Definition add := I.add.
Definition sub := I.sub.
Definition mul := I.mul.
Definition div := I.div.
Definition power_int := I.power_int.
Definition exp := I.exp.
Definition ln := I.ln.
Definition from_nat := fun n => I.fromZ (Z_of_nat n).
Definition fromZ := I.fromZ.
Definition inv := I.inv.
Definition cos := I.cos.
Definition sin := I.sin.
Definition sqr := I.sqr.
Definition sqrt := I.sqrt.
Definition invsqrt := fun prec x => I.inv prec (I.sqrt prec x).
Definition mask : T -> T -> T := I.mask.
Definition tan := I.tan.
Definition atan := I.atan.
End FullInt.

Module Type PolyOps (C : PowDivOps) <: BaseOps.
Include Type BaseOps with Definition U := C.U. (* simplifying assumption *)

Parameter Inline toSeq : T -> seq C.T.
Parameter Inline mkPoly : seq C.T -> T.
Parameter Inline nth : T -> nat -> C.T.
Parameter Inline size : T -> nat.
Parameter Inline rec1 : (C.T -> nat -> C.T) -> C.T -> nat -> T.
Parameter Inline rec2 : (C.T -> C.T -> nat -> C.T) -> C.T -> C.T -> nat -> T.
Parameter Inline grec1 :
  forall A : Type,
  (A -> nat -> A) ->
  (A -> nat -> C.T) -> A -> seq C.T -> nat -> T.
(* Erik: We don't use [Parameter map : forall f : C.T -> C.T, T -> T.]
   as its specification would require [f C.tzero = C.tzero], which
   does not hold in general. Still, we can rely on fold(r) instead. *)
Parameter Inline fold : forall V : Type, (C.T -> V -> V) -> V -> T -> V.
Parameter Inline set_nth : T -> nat -> C.T -> T.
Parameter Inline mul_trunc : U -> nat -> T -> T -> T.
Parameter Inline mul_tail : U -> nat -> T -> T -> T.
(** [tlift j pol] represents [pol * X^j] if [pol] is in the monomial basis *)
Parameter Inline lift : nat -> T -> T.
Parameter Inline tail : nat -> T -> T.
(* Parameter polyX : T. (Subsumed by [tpolyNil] and [tpolyCons].) *)
Parameter Inline polyNil : T.
Parameter Inline polyCons : C.T -> T -> T.
Parameter Inline eval : U -> T -> C.T -> C.T.
Parameter Inline deriv : U -> T -> T.
Parameter Inline mul_mixed : U -> C.T -> T -> T.
Parameter Inline div_mixed_r : U -> T -> C.T -> T.
Parameter Inline dotmuldiv : U -> seq Z -> seq Z -> T -> T.
Parameter primitive : U -> C.T -> T -> T.

(* specifications of toSeq *)
Parameter toSeq_nil : toSeq zero = [::].
Parameter mkPoly_toSeq : forall p, mkPoly (toSeq p) = p.
Parameter toSeq_mkPoly : forall s, toSeq (mkPoly s) = s.
Parameter eval_seq : forall u p x, eval u p x =
  C.mask (foldr (fun a b => C.add u (C.mul u b x) a) C.zero (toSeq p)) x.
Parameter nth_toSeq : forall p n, nth p n = seq.nth (C.zero) (toSeq p) n.

Parameter poly_ind : forall (f : T -> Type),
  f polyNil ->
  (forall a p, f p -> f (polyCons a p)) ->
  forall p, f p.

Parameter primitive_correct : forall u p c k, k < (size p).+1 ->
                                              nth (primitive u c p) k =
                                              match k with
                                                | 0 => c
                                                | S m => C.div u (nth p m) (C.from_nat k) end.

Parameter size_primitive : forall u c p, size (primitive u c p) = (size p).+1.
(* FIXME: remove if possible *)

Parameter size_sub :
  forall u p1 p2,
  size (sub u p1 p2) = maxn (size p1) (size p2).
Parameter size_rec1 : forall F x n, size (rec1 F x n) = n.+1.
Parameter size_rec2 : forall F x y n, size (rec2 F x y n) = n.+1.
Parameter size_mul_trunc : forall u n p q, size (mul_trunc u n p q) = n.+1.
Parameter size_mul_tail :
  forall u n p q, size (mul_tail u n p q) = ((size p).-1 + (size q).-1 - n).
Parameter size_add :
  forall u p1 p2,
  size (add u p1 p2) = maxn (size p1) (size p2).
Parameter size_opp :
  forall p1,
  size (opp p1) = size p1.
Parameter size_polyNil : size polyNil = 0.
Parameter size_polyCons : forall a p, size (polyCons a p) = (size p).+1.
Parameter size_grec1 :
  forall (A : Type)
  (F : A -> nat -> A) (G : A -> nat -> C.T) (q : A) (s : seq C.T) (n : nat),
  size (grec1 F G q s n) = n.+1.
Parameter size_tail :
  forall p k, size (tail k p) = size p - k.

Parameter size_dotmuldiv :
  forall n u a b p, size p = n -> seq.size a = n -> seq.size b = n ->
  size (dotmuldiv u a b p) = n.
Parameter size_set_nth : forall p n val,
  size (set_nth p n val) = maxn n.+1 (size p).
(* i.e., tsize (tset_nth p n val) = maxn n.+1 (tsize p) = tsize p. *)

Parameter nth_polyCons : forall a p k,
  nth (polyCons a p) k = if k is k'.+1 then nth p k' else a.
Parameter nth_polyNil : forall n, nth polyNil n = C.zero.

Parameter fold_polyNil : forall U f iv, @fold U f iv polyNil = iv.
Parameter fold_polyCons : forall U f iv c p,
  @fold U f iv (polyCons c p) = f c (@fold U f iv p).
Parameter nth_set_nth : forall p n val k,
  nth (set_nth p n val) k = if k == n then val else nth p k.

Parameter nth_default : forall p n, size p <= n -> nth p n = C.zero.

(* FIXME: Is the following mandatory? *)
Parameter set_nth_nth : forall p n, n < size p -> set_nth p n (nth p n) = p.

(*
Parameter Inline recN :
  forall N : nat, C.T ^ N -> C.T ^^ N --> (nat -> C.T) -> nat -> T.
Parameter Inline lastN : C.T -> forall N : nat, T -> C.T ^ N.

Parameter rec1_spec0 :
  forall (F : C.T -> nat -> C.T) F0 n,
  tnth (trec1 F F0 n) 0 = F0.
Parameter rec1_spec :
  forall (F : C.T -> nat -> C.T) F0 p k, k < p ->
  tnth (trec1 F F0 p) k.+1 = F (tnth (trec1 F F0 k) k) k.+1.

Parameter rec2_spec0 :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 n,
  tnth (trec2 F F0 F1 n) 0 = F0.

Parameter rec2_spec1 :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 n,
  tnth (trec2 F F0 F1 n.+1) 1 = F1.
Parameter rec2_spec :
  forall (F : C.T -> C.T -> nat -> C.T) F0 F1 p k, k.+1 < p ->
  tnth (trec2 F F0 F1 p) k.+2 =
  F (tnth (trec2 F F0 F1 k) k) (tnth (trec2 F F0 F1 k.+1) k.+1) k.+2.

Parameter recN_spec0 :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
  (d : C.T),
  k <= n -> k < N -> tnth (trecN L0 F n) k = nth d (Ttoseq L0) k.

Parameter lastN_spec :
  forall (d := C.tzero) N (p : T) (i : 'I_N),
  Tnth (tlastN d N p) i = tnth p (tsize p - N + val i).

Parameter recN_spec :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
         (d : C.T),
  k <= n -> k >= N ->
  tnth (trecN L0 F n) k =
  (nuncurry F) (tlastN d N (trecN L0 F k.-1)) k.
Parameter size_trecN :
  forall (N : nat) (L0 : C.T ^ N) (F : C.T ^^ N --> (nat -> C.T)) (n k : nat)
         (d : C.T),
  tsize (trecN L0 F n) = n.+1.

Parameter nth_polyCons :
  forall a p k, k <= tsize p ->
  tnth (tpolyCons a p) k = if k is k'.+1 then tnth p k' else a.
Parameter nth_polyNil : forall n, tnth tpolyNil n = C.tzero.
Parameter nth_out : forall p n, tsize p <= n -> tnth p n = C.tzero.
(** Note that we explicitely choose a default value here *)
Parameter size_set_nth : forall p n val,
  tsize (tset_nth p n val) = maxn n.+1 (tsize p).
(* i.e., tsize (tset_nth p n val) = maxn n.+1 (tsize p) = tsize p. *)
Parameter nth_set_nth : forall p n val k,
  tnth (tset_nth p n val) k = if k == n then val else tnth p k.
Parameter fold_polyNil : forall U f iv, @tfold U f iv tpolyNil = iv.
Parameter fold_polyCons : forall U f iv c p,
  @tfold U f iv (tpolyCons c p) = f c (@tfold U f iv p).

Parameter nth_tail :
  forall p n k,
  tnth (ttail k p) n = tnth p (k + n).
*)

End PolyOps.

Module FullR <: ExactFullOps.
Definition U := unit.
Local Notation "--> e" := (fun _ : U => e).
Definition T := R.
Definition zero := R0.
Definition one := R1.
Definition opp := Ropp.
Definition add := --> Rplus.
Definition sub := --> Rminus.
Definition mul := --> Rmult.
Definition div := --> Rdiv.
Definition power_int := --> powerRZ.
Definition exp := --> exp.
Definition ln := --> ln.
Definition from_nat := INR.
Definition fromZ := IZR.
Definition inv := --> Rinv.
Definition cos := --> cos.
Definition sin := --> sin.
Definition sqr := --> fun x => Rmult x x.
Definition sqrt := --> sqrt.
Definition invsqrt := --> fun x => (Rinv (sqrt tt x)).
Definition mask : T -> T -> T := fun c _ => c.
Definition tan := --> tan.
Definition atan := --> atan.
Lemma maskE : forall c x, mask c x = c.
Proof. done. Qed.

Definition pow x n := (power_int tt x (Z_of_nat n)).

Lemma pow_0 : forall x, pow x 0 = one.
Proof. done. Qed.

Lemma pow_S : forall x n, pow x n.+1 = mul tt x (pow x n).
Proof. by move=> *; rewrite /pow /power_int -!Interval_missing.pow_powerRZ. Qed.

Lemma pow_opp :
  forall x n, x <> zero -> power_int tt x (-n) = inv tt (power_int tt x n).
Proof.
move=> x [||p H] //=; auto with real.
rewrite /inv ?Rinv_involutive //; exact: pow_nonzero.
Qed.

End FullR.

Module SeqPoly (C : PowDivOps) <: PolyOps C.
Definition U := C.U.
Definition T := seq C.T.

(* TODO Definition recN := @recNup C.T. *)
(* TODO Definition lastN : C.T -> forall N : nat, T -> C.T ^ N := @lastN C.T. *)

Definition zero : T := [::].
Definition one : T := [:: C.one].

Definition opp := map C.opp.

Section PrecIsPropagated.
Variable u : U.

Definition add := map2 (C.add u) id.

Definition sub := map2 (C.sub u) C.opp.

Definition nth := nth C.zero.

(** Advantage of using foldl w.r.t foldr : foldl is tail-recursive *)
Definition mul_coeff (p q : T) (np k : nat) : C.T :=
  foldl (fun x i => C.add u (C.mul u (nth p i) (nth q (k - i))) x) (C.zero)
        (rev (iota 0 np)).

Lemma mul_coeffE p q np k : mul_coeff p q np k =
  \big[C.add u/C.zero]_(0 <= i < np) C.mul u (nth p i) (nth q (k - i)).
Proof.
rewrite BigOp.bigopE /reducebig /mul_coeff foldl_rev.
by congr foldr; rewrite /index_iota subn0.
Qed.

Definition mul_trunc n p q := mkseq (mul_coeff p q (size p)) n.+1.

Definition mul_tail n p q :=
  let np := size p in
  mkseq (fun i => mul_coeff p q np (n.+1+i)) (np.-1 + (size q).-1 - n).

Definition mul p q :=
  let np := size p in
  mkseq (mul_coeff p q np) (np + size q).-1.

(* Old definitions

Definition polyC (c : C.T) : T := [:: c].

Definition polyX := [:: C.tzero; C.tone].

Fixpoint eval' (p : T) (x : C.T) :=
  match p with
    | [::] => C.tzero
    | c :: p' => C.tadd u (C.tmul u (teval' p' x) x) c
  end.
*)

Definition rec1 := @rec1up C.T.
Definition rec2 := @rec2up C.T.
Definition size := @size C.T.
Definition fold := @foldr C.T.
Definition eval p x :=
  C.mask
  (@fold C.T (fun a b => C.add u (C.mul u b x) a) C.zero p)
  x.
Definition set_nth := @set_nth C.T C.zero.
Definition map := @map C.T C.T.

Definition polyCons := @Cons C.T.

Definition polyNil := @Nil C.T.

(* TODO: Revise *)
Lemma poly_ind : forall (f : T -> Type),
  f polyNil ->
  (forall a p, f p -> f (polyCons a p)) ->
  forall p, f p.
Proof.
by move=> f h1 hrec; elim =>//= a e; apply:hrec.
Qed.

Fixpoint deriv_loop (p : T) (i : nat) :=
  match p with
    | [::] => [::]
    | a :: e =>
      C.mul u a (C.from_nat i) :: deriv_loop e i.+1
  end.
Definition deriv (p : T) := deriv_loop (behead p) 1%N.

Definition grec1 (A : Type) := @grec1up A C.T.

Lemma size_grec1 A F G (q : A) s n : size (grec1 F G q s n) = n.+1.
Proof. by apply size_grec1up. Qed.


Lemma size_add p1 p2 : size (add p1 p2) = maxn (size p1) (size p2).
Proof. by rewrite /size /add size_map2. Qed.

Lemma size_rec1 F x n: size (rec1 F x n) = n.+1.
Proof. by apply size_rec1up. Qed.

Lemma size_rec2 F x y n: size (rec2 F x y n) = n.+1.
Proof. by apply size_rec2up. Qed.


Lemma size_mul_trunc n p q: size (mul_trunc n p q) = n.+1.
Proof. by rewrite /size size_mkseq. Qed.

Lemma size_mul_tail n p q:
     size (mul_tail n p q) = ((size p).-1 + (size q).-1 - n).
Proof. by rewrite /size size_mkseq. Qed.

End PrecIsPropagated.

Definition tail := @drop C.T.

Definition lift (n : nat) p := ncons n C.zero p.

Definition mul_mixed (u : U) (a : C.T) (p : T) :=
  @foldr C.T T (fun x acc => (C.mul u a x) :: acc) [::] p.

Definition div_mixed_r (u : U) (p : T) (b : C.T) :=
  @foldr C.T T (fun x acc => (C.div u x b) :: acc) [::] p.

Fixpoint dotmuldiv (u : U) (a b : seq Z) (p : T) : T :=
match a, b, p with
| a0 :: a1, b0 :: b1, p0 :: p1 =>
  C.mul u (C.div u (C.fromZ a0) (C.fromZ b0)) p0 ::
  dotmuldiv u a1 b1 p1
| _, _, _ => [::] (* e.g. *)
end.

Lemma fold_polyNil : forall U f iv, @fold U f iv polyNil = iv.
Proof. done. Qed.

Lemma fold_polyCons : forall U f iv c p,
  @fold U f iv (polyCons c p) = f c (@fold U f iv p).
Proof. done. Qed.

Lemma size_set_nth p n val :
  size (set_nth p n val) = maxn n.+1 (size p).
Proof. by rewrite /size seq.size_set_nth. Qed.

Lemma nth_set_nth p n val k :
  nth (set_nth p n val) k = if k == n then val else nth p k.
Proof. by rewrite /nth nth_set_nth. Qed.

Lemma nth_default : forall p n, size p <= n -> nth p n = C.zero.
Proof. by move=> *; rewrite /nth nth_default. Qed.

Lemma set_nth_nth : forall p n, n < size p -> set_nth p n (nth p n) = p.
Proof.
move=> p n H.
apply: (eq_from_nth (x0 := C.zero)).
  by rewrite seq.size_set_nth; apply/maxn_idPr.
move=> i Hi.
rewrite seq.size_set_nth in Hi.
move/maxn_idPr: (H) (Hi) =>-> Hn.
rewrite seq.nth_set_nth /=.
by case E : (i == n); first by rewrite (eqP E).
Qed.

Lemma size_polyNil : size polyNil = 0.
Proof. done. Qed.

Lemma size_polyCons : forall a p, size (polyCons a p) = (size p).+1.
Proof. by []. Qed.

Lemma nth_polyNil n: nth polyNil n = C.zero.
Proof. by rewrite nth_default. Qed.

Lemma nth_polyCons : forall a p k, (* k <= size p -> *)
  nth (polyCons a p) k = if k is k'.+1 then nth p k' else a.
Proof. by move=> a p; case. Qed.

Lemma size_opp p1 :
  size (opp p1) = size p1.
Proof. by rewrite /size /opp size_map. Qed.

Lemma size_sub u p1 p2 :
  size (sub u p1 p2) = maxn (size p1) (size p2).
Proof. by rewrite /sub /size size_map2. Qed.

Lemma size_dotmuldiv (n : nat) (u : U) a b p :
  size p = n -> seq.size a = n -> seq.size b = n ->
  size (dotmuldiv u a b p) = n.
Proof.
move: a b p n; elim=> [|a0 a1 IH] [|b0 b1] [|p0 p1] =>//.
move=> /= n Hp Ha Hb /=.
rewrite (IH _ _ n.-1) //.
by rewrite -Hp.
by rewrite -Hp.
by rewrite -Ha.
by rewrite -Hb.
Qed.

Lemma size_tail p k : size (tail k p) = size p - k.
Proof. by rewrite /size /tail size_drop. Qed.

Definition toSeq (p : T) := p.
Definition mkPoly (s : seq C.T) := (s : T).

Lemma mkPoly_toSeq : forall p, mkPoly (toSeq p) = p.
Proof. by []. Qed.

Lemma toSeq_mkPoly : forall s, toSeq (mkPoly s) = s.
Proof. by []. Qed.

Lemma toSeq_nil : toSeq zero = [::].
Proof. by []. Qed.
Lemma eval_seq : forall u p x, eval u p x = C.mask (foldr (fun a b => C.add u (C.mul u b x) a) C.zero (toSeq p)) x.
Proof. done. Qed.

Lemma nth_toSeq p n : nth p n = seq.nth (C.zero) (toSeq p) n.
Proof. by []. Qed.

Section precSection.
Variable u : U.
Definition int_coeff (p : T) (c : C.T) (n : nat) :=
match n with
| 0 => c
| S m => C.div u (nth p m) (C.from_nat n)
end.

Definition int_coeff_shift (p : T) (k : nat) := C.div u
(seq.nth C.zero p k)
(C.from_nat k.+1).

Definition primitive (c : C.T) (p : T) :=
 (c::(mkseq (int_coeff_shift p) (size p))) : T.

Lemma psize_primitive (c : C.T) (p : T):
size (primitive c p) = (size p).+1.
Proof.
by rewrite /size /= size_mkseq /size.
Qed.

Lemma nth_primitive (p : T) (c : C.T) (k : nat) : (k < (size p).+1) -> nth (primitive c p) k = int_coeff p c k.
Proof.
move => Hk.
case : k Hk => [ _ | m Hm] //=.
have HSiota : m < seq.size (iota 0 (size p)) by rewrite size_iota.
rewrite /nth /toSeq /primitive /= .
by rewrite (nth_map 0) // nth_iota /=; first rewrite add0n.
Qed.

Lemma primitive_correct : forall (p : T) c k, k < (size p).+1 ->
                                              nth (primitive c p) k =
                                              match k with
                                                | 0 => c
                                                | S m => C.div u (nth p m) (C.from_nat k) end.
Proof.
move => k c p Hkp.
by apply: nth_primitive.
Qed.

Lemma size_primitive (c : C.T) (p : T):
size (primitive c p) = (size p).+1.
Proof. by rewrite /size /= size_mkseq. Qed.

End precSection.
End SeqPoly.

Module PolR <: PolyOps FullR.
Include SeqPoly FullR.

Lemma toSeq_eval0 : forall (u : U) (p : T),
                           eval u p R0 = head R0 (toSeq p).
Proof.
move => u.
elim=> [| a q HI] ; first by [].
by rewrite /= HI; case: u HI; rewrite Rmult_0_r Rplus_0_l.
Qed.

Lemma hornerE p x :
  eval tt p x =
  \big[Rplus/R0]_(0 <= i < size p) Rmult (nth p i) (FullR.pow x i).
Proof.
elim: p; first by rewrite big_mkord big_ord0 /=.
move=> t p /= ->.
rewrite big_nat_recl // FullR.pow_0 /=.
rewrite Rmult_1_r Rplus_comm.
case: (size p)=> [|n].
  by rewrite !big_mkord !big_ord0 /= Rmult_0_l.
rewrite Rmult_comm big_distrr /=; congr Rplus.
apply: eq_bigr => i _; rewrite FullR.pow_S /FullR.mul.
by rewrite ![_ x _]Rmult_comm ![Rmult x _]Rmult_comm Rmult_assoc.
Qed.

Lemma hornerE_wide n p x :
  size p <= n ->
  eval tt p x =
  \big[Rplus/R0]_(0 <= i < n) Rmult (nth p i) (FullR.pow x i).
Proof.
move=> Hn; rewrite hornerE (big_nat_leq_idx _ Hn) //.
by move=> i /andP [Hi _]; rewrite nth_default // Rmult_0_l.
Qed.

(*
Lemma nth_add p1 p2 k :
  nth (add tt p1 p2) k = Rplus (nth p1 k) (nth p2 k).
Proof.
elim: p1 p2 k =>[//|c1 p1 IHp] p2 k.
  by rewrite /= !nth_polyNil Rplus_0_l.
by case: p2 k =>[//|c2 p2] k; case: k IHp =>[//|k] IHp //=; rewrite Rplus_0_r.
Qed.

Lemma nth_opp p1 k : nth (opp p1) k = Ropp (nth p1 k).
Proof.
elim: p1 k =>[//|c1 p1 IHp] k.
  by rewrite /= !nth_polyNil Ropp_0.
by case: k IHp =>[//|k] IHp //=; rewrite Rplus_0_r.
Qed.

Lemma nth_sub p1 p2 k :
  nth (sub tt p1 p2) k = Rminus (nth p1 k) (nth p2 k).
Proof.
elim: p1 p2 k =>[//|c1 p1 IHp] p2 k.
  by rewrite /= !nth_polyNil Rminus_0_l nth_opp.
by case: p2 k =>[//|c2 p2] k; case: k IHp =>[//|k] IHp //=; rewrite Rminus_0_r.
Qed.

Lemma mul_coeffE p1 p2 k : mul_coeff tt p1 p2 k =
         \big[Rplus/0%R]_(i < k.+1) Rmult (PolR.nth p1 (k - i)) (PolR.nth p2 i).
Proof.
rewrite BigOp.bigopE /reducebig /mul_coeff.
have {1} ->: (iota 0 k.+1) = (rev (rev (iota 0 k.+1))) by rewrite revK.
rewrite foldl_rev.
apply: sym_eq; set f0 := (fun _ => _); set g0 := (fun _ => _).
rewrite (@eq_foldr _ _ _ _ g0 (fun (i: 'I_k.+1) => k -(val i))); first last.
  by move=> x y; rewrite /f0 /g0 sub_ordK.
rewrite /index_enum /= -enumT map_comp.
have->: (seq.map (nat_of_ord (n:=k.+1)) (enum 'I_k.+1)) = iota 0 k.+1.
  by rewrite -val_ord_enum enumT unlock //=.
congr foldr; rewrite /= -map_cons.
change (0 :: iota 1 k) with (iota 0 k.+1).
by rewrite rev_iota.
Qed.

*)
End PolR.

Module Type PolyIntOps (I : IntervalOps).
Module Int := FullInt I.
Include PolyOps Int.

Definition contains_pointwise pi p : Prop :=
  forall k, contains (I.convert (nth pi k)) (Xreal (PolR.nth p k)).

(* Very similar definition, suitable for specifying grec1 *)
Definition seq_contains_pointwise si s : Prop :=
  forall k, contains (I.convert (seq.nth Int.zero si k)) (Xreal (PolR.nth s k)).

Module Import Notations.
Delimit Scope ipoly_scope with IP.
Notation "i >: x" := (contains (I.convert i) (Xreal x)) : ipoly_scope.
Notation "p >:: x" := (contains_pointwise p x) : ipoly_scope.
Notation eq_size pi p := (size pi = PolR.size p).
End Notations.
Local Open Scope ipoly_scope.

Parameter eval_correct :
  forall u pi ci p x, pi >:: p -> ci >: x -> eval u pi ci >: PolR.eval tt p x.

Parameter zero_correct : zero >:: PolR.zero.
Parameter one_correct : one >:: PolR.one.
Parameter opp_correct : forall pi p, pi >:: p -> opp pi >:: PolR.opp p.
Parameter add_correct :
  forall u pi qi p q, pi >:: p -> qi >:: q -> add u pi qi >:: PolR.add tt p q.
Parameter sub_correct :
  forall u pi qi p q, pi >:: p -> qi >:: q -> sub u pi qi >:: PolR.sub tt p q.
Parameter mul_correct :
  forall u pi qi p q, pi >:: p -> qi >:: q -> mul u pi qi >:: PolR.mul tt p q.
Parameter mul_trunc_correct :
  forall u n pi qi p q, pi >:: p -> qi >:: q ->
  mul_trunc u n pi qi >:: PolR.mul_trunc tt n p q.
Parameter mul_tail_correct :
  forall u n pi qi p q, pi >:: p -> qi >:: q ->
  mul_tail u n pi qi >:: PolR.mul_tail tt n p q.
Parameter lift_correct : forall n pi p, pi >:: p -> lift n pi >:: PolR.lift n p.
Parameter tail_correct : forall n pi p, pi >:: p -> tail n pi >:: PolR.tail n p.
Parameter polyNil_correct : polyNil >:: PolR.polyNil. (* strong enough ? *)
Parameter polyCons_correct :
  forall pi xi p x, pi >:: p -> xi >: x ->
  polyCons xi pi >:: PolR.polyCons x p.

Parameter eval_propagate : forall u pi, I.propagate (eval u pi).

(* Parameter size_correct *)
Parameter rec1_correct :
  forall fi f fi0 f0 n,
    (forall ai a m, ai >: a -> fi ai m >: f a m) -> fi0 >: f0 ->
    rec1 fi fi0 n >:: PolR.rec1 f f0 n.
Parameter rec2_correct :
  forall fi f fi0 f0 fi1 f1 n,
    (forall ai bi a b m, ai >: a -> bi >: b -> fi ai bi m >: f a b m) ->
    fi0 >: f0 -> fi1 >: f1 ->
    rec2 fi fi0 fi1 n >:: PolR.rec2 f f0 f1 n.
Parameter set_nth_correct :
  forall pi p n ai a, pi >:: p -> ai >: a -> set_nth pi n ai >:: PolR.set_nth p n a.
Parameter deriv_correct :
  forall u pi p, pi >:: p -> deriv u pi >:: (PolR.deriv tt p).
(*
Parameter grec1_correct :
  forall (A := PolR.T) Fi (F : A -> nat -> A) Gi (G : A -> nat -> R) ai a si s n,
  (forall qi q m, qi >:: q -> Fi qi m >:: F q m) ->
  (forall qi q m, qi >:: q -> Gi qi m >: G q m) ->
  ai >:: a -> cpw' si s ->
  cpw (grec1 Fi Gi ai si n) (PolR.grec1 F G a s n).
*)

(* TODO recN_correct : forall N : nat, C.T ^ N -> C.T ^^ N --> (nat -> C.T) -> nat -> T. *)
(* TODO lastN_correct : C.T -> forall N : nat, T -> C.T ^ N. *)

(*
Parameter poly2_ind : forall K : T -> PolR.T -> Type,
  K polyNil PolR.polyNil ->
  (forall xi x pi p, K pi p -> K (polyCons xi pi) (PolR.polyCons x p)) ->
  forall pi p, K pi p.
*)

(*
Parameter poly2_ind :
  forall K : T -> PolR.T -> Prop,
  K polyNil PolR.polyNil ->
  (forall xi x pi p, size pi = PolR.size p -> K pi p -> K (polyCons xi pi) (PolR.polyCons x p)) ->
  forall pi p, size pi = PolR.size p -> K pi p.
*)

End PolyIntOps.

(** Note that the implementation(s) of the previous signature will
depend on the choice of a particular polynomial basis, especially for
the multiplication and polynomial evaluation. *)

(** Implementation of PolyOps with sequences and operations in monomial basis *)

Module SeqPolyInt (I : IntervalOps) <: PolyIntOps I.
Module Int := FullInt I.
Include SeqPoly Int.

Module Import Aux := IntervalAux I.

Definition contains_pointwise pi p : Prop :=
  forall k, contains (I.convert (nth pi k)) (Xreal (PolR.nth p k)).

(* Very similar definition, suitable for specifying grec1 *)
Definition seq_contains_pointwise si s : Prop :=
  forall k, contains (I.convert (seq.nth Int.zero si k)) (Xreal (PolR.nth s k)).

Module Import Notations.
Delimit Scope ipoly_scope with IP.
Notation "i >: x" := (contains (I.convert i) (Xreal x)) : ipoly_scope.
Notation "p >:: x" := (contains_pointwise p x) : ipoly_scope.
Notation eq_size pi p := (size pi = PolR.size p).
End Notations.
Local Open Scope ipoly_scope.

Lemma eval_propagate : forall u pi, I.propagate (eval u pi).
Proof. by red=> *; rewrite /eval I.mask_propagate_r. Qed.

Lemma zero_correct : zero >:: PolR.zero.
Proof. by case=> [|k]; exact: cont0. Qed.

Lemma one_correct : one >:: PolR.one.
Proof. by case=> [|k] /=; [apply: I.fromZ_correct|exact: zero_correct]. Qed.

Lemma opp_correct pi p : pi >:: p -> opp pi >:: PolR.opp p.
Proof.
move=> Hp k; rewrite /opp /PolR.opp /nth /PolR.nth.
apply(*:*) (@map_correct R I.type) =>//.
- exact: cont0.
- by move=> ? /only0 ->; rewrite Ropp_0; apply: cont0.
- by move=> *; rewrite -(Ropp_0); apply: R_neg_correct.
- move=> *; exact: R_neg_correct.
Qed.

Lemma add_correct u pi qi p q :
  pi >:: p -> qi >:: q -> add u pi qi >:: PolR.add tt p q.
Proof.
move=> Hp Hq k; rewrite /PolR.add /add /nth /PolR.nth.
apply (@map2_correct R I.type) =>//.
- exact: cont0.
- exact: only0.
- by move=> ? ? ? H1 /only0 ->; rewrite Rplus_0_r.
- by move=> ? ? ? /only0 -> H2; rewrite Rplus_0_l.
- by move=> v1 ? ? ? ?; rewrite -(Rplus_0_r v1); apply: R_add_correct.
- by move=> v2 ? ? ? ?; rewrite -(Rplus_0_l v2); apply: R_add_correct.
- by move=> *; apply: R_add_correct.
Qed.

Lemma sub_correct u pi qi p q :
  pi >:: p -> qi >:: q -> sub u pi qi >:: PolR.sub tt p q.
Proof.
move=> Hp Hq k; rewrite /PolR.sub /sub /nth /PolR.nth.
apply (@map2_correct R I.type) =>//.
- exact: cont0.
- by move=> v /only0 ->; rewrite Ropp_0; apply: cont0.
- by move=> t ?; rewrite -Ropp_0; apply: R_neg_correct.
- move=> *; exact: R_neg_correct.
- exact: only0.
- by move=> ? ? ? H1 /only0 ->; rewrite Rminus_0_r.
- by move=> ? ? ? /only0 -> H2; rewrite Rminus_0_l; apply: R_neg_correct.
- by move=> v1 ? ? ? ?; rewrite -(Rminus_0_r v1); apply: R_sub_correct.
- by move=> v2 ? ? ? ?; rewrite -(Rminus_0_l v2); apply: R_sub_correct.
- by move=> *; apply: R_sub_correct.
Qed.

Lemma bigop_resize pi p f :
  pi >:: p ->
  \big[Rplus/0%R]_(0 <= i < PolR.size p) (PolR.nth p i * f i)%R =
  \big[Rplus/0%R]_(0 <= i < size pi) (PolR.nth p i * f i)%R.
Proof.
move=> Hp.
case: (leqP (PolR.size p) (size pi)) => Hsz.
  rewrite [LHS](big_nat_leq_idx _ (m := size pi)) //.
  by move=> i /andP[_i i_]; rewrite PolR.nth_default // Rmult_0_l.
rewrite [RHS](big_nat_leq_idx _ (m := PolR.size p)) //; first exact: ltnW.
move=> i /andP[_i i_]; move/(_ i): Hp.
rewrite nth_default //; move/only0 ->.
by rewrite Rmult_0_l.
Qed.

Arguments bigop_resize [pi p f] _.

Lemma mul_coeff_resize pi qi p q :
  pi >:: p ->
  qi >:: q ->
  forall k : nat, PolR.mul_coeff tt p q (PolR.size p) k = PolR.mul_coeff tt p q (size pi) k.
Proof. by move=> Hpi Hqi k; rewrite !PolR.mul_coeffE (bigop_resize Hpi). Qed.

Lemma mul_coeff_correct u pi qi p q :
  pi >:: p -> qi >:: q ->
  forall k : nat, mul_coeff u pi qi (size pi) k >: PolR.mul_coeff tt p q (PolR.size p) k.
Proof.
move=> Hpi Hqi k.
rewrite mul_coeffE PolR.mul_coeffE (bigop_resize Hpi).
apply (@big_ind2 R I.type (fun r i => i >: r)).
- exact: cont0.
- move=> *; exact: R_add_correct.
- move=> *; exact: R_mul_correct.
Qed.

Lemma nth_default_alt pi p :
  pi >:: p ->
  forall n : nat, size pi <= n -> PolR.nth p n = 0%R.
Proof.
move=> Hpi n Hn.
case: (leqP (PolR.size p) (size pi)) => Hsz.
  rewrite PolR.nth_default //; exact: leq_trans Hsz Hn.
by move/(_ n): Hpi; rewrite nth_default //; move/only0=>->.
Qed.

Lemma mul_correct u pi qi p q :
  pi >:: p -> qi >:: q -> mul u pi qi >:: PolR.mul tt p q.
Proof.
move=> Hp Hq; rewrite /mul /PolR.mul /nth /PolR.nth.
apply: (mkseq_correct (Rel := fun r i => i >: r)) =>//.
- exact: cont0.
- exact: mul_coeff_correct.
- move=> k /andP [Hk _]; rewrite PolR.mul_coeffE.
  case Ep0 : (seq.size p) => [|n]; first by rewrite big_mkord big_ord0.
  rewrite Ep0 addSn /= in Hk.
  rewrite big_mkord big1 //; move => [i Hi _] /=.
  rewrite ltnS in Hi.
  suff Hki: (seq.size q) <= k - i by rewrite (PolR.nth_default Hki) Rmult_0_r.
  apply: leq_addLR; rewrite addnC; apply: leq_trans _ Hk.
  by rewrite leq_add2r.
- move=> k /andP [Hk _]; rewrite (mul_coeff_resize Hp Hq) PolR.mul_coeffE /size.
  case Epi0 : (seq.size pi) => [|n]; first by rewrite big_mkord big_ord0.
  rewrite Epi0 addSn /= in Hk.
  rewrite big_mkord big1 //; move => [i Hi _] /=.
  rewrite ltnS in Hi.
  suff Hki: (size qi) <= k - i by rewrite (nth_default_alt Hq Hki) Rmult_0_r.
  apply: leq_addLR; rewrite addnC; apply: leq_trans _ Hk.
  by rewrite leq_add2r.
Qed.

Definition sizes := (size_polyNil, size_polyCons,
                     PolR.size_polyNil, PolR.size_polyCons).

(*
Lemma poly2_ind :
  forall K : T -> PolR.T -> Prop,
  (* (forall pi p, K pi p -> size pi = PolR.size p) -> *)
  K polyNil PolR.polyNil ->
  (forall xi x pi p, size pi = PolR.size p -> K pi p -> K (polyCons xi pi) (PolR.polyCons x p)) ->
  forall pi p, size pi = PolR.size p -> K pi p.
Proof.
move=> K H0 H1 pi p.
(* suff: (K pi p /\ (*forall pi p,*) (size pi  PolR.size p -> K pi p)) by case. *)
elim/poly_ind: pi p => [ |ai pi IHpi] p; elim/PolR.poly_ind: p =>[ |a p _] //.
rewrite !sizes.
by intuition.
Qed.
*)

Conjecture eval_correct :
  forall u pi ci p x, pi >:: p -> ci >: x -> eval u pi ci >: PolR.eval tt p x.

Conjecture lift_correct : forall n pi p, pi >:: p -> lift n pi >:: PolR.lift n p.
Conjecture tail_correct : forall n pi p, pi >:: p -> tail n pi >:: PolR.tail n p.
Conjecture polyNil_correct : polyNil >:: PolR.polyNil. (* strong enough ? *)
Conjecture polyCons_correct :
  forall pi xi p x, pi >:: p -> xi >: x ->
  polyCons xi pi >:: PolR.polyCons x p.

(* Conjecture size_correct *)
Conjecture rec1_correct :
  forall fi f fi0 f0 n,
    (forall ai a m, ai >: a -> fi ai m >: f a m) -> fi0 >: f0 ->
    rec1 fi fi0 n >:: PolR.rec1 f f0 n.
Conjecture rec2_correct :
  forall fi f fi0 f0 fi1 f1 n,
    (forall ai bi a b m, ai >: a -> bi >: b -> fi ai bi m >: f a b m) ->
    fi0 >: f0 -> fi1 >: f1 ->
    rec2 fi fi0 fi1 n >:: PolR.rec2 f f0 f1 n.
Conjecture set_nth_correct :
  forall pi p n ai a, pi >:: p -> ai >: a -> set_nth pi n ai >:: PolR.set_nth p n a.
Conjecture deriv_correct :
  forall u pi p, pi >:: p -> deriv u pi >:: (PolR.deriv tt p).
Conjecture grec1_correct :
  forall (A := PolR.T) Fi (F : A -> nat -> A) Gi (G : A -> nat -> R) ai a si s n,
  (forall qi q m, qi >:: q -> Fi qi m >:: F q m) ->
  (forall qi q m, qi >:: q -> Gi qi m >: G q m) ->
  ai >:: a -> seq_contains_pointwise si s ->
  grec1 Fi Gi ai si n >:: PolR.grec1 F G a s n.

(* TODO recN_correct : forall N : nat, C.T ^ N -> C.T ^^ N --> (nat -> C.T) -> nat -> T. *)
(* TODO lastN_correct : C.T -> forall N : nat, T -> C.T ^ N. *)

Lemma mul_trunc_correct :
  forall u n pi qi p q, pi >:: p -> qi >:: q ->
  mul_trunc u n pi qi >:: PolR.mul_trunc tt n p q.
Proof.
move=> u n pi qi p q  Hf Hg.
admit. (* new archi *)
(*
move=> k; rewrite /mul_trunc /PolR.mul_trunc  /nth /PolR.nth !nth_mkseq //.
rewrite (* mul_coeffE *) PolR.mul_coeffE.
apply big_ind2 with (id1 := Int.tzero) (R2 := R).
- by rewrite I.zero_correct; split; auto with real.
- by move=> x1 x2 y1 y2 Hx Hy; apply: R_add_correct.
move=> i _; apply: R_mul_correct;[apply: Hf| apply: Hg];case: i=> [i Hi] /=.
  by apply:(@leq_ltn_trans k); rewrite ?leq_subr //; apply: (@leq_ltn_trans n).
move: Hi Hkn; rewrite !ltnS=> Hi Hkn.
by apply:(leq_ltn_trans Hi); apply:(leq_ltn_trans Hkn).
*)
Qed.

Lemma mul_tail_correct :
  forall u n pi qi p q, pi >:: p -> qi >:: q ->
  mul_tail u n pi qi >:: PolR.mul_tail tt n p q.
Proof.
move=> u n pi qi p q Hf Hg.
move=> k.
rewrite /mul_tail /PolR.mul_tail /nth /PolR.nth /= !nth_mkseq //; last first.
  admit. admit.
  (* by rewrite Hsizef Hsizeg /PolR.size in Hkn. *)
admit.
(*
rewrite mul_coeffE' PolR.mul_coeffE' /=.
apply big_ind2 with (id1 := Int.tzero) (R2 := R) => //.
- by rewrite I.zero_correct; split; auto with real.
- by move=> x1 x2 y1 y2 Hx Hy; apply: R_add_correct.
move=> [i Hi] _.
case (boolP (n < (tsize fi).-1 + (tsize gi).-1)) => Hn; last first.
  rewrite -leqNgt -subn_eq0 in Hn.
  by rewrite (eqP Hn) in Hkn.
case: (boolP (i < tsize gi))=> Hig /=.
  case :(boolP (n.+1 + k - i < tsize fi)) => Hif.
    by apply: R_mul_correct; [apply: Hf| apply: Hg].
  rewrite -ltnNge ltnS in Hif.
  rewrite nth_default; last by rewrite /tsize in Hif.
  set gii := (nth Int.tzero gi i).
  rewrite nth_default; last by move: Hif; rewrite Hsizef /PolR.tsize.
  apply: R_mul_correct; first by rewrite I.zero_correct; split; auto with real.
  rewrite /gii; apply:Hg => //.
rewrite -ltnNge ltnS in Hig.
case :(boolP (n.+1 + k - i < tsize fi)) => Hif.
  set s := (nth Int.tzero fi _).
  rewrite nth_default; last by rewrite /tsize in Hig.
  set t:= nth (R0) fx _.
  rewrite nth_default; last by move: Hig; rewrite Hsizeg.
  apply: R_mul_correct; last by rewrite I.zero_correct; split; auto with real.
  by apply: Hf.
rewrite -ltnNge ltnS in Hif.
move: (Hig) (Hif); rewrite Hsizef Hsizeg.
move : Hig Hif; rewrite /tsize /PolR.tsize=>*; rewrite !nth_default =>//.
by apply: R_mul_correct; rewrite I.zero_correct; split; auto with real.
*)
Qed.

End SeqPolyInt.
