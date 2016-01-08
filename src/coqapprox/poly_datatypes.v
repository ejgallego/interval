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
Require Import Coquelicot.
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

Local Open Scope nat_scope.

Reserved Notation "--> e"
  (at level 10, e at level 8, no associativity, format "-->  e").
Reserved Notation "i >: x"
  (at level 70, no associativity, format "i  >:  x").
Reserved Notation "i >:: x"
  (at level 70, no associativity, format "i  >::  x").

Reserved Notation "p .[ x ]"
  (at level 2, left associativity, format "p .[ x ]").
Reserved Notation "a ^` ()" (at level 8, format "a ^` ()").

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
(* Include BaseOps with Definition U := C.U. *)
Definition U := C.U.
Parameter T : Type.
Parameter zero : T.
Parameter one : T.
Parameter opp : T -> T.
Parameter add : U -> T -> T -> T.
Parameter sub : U -> T -> T -> T.
Parameter mul : U -> T -> T -> T.

Parameter toSeq : T -> seq C.T.
Parameter mkPoly : seq C.T -> T.
Parameter nth : T -> nat -> C.T.
Parameter size : T -> nat.
Parameter rec1 : (C.T -> nat -> C.T) -> C.T -> nat -> T.
Parameter rec2 : (C.T -> C.T -> nat -> C.T) -> C.T -> C.T -> nat -> T.
Parameter grec1 :
  forall A : Type,
  (A -> nat -> A) ->
  (A -> nat -> C.T) -> A -> seq C.T -> nat -> T.
Parameter map : forall f : C.T -> C.T, T -> T.
Parameter fold : forall V : Type, (C.T -> V -> V) -> V -> T -> V.
Parameter set_nth : T -> nat -> C.T -> T.
Parameter mul_trunc : U -> nat -> T -> T -> T.
Parameter mul_tail : U -> nat -> T -> T -> T.
(** [tlift j pol] represents [pol * X^j] if [pol] is in the monomial basis *)
Parameter lift : nat -> T -> T.
Parameter tail : nat -> T -> T.
Parameter polyC : C.T -> T.
Parameter polyX : T.
Parameter polyNil : T.
Parameter polyCons : C.T -> T -> T.
Parameter horner : U -> T -> C.T -> C.T.
Parameter deriv : U -> T -> T.
Parameter mul_mixed : U -> C.T -> T -> T.
Parameter div_mixed_r : U -> T -> C.T -> T.
Parameter dotmuldiv : U -> seq Z -> seq Z -> T -> T.
Parameter primitive : U -> C.T -> T -> T.

(* specifications of toSeq *)
Parameter toSeq_nil : toSeq zero = [::].
Parameter mkPoly_toSeq : forall p, mkPoly (toSeq p) = p.
Parameter toSeq_mkPoly : forall s, toSeq (mkPoly s) = s.
Parameter horner_seq : forall u p x, horner u p x =
  C.mask (foldr (fun a b => C.add u (C.mul u b x) a) C.zero (toSeq p)) x.
Parameter nth_toSeq : forall p n, nth p n = seq.nth (C.zero) (toSeq p) n.

Parameter polyCE : forall c, polyC c = polyCons c polyNil.
Parameter polyXE : polyX = lift 1 one.
Parameter size_polyX : size polyX = 2.
Parameter oneE : one = polyC C.one.
Parameter zeroE : zero = polyNil.

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

Parameter size_lift : forall n p, size (lift n p) = n + size p.
Parameter size_mul_mixed : forall u a p, size (mul_mixed u a p) = size p.
Parameter size_div_mixed_r : forall u p b, size (div_mixed_r u p b) = size p.
Parameter size_rec1 : forall F x n, size (rec1 F x n) = n.+1.
Parameter size_rec2 : forall F x y n, size (rec2 F x y n) = n.+1.
Parameter size_mul_trunc : forall u n p q, size (mul_trunc u n p q) = n.+1.
Parameter size_mul_tail :
  forall u n p q, size (mul_tail u n p q) = ((size p) + (size q)).-1 - n.+1.
Parameter size_add :
  forall u p1 p2, size (add u p1 p2) = maxn (size p1) (size p2).
Parameter size_opp : forall p1, size (opp p1) = size p1.
Parameter size_map : forall f p, size (map f p) = size p.
Parameter size_sub :
  forall u p1 p2, size (sub u p1 p2) = maxn (size p1) (size p2).
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
Parameter recN :
  forall N : nat, C.T ^ N -> C.T ^^ N --> (nat -> C.T) -> nat -> T.
Parameter lastN : C.T -> forall N : nat, T -> C.T ^ N.

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
*)

Parameter nth_tail : forall n p k, nth (tail n p) k = nth p (n + k).

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

Lemma maskE c x : mask c x = c.
Proof. done. Qed.

Definition pow x n := (power_int tt x (Z_of_nat n)).

Lemma pow_0 x : pow x 0 = one.
Proof. done. Qed.

Lemma pow_S x n : pow x n.+1 = mul tt x (pow x n).
Proof. by move=> *; rewrite /pow /power_int -!Interval_missing.pow_powerRZ. Qed.

Lemma pow_opp x n :
  x <> zero -> power_int tt x (-n) = inv tt (power_int tt x n).
Proof.
case: n=> [||p H] //=; auto with real.
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
  mkseq (fun i => mul_coeff p q np (n.+1+i)) ((np + size q).-1 - n.+1).

Definition mul p q :=
  let np := size p in
  mkseq (mul_coeff p q np) (np + size q).-1.

(* Old definitions

Fixpoint horner' (p : T) (x : C.T) :=
  match p with
    | [::] => C.tzero
    | c :: p' => C.tadd u (C.tmul u (thorner' p' x) x) c
  end.
*)

Definition rec1 := @rec1up C.T.
Definition rec2 := @rec2up C.T.
Definition size := @size C.T.
Definition fold := @foldr C.T.
Definition horner p x :=
  C.mask
  (@fold C.T (fun a b => C.add u (C.mul u b x) a) C.zero p)
  x.
Definition set_nth := @set_nth C.T C.zero.
Definition map := @map C.T C.T.

Definition polyCons := @Cons C.T.

Definition polyNil := @Nil C.T.

Definition polyC (c : C.T) : T := polyCons c polyNil.

Definition polyX := [:: C.zero; C.one].

(* TODO: Revise *)
Lemma poly_ind : forall (f : T -> Type),
  f polyNil ->
  (forall a p, f p -> f (polyCons a p)) ->
  forall p, f p.
Proof.
by move=> f h1 hrec; elim =>//= a e; apply:hrec.
Qed.

Definition deriv_loop := foldri (fun a i s => C.mul u a (C.from_nat i) :: s) [::].

Definition deriv (p : T) := deriv_loop (behead p) 1%N.

Definition grec1 (A : Type) := @grec1up A C.T.

Lemma size_grec1 A F G (q : A) s n : size (grec1 F G q s n) = n.+1.
Proof. by apply size_grec1up. Qed.

Lemma size_rec1 F x n: size (rec1 F x n) = n.+1.
Proof. by apply size_rec1up. Qed.

Lemma size_rec2 F x y n: size (rec2 F x y n) = n.+1.
Proof. by apply size_rec2up. Qed.

Lemma size_mul_trunc n p q: size (mul_trunc n p q) = n.+1.
Proof. by rewrite /size size_mkseq. Qed.

Lemma size_mul_tail n p q:
  size (mul_tail n p q) = ((size p) + (size q)).-1 - n.+1.
Proof. by rewrite /size size_mkseq. Qed.

Lemma size_add p1 p2 : size (add p1 p2) = maxn (size p1) (size p2).
Proof. by rewrite /size /add size_map2. Qed.

Lemma size_opp p1 : size (opp p1) = size p1.
Proof. by rewrite /size /opp size_map. Qed.

Lemma size_sub p1 p2 : size (sub p1 p2) = maxn (size p1) (size p2).
Proof. by rewrite /sub /size size_map2. Qed.

Lemma size_deriv p : size (deriv p) = (size p).-1.
Proof.
rewrite /deriv /deriv_loop.
case: p => [|a p] //=.
elim: p 1 => [|b p IHp] n //=.
by rewrite IHp.
Qed.

End PrecIsPropagated.

Definition tail := @drop C.T.

Definition lift (n : nat) p := ncons n C.zero p.

Lemma size_lift n p : size (lift n p) = n + size p.
Proof (size_ncons n C.zero p).

Definition mul_mixed (u : U) (a : C.T) (p : T) :=
  @foldr C.T T (fun x acc => (C.mul u a x) :: acc) [::] p.

Definition div_mixed_r (u : U) (p : T) (b : C.T) :=
  @foldr C.T T (fun x acc => (C.div u x b) :: acc) [::] p.

Lemma size_mul_mixed u a p : size (mul_mixed u a p) = size p.
Proof. by elim: p => [//|x p IHp]; rewrite /= IHp. Qed.

Lemma size_div_mixed_r u p b : size (div_mixed_r u p b) = size p.
Proof. by elim: p => [//|x p IHp]; rewrite /= IHp. Qed.

Fixpoint dotmuldiv (u : U) (a b : seq Z) (p : T) : T :=
match a, b, p with
| a0 :: a1, b0 :: b1, p0 :: p1 =>
  C.mul u (C.div u (C.fromZ a0) (C.fromZ b0)) p0 ::
  dotmuldiv u a1 b1 p1
| _, _, _ => [::] (* e.g. *)
end.

Lemma fold_polyNil U f iv : @fold U f iv polyNil = iv.
Proof. done. Qed.

Lemma fold_polyCons U f iv c p :
  @fold U f iv (polyCons c p) = f c (@fold U f iv p).
Proof. done. Qed.

Lemma size_set_nth p n val :
  size (set_nth p n val) = maxn n.+1 (size p).
Proof. by rewrite /size seq.size_set_nth. Qed.

Lemma nth_set_nth p n val k :
  nth (set_nth p n val) k = if k == n then val else nth p k.
Proof. by rewrite /nth nth_set_nth. Qed.

Lemma nth_default p n : size p <= n -> nth p n = C.zero.
Proof. by move=> *; rewrite /nth nth_default. Qed.

Lemma set_nth_nth p n : n < size p -> set_nth p n (nth p n) = p.
Proof.
move=> H.
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

Lemma size_polyCons a p : size (polyCons a p) = (size p).+1.
Proof. by []. Qed.

Lemma nth_polyNil n : nth polyNil n = C.zero.
Proof. by rewrite nth_default. Qed.

Lemma nth_polyCons a p k : (* k <= size p -> *)
  nth (polyCons a p) k = if k is k'.+1 then nth p k' else a.
Proof. by case: k. Qed.

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

Lemma mkPoly_toSeq p : mkPoly (toSeq p) = p.
Proof. by []. Qed.

Lemma toSeq_mkPoly s : toSeq (mkPoly s) = s.
Proof. by []. Qed.

Lemma toSeq_nil : toSeq zero = [::].
Proof. by []. Qed.

Lemma horner_seq u p x :
  horner u p x = C.mask (foldr (fun a b => C.add u (C.mul u b x) a)
    C.zero (toSeq p)) x.
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

Lemma size_primitive (c : C.T) (p : T): size (primitive c p) = (size p).+1.
Proof. by rewrite /size /= size_mkseq. Qed.

End precSection.

Lemma nth_tail n p k : nth (tail n p) k = nth p (n + k).
Proof (nth_drop n _ p k).

Lemma size_map f p : size (map f p) = size p.
Proof (size_map f p).

Lemma polyCE c : polyC c = polyCons c polyNil.
Proof. done. Qed.

Lemma polyXE : polyX = lift 1 one.
Proof. done. Qed.

Lemma oneE : one = polyC C.one.
Proof. done. Qed.

Lemma zeroE : zero = polyNil.
Proof. done. Qed.

(* TODO/Erik: Remove polyNil and only speak of zero *)

Lemma size_polyX : size polyX = 2.
Proof. done. Qed.

End SeqPoly.

Module PolR <: PolyOps FullR.
Include SeqPoly FullR.

Module Import Notations.
Delimit Scope rpoly_scope with P.
Notation "p .[ x ]" := (PolR.horner tt p x) : rpoly_scope.
Notation "p ^` ()" := (PolR.deriv tt p) : rpoly_scope.
End Notations.
Local Open Scope rpoly_scope.

Lemma toSeq_horner0 (u : U) (p : T) : horner u p R0 = head R0 (toSeq p).
Proof.
elim: p=> [| a q HI] ; first by [].
by rewrite /= HI; case: u HI; rewrite Rmult_0_r Rplus_0_l.
Qed.

Lemma hornerE p x :
  horner tt p x =
  \big[Rplus/R0]_(0 <= i < size p) Rmult (nth p i) (x ^ i).
Proof.
elim: p; first by rewrite big_mkord big_ord0 /=.
move=> t p /= ->.
rewrite big_nat_recl // pow_O /=.
rewrite Rmult_1_r Rplus_comm.
case: (size p)=> [|n].
  by rewrite !big_mkord !big_ord0 /= Rmult_0_l.
rewrite Rmult_comm big_distrr /=; congr Rplus.
apply: eq_bigr => i _.
by rewrite ![Rmult x _]Rmult_comm Rmult_assoc.
Qed.

Lemma hornerE_wide n p x :
  size p <= n ->
  horner tt p x =
  \big[Rplus/R0]_(0 <= i < n) Rmult (nth p i) (x ^ i).
Proof.
move=> Hn; rewrite hornerE (big_nat_leq_idx _ Hn) //.
by move=> i /andP [Hi _]; rewrite nth_default // Rmult_0_l.
Qed.

Lemma coef_deriv p i :
  nth (deriv tt p) i = (nth p i.+1 * INR i.+1)%R.
Proof.
rewrite /deriv /deriv_loop -{2}[in RHS]addn1.
elim: p i 1 => [|a p IHp] i n; first by rewrite /nth !nth_nil Rmult_0_l.
case: p IHp => [|b p] IHp; first by rewrite /= /nth !nth_nil Rmult_0_l.
case: i => [|i] //=.
rewrite IHp; congr Rmult.
by rewrite addnS.
Qed.

Lemma horner_derivE_wide n p x :
  (size p).-1 <= n ->
  horner tt (deriv tt p) x =
  \big[Rplus/R0]_(0 <= i < n) ((nth p i.+1) * (INR i.+1) * (x ^ i))%R.
Proof.
move=> H.
rewrite (@hornerE_wide n); last by rewrite size_deriv.
apply: eq_bigr => i _.
congr Rmult.
exact: coef_deriv.
Qed.

Lemma horner_derivE p x :
  horner tt (deriv tt p) x =
  \big[Rplus/R0]_(0 <= i < (size p).-1)
    ((nth p i.+1) * (INR i.+1) * (x ^ i))%R.
Proof. by rewrite (@horner_derivE_wide (size p).-1). Qed.

Lemma is_derive_horner p x :
  is_derive (horner tt p) x (horner tt (deriv tt p) x).
Proof.
elim: p => [|a p IHp].
- rewrite /horner /=; exact: is_derive_const.
- apply: (@is_derive_ext _ _ (fun x => horner tt p x * x + a)%R); first done.
  rewrite -[horner _ _ _]Rplus_0_r.
  apply: is_derive_plus; last by auto_derive.
  suff->: horner tt (deriv tt (a :: p)) x =
    ((horner tt (deriv tt p) x) * x + (horner tt p x) * 1)%R.
    apply: is_derive_mult =>//.
    apply: is_derive_id.
    exact: Rmult_comm.
  rewrite (@horner_derivE_wide (size p)) //
          (@horner_derivE_wide (size p).-1) //
          (@hornerE_wide (size p)) //.
  (* Some bigop bookkeeping *)
  rewrite Rmult_1_r.
  rewrite big_distrl.
  case E: (size p) => [|sp]; first by rewrite !(big_mkord, big_ord0) Rplus_0_l.
  rewrite [LHS]big_ltn // [in LHS]big_add1.
  rewrite [in X in _ = (_ + X)%R](big_ltn, big_add1) //.
  rewrite [in RHS]Rplus_comm [in RHS]Rplus_assoc; congr Rplus.
    by rewrite !Rmult_1_r.
  rewrite big_add1.
  rewrite -big_split.
  apply: eq_bigr => i _.
  have->: INR i.+2 = (INR i.+1 + 1)%R by [].
  have->: nth (a :: p) i.+2 = nth p i.+1 by [].
  rewrite -tech_pow_Rmult; simpl; ring.
Qed.

Corollary Derive_horner p x :
  Derive (horner tt p) x = horner tt (deriv tt p) x.
Proof. apply: is_derive_unique; exact: is_derive_horner. Qed.

Corollary ex_derive_horner p x : ex_derive (horner tt p) x.
Proof. exists (horner tt (deriv tt p) x); exact: is_derive_horner. Qed.

Lemma nth_add p1 p2 k :
  nth (add tt p1 p2) k = Rplus (nth p1 k) (nth p2 k).
Proof.
rewrite /nth /add nth_map2_dflt -!/(nth _ _).
by case: (leqP (size p1) k) => H1; case: (leqP (size p2) k) => H2;
  rewrite ?(nth_default H1) ?(nth_default H2); auto with real.
Qed.

Lemma nth_opp p1 k : nth (opp p1) k = Ropp (nth p1 k).
Proof.
rewrite /nth /add nth_map_dflt -!/(nth _ _).
by case: (leqP (size p1) k) => H1;
  rewrite ?(nth_default H1); auto with real.
Qed.

Lemma nth_sub p1 p2 k :
  nth (sub tt p1 p2) k = Rminus (nth p1 k) (nth p2 k).
Proof.
rewrite /nth /add nth_map2_dflt -!/(nth _ _).
by case: (leqP (size p1) k) => H1; case: (leqP (size p2) k) => H2;
  rewrite ?(nth_default H1) ?(nth_default H2); auto with real.
Qed.

Lemma nth_mul_mixed a p1 k :
  nth (mul_mixed tt a p1) k = Rmult a (nth p1 k).
Proof. (* TODO: revise proof, using [map] rather than [foldr] ? *)
elim: p1 k => [|x p IHp] k; first by rewrite nth_default // Rmult_0_r.
case: k IHp => [|k] IHp //; by rewrite /= IHp.
Qed.

Lemma nth_div_mixed_r p1 b k :
  nth (div_mixed_r tt p1 b) k = Rdiv (nth p1 k) b.
Proof.
elim: p1 k => [|x p IHp] k; first by rewrite nth_default // /Rdiv Rmult_0_l.
case: k IHp => [|k] IHp //; by rewrite /= IHp.
Qed.

Lemma nth_lift n p k :
  nth (lift n p) k = if k < n then 0%R else nth p (k - n).
Proof (nth_ncons 0%R n 0%R p k).

Lemma horner_opp p x :
  horner tt (opp p) x = Ropp (horner tt p x).
Proof.
rewrite !hornerE size_opp.
rewrite big_endo ?Ropp_0 //; last exact: Ropp_plus_distr.
apply: eq_bigr => i _ /=.
by rewrite nth_opp Ropp_mult_distr_l_reverse.
Qed.

Lemma horner_add p q x :
  horner tt (add tt p q) x = (horner tt p x + horner tt q x)%R.
Proof.
rewrite !(@hornerE_wide (maxn (size p) (size q))).
rewrite -big_split; apply: eq_bigr => i _ /=.
by rewrite nth_add Rmult_plus_distr_r.
exact: leq_maxr.
exact: leq_maxl.
by rewrite size_add.
Qed.

Lemma horner_sub p q x :
  horner tt (sub tt p q) x = (horner tt p x - horner tt q x)%R.
Proof.
rewrite !(@hornerE_wide (maxn (size p) (size q))).
rewrite /Rminus.
rewrite (big_endo Ropp); first last.
  by rewrite Ropp_0.
  exact: Ropp_plus_distr.
rewrite -big_split; apply: eq_bigr => i _ /=.
by rewrite -/(Rminus _ _) nth_sub Rmult_minus_distr_r.
exact: leq_maxr.
exact: leq_maxl.
by rewrite size_sub.
Qed.

Lemma horner_lift n p x :
  horner tt (lift n p) x = (horner tt p x * x ^ n)%R.
Proof.
rewrite !hornerE (*(@hornerE_wide (size (lift n p))) *).
rewrite (big_endo (fun y => y * x ^ n)%R); first last.
  by rewrite Rmult_0_l.
  by red=> *; rewrite Rmult_plus_distr_r.
rewrite size_lift.
rewrite (@big_cat_nat _ _ _ n) ?leq_addr //=.
rewrite big1_seq; first last.
  move=> i /andP [_ Hi]; rewrite nth_lift ifT ?Rmult_0_l //.
  by move: Hi; rewrite mem_index_iota; case/andP.
rewrite Rplus_0_l -{1}(add0n n) big_addn addKn.
apply: eq_bigr => i _ /=.
rewrite nth_lift ifF ?(ltnNge, leq_addl) //.
rewrite addnK Rmult_assoc; congr Rmult.
by rewrite pow_add.
Qed.

Lemma horner_mul_mixed a p x :
  horner tt (mul_mixed tt a p) x = (a * horner tt p x)%R.
Proof.
rewrite !hornerE size_mul_mixed.
rewrite big_endo; first last.
  by rewrite Rmult_0_r.
  by move=> *; rewrite Rmult_plus_distr_l.
apply: eq_bigr => i _.
by rewrite nth_mul_mixed Rmult_assoc.
Qed.

Lemma horner_div_mixed_r p b x :
  horner tt (div_mixed_r tt p b) x = (horner tt p x / b)%R.
Proof.
rewrite !hornerE size_div_mixed_r /Rdiv Rmult_comm.
rewrite big_endo; first last.
  by rewrite Rmult_0_r.
  by move=> *; rewrite Rmult_plus_distr_l.
apply: eq_bigr => i _.
by rewrite nth_div_mixed_r -Rmult_assoc; congr Rmult; rewrite Rmult_comm.
Qed.

(*
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
Module Import Aux := IntervalAux I. (* for Aux.eqNai *)
Include PolyOps Int.

Definition contains_pointwise pi p : Prop :=
  forall k, contains (I.convert (nth pi k)) (Xreal (PolR.nth p k)).

(* Very similar definition, suitable for specifying grec1 *)
Definition seq_contains_pointwise si s : Prop :=
  forall k, contains (I.convert (seq.nth Int.zero si k)) (Xreal (PolR.nth s k)).

Notation seq_eq_size si s := (seq.size si = seq.size s).

Module Import Notations.
Delimit Scope ipoly_scope with IP.
Notation "i >: x" := (contains (I.convert i) (Xreal x)) : ipoly_scope.
Notation "p >:: x" := (contains_pointwise p x) : ipoly_scope.
Notation eq_size pi p := (size pi = PolR.size p).
End Notations.
Local Open Scope ipoly_scope.

Parameter horner_correct :
  forall u pi ci p x, pi >:: p -> ci >: x -> horner u pi ci >: PolR.horner tt p x.

Parameter polyC_correct : forall ci c, ci >: c -> polyC ci >:: PolR.polyC c.
Parameter polyX_correct : polyX >:: PolR.polyX.

Parameter zero_correct : zero >:: PolR.zero.
Parameter one_correct : one >:: PolR.one.
Parameter opp_correct : forall pi p, pi >:: p -> opp pi >:: PolR.opp p.
Parameter map_correct :
  forall fi f pi p,
  (f 0%R = 0%R) ->
  (forall xi x, xi >: x -> fi xi >: f x) ->
  pi >:: p ->
  map fi pi >:: PolR.map f p.
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
Parameter mul_mixed_correct :
  forall u ai pi a p, ai >: a -> pi >:: p ->
  mul_mixed u ai pi >:: PolR.mul_mixed tt a p.
Parameter div_mixed_r_correct :
  forall u pi bi p b, pi >:: p -> bi >: b ->
  div_mixed_r u pi bi >:: PolR.div_mixed_r tt p b.
Parameter horner_propagate : forall u pi, I.propagate (horner u pi).
Parameter deriv_correct :
  forall u pi p, pi >:: p -> deriv u pi >:: (PolR.deriv tt p).
Parameter lift_correct : forall n pi p, pi >:: p -> lift n pi >:: PolR.lift n p.
Parameter tail_correct : forall n pi p, pi >:: p -> tail n pi >:: PolR.tail n p.
Parameter set_nth_correct :
  forall pi p n ai a, pi >:: p -> ai >: a -> set_nth pi n ai >:: PolR.set_nth p n a.
Parameter polyNil_correct : polyNil >:: PolR.polyNil. (* strong enough ? *)
Parameter polyCons_correct :
  forall pi xi p x, pi >:: p -> xi >: x ->
  polyCons xi pi >:: PolR.polyCons x p.
Parameter rec1_correct :
  forall fi f fi0 f0 n,
    (forall ai a m, ai >: a -> fi ai m >: f a m) -> fi0 >: f0 ->
    rec1 fi fi0 n >:: PolR.rec1 f f0 n.
Parameter rec2_correct :
  forall fi f fi0 f0 fi1 f1 n,
    (forall ai bi a b m, ai >: a -> bi >: b -> fi ai bi m >: f a b m) ->
    fi0 >: f0 -> fi1 >: f1 ->
    rec2 fi fi0 fi1 n >:: PolR.rec2 f f0 f1 n.
Parameter grec1_correct :
  forall (A := PolR.T) Fi (F : A -> nat -> A) Gi (G : A -> nat -> R) ai a si s n,
  (forall qi q m, qi >:: q -> Fi qi m >:: F q m) ->
  (forall qi q m, qi >:: q -> Gi qi m >: G q m) ->
  ai >:: a ->
  seq_contains_pointwise si s ->
  seq_eq_size si s ->
  grec1 Fi Gi ai si n >:: PolR.grec1 F G a s n.

(* TODO size_correct *)
(* TODO recN_correct : forall N : nat, C.T ^ N -> C.T ^^ N --> (nat -> C.T) -> nat -> T. *)
(* TODO lastN_correct : C.T -> forall N : nat, T -> C.T ^ N. *)

Parameter nth_default_alt : forall pi p, pi >:: p ->
  forall n : nat, size pi <= n -> PolR.nth p n = 0%R.

Definition poly_eqNai s := forall k, k < size s -> eqNai (nth s k).

Definition seq_eqNai s := forall k, k < seq.size s -> eqNai (seq.nth I.zero s k).

Parameter grec1_propagate :
  forall A (Fi : A -> nat -> A) (Gi : A -> nat -> I.type) ai si,
  (forall qi m, eqNai (Gi qi m)) ->
  seq_eqNai si ->
  forall n, poly_eqNai (grec1 Fi Gi ai si n).
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

Notation seq_eq_size si s := (seq.size si = seq.size s).

Module Import Notations.
Delimit Scope ipoly_scope with IP.
Notation "i >: x" := (contains (I.convert i) (Xreal x)) : ipoly_scope.
Notation "p >:: x" := (contains_pointwise p x) : ipoly_scope.
Notation eq_size pi p := (size pi = PolR.size p).
End Notations.
Local Open Scope ipoly_scope.

Definition poly_eqNai s := forall k, k < size s -> eqNai (nth s k).

Definition seq_eqNai s := forall k, k < seq.size s -> eqNai (seq.nth I.zero s k).

Lemma horner_propagate u pi : I.propagate (horner u pi).
Proof. by red=> *; rewrite /horner I.mask_propagate_r. Qed.

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

Lemma map_correct fi f pi p :
  (f 0%R = 0%R) ->
  (forall xi x, xi >: x -> fi xi >: f x) ->
  pi >:: p ->
  map fi pi >:: PolR.map f p.
Proof.
move=> H0 Hf Hp k; rewrite /map /PolR.map /nth /PolR.nth.
apply(*:*) (@map_correct R I.type) =>//.
- exact: cont0.
- by move=> ? /only0 ->; rewrite H0; apply: cont0.
- by move=> *; rewrite -(H0); apply: Hf.
- move=> *; exact: Hf.
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

(*
Lemma add_propagate_l u pi qi :
  poly_eqNai pi -> poly_eqNai (add u pi qi).
Proof.
move=> H k Hk.
rewrite size_add in Hk.
have := H k.
Abort.
*)

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
  apply: leq_addLRI; rewrite addnC; apply: leq_trans _ Hk.
  by rewrite leq_add2r.
- move=> k /andP [Hk _]; rewrite (mul_coeff_resize Hp Hq) PolR.mul_coeffE /size.
  case Epi0 : (seq.size pi) => [|n]; first by rewrite big_mkord big_ord0.
  rewrite Epi0 addSn /= in Hk.
  rewrite big_mkord big1 //; move => [i Hi _] /=.
  rewrite ltnS in Hi.
  suff Hki: (size qi) <= k - i by rewrite (nth_default_alt Hq Hki) Rmult_0_r.
  apply: leq_addLRI; rewrite addnC; apply: leq_trans _ Hk.
  by rewrite leq_add2r.
Qed.


Lemma mul_trunc_correct u n pi qi p q :
  pi >:: p -> qi >:: q ->
  mul_trunc u n pi qi >:: PolR.mul_trunc tt n p q.
Proof.
move=> Hp Hq; rewrite /nth /PolR.nth.
apply: (mkseq_correct (Rel := fun r i => i >: r)) =>//.
- exact: cont0.
- exact: mul_coeff_correct.
- by move=> k; rewrite ltn_leqN.
- by move=> k; rewrite ltn_leqN.
Qed.

Lemma mul_tail_correct u n pi qi p q :
  pi >:: p -> qi >:: q ->
  mul_tail u n pi qi >:: PolR.mul_tail tt n p q.
Proof.
move=> Hp Hq; rewrite /mul_tail /PolR.mul_tail /nth /PolR.nth.
apply: (mkseq_correct (Rel := fun r i => i >: r)) =>//.
- exact: cont0.
- move=> k; exact: mul_coeff_correct.
- move=> k /andP [_k k_]; rewrite PolR.mul_coeffE.
  case Ep0 : (seq.size p) => [|m]; first by rewrite big_mkord big_ord0.
  rewrite Ep0 addSn /= in _k.
  rewrite big_mkord big1 //; move => [i Hi _] /=.
  rewrite ltnS in Hi.
  suff Hki: (seq.size q) <= n.+1 + k - i by rewrite (PolR.nth_default Hki) Rmult_0_r.
  apply: leq_addLRI; rewrite addnC; rewrite leq_subLR in _k.
  by apply: leq_trans _ _k; rewrite leq_add2r.
- move=> k /andP [_k k_]; rewrite (mul_coeff_resize Hp Hq) PolR.mul_coeffE /size.
  case Epi0 : (seq.size pi) => [|m]; first by rewrite big_mkord big_ord0.
  rewrite Epi0 addSn /= in _k.
  rewrite big_mkord big1 //; move => [i Hi _] /=.
  rewrite ltnS in Hi.
  suff Hki: (size qi) <= n.+1 + k - i.
    by rewrite (nth_default_alt Hq Hki) Rmult_0_r.
  apply: leq_addLRI; rewrite addnC; rewrite leq_subLR in _k.
  by apply: leq_trans _ _k; rewrite leq_add2r.
Qed.

Lemma mul_mixed_correct  u ai pi a p :
  ai >: a ->
  pi >:: p ->
  mul_mixed u ai pi >:: PolR.mul_mixed tt a p.
Proof.
move=> Ha Hp; rewrite /mul_mixed /PolR.mul_mixed.
apply: (seq_foldr_correct (Rel := fun v t => t >: v)) =>//.
- move=> x s /only0 -> Hs [|k] /=; first by rewrite Rmult_0_r; apply: cont0.
  by move: (Hs k); rewrite nth_nil.
- move=> x s Hx Hs [|k]; first by rewrite -(Rmult_0_r a); apply: R_mul_correct.
  by move: (Hs k); rewrite nth_nil.
- move=> x y s t Hx Hs [|k]; first by apply: R_mul_correct.
  by apply: Hs.
Qed.

Lemma div_mixed_r_correct u pi bi p b :
  pi >:: p ->
  bi >: b ->
  div_mixed_r u pi bi >:: PolR.div_mixed_r tt p b.
Proof.
move=> Ha Hp; rewrite /div_mixed_r /PolR.div_mixed_r.
apply: (seq_foldr_correct (Rel := fun v t => t >: v)) =>//.
- move=> x s /only0 -> Hs [|k] /=; first by rewrite /Rdiv Rmult_0_l; apply: cont0.
  by move: (Hs k); rewrite nth_nil.
- move=> x s Hx Hs [|k]; last by move: (Hs k); rewrite nth_nil.
  by rewrite -(Rmult_0_l (Rinv b)); apply: R_div_correct.
- move=> x y s t Hx Hs [|k]; first by apply: R_div_correct.
  by apply: Hs.
Qed.

Lemma horner_correct u pi ai p a :
  pi >:: p -> ai >: a -> horner u pi ai >: PolR.horner tt p a.
Proof.
move=> Hp Ha.
rewrite /horner /PolR.horner.
apply: (R_mask_correct a _ Ha).
apply: (foldr_correct (Rel := fun v t => t >: v)) =>//.
- exact: cont0.
- move=> x y /only0 -> /only0 ->; rewrite Rmult_0_l Rplus_0_r; exact: cont0.
- move=> x y Hx Hy; rewrite -(Rplus_0_r R0) -{1}(Rmult_0_l a).
  apply: R_add_correct =>//; exact: R_mul_correct.
- move=> x xi y yi Hx Hy; apply: R_add_correct=>//; exact: R_mul_correct.
Qed.

Lemma deriv_correct u pi p : pi >:: p -> deriv u pi >:: PolR.deriv tt p.

Proof.
move=> Hpi; rewrite /deriv /PolR.deriv /deriv_loop /PolR.deriv_loop.
apply: (seq_foldri_correct (Rel := fun v t => t >: v)) =>//.
- by move=> k; rewrite !nth_behead.
- move=> x s i Hx Hs [|k] /=.
  + by move/only0: Hx->; rewrite Rmult_0_l; apply: cont0.
  + by move: (Hs k); rewrite nth_nil.
- move=> x s i Hx Hs [|k] /=.
  rewrite -(Rmult_0_l (INR i)).
  apply: R_mul_correct =>//; rewrite INR_Z2R; apply: I.fromZ_correct.
  by move: (Hs k); rewrite nth_nil.
- move=> x xi y yi i Hx Hy [|k] //=.
  by apply: R_mul_correct =>//; rewrite INR_Z2R; apply: I.fromZ_correct.
Qed.

Lemma set_nth_correct pi p n ai a :
  pi >:: p -> ai >: a -> set_nth pi n ai >:: PolR.set_nth p n a.
Proof.
move=> Hp Ha k; rewrite /nth /PolR.nth.
exact: (seq_compl.set_nth_correct (Rel := fun v t => t >: v)).
Qed.

Lemma lift_correct n pi p : pi >:: p -> lift n pi >:: PolR.lift n p.
Proof.
move=> Hp k; rewrite /nth /PolR.nth.
by apply: (ncons_correct (Rel := fun v t => t >: v)); first exact: cont0.
Qed.

Lemma tail_correct n pi p : pi >:: p -> tail n pi >:: PolR.tail n p.
move=> Hp k; rewrite /nth /PolR.nth.
exact: (drop_correct (Rel := fun v t => t >: v)).
Qed.

Lemma polyNil_correct : polyNil >:: PolR.polyNil.
Proof. intro; rewrite /nth /PolR.nth ![seq.nth _ _ _]nth_nil; exact: cont0. Qed.

Lemma polyCons_correct pi xi p x :
  pi >:: p -> xi >: x -> polyCons xi pi >:: PolR.polyCons x p.
Proof. by move=> Hp Hx [|k] /=. Qed.

Lemma rec1_correct fi f fi0 f0 n :
  (forall ai a m, ai >: a -> fi ai m >: f a m) ->
  fi0 >: f0 ->
  rec1 fi fi0 n >:: PolR.rec1 f f0 n.
Proof.
move=> Hf Hf0.
by apply: (rec1up_correct (Rel := fun r i => i >: r)); first exact: cont0.
Qed.

Lemma rec2_correct fi f fi0 f0 fi1 f1 n :
  (forall ai bi a b m, ai >: a -> bi >: b -> fi ai bi m >: f a b m) ->
  fi0 >: f0 ->
  fi1 >: f1 ->
  rec2 fi fi0 fi1 n >:: PolR.rec2 f f0 f1 n.
Proof.
move=> Hf Hf0 Hf1.
by apply: (rec2up_correct (Rel := fun r i => i >: r)); first exact: cont0.
Qed.

Lemma grec1_correct
  (A := PolR.T) Fi (F : A -> nat -> A) Gi (G : A -> nat -> R) ai a si s n :
  (forall qi q m, qi >:: q -> Fi qi m >:: F q m) ->
  (forall qi q m, qi >:: q -> Gi qi m >: G q m) ->
  ai >:: a ->
  seq_contains_pointwise si s ->
  eq_size si s ->
  grec1 Fi Gi ai si n >:: PolR.grec1 F G a s n.
Proof.
move=> HF HG Ha Hs Hsize.
by apply: (grec1up_correct (Rel := fun r i => i >: r)); first exact: cont0.
Qed.

(* Check all_nthP *)
Lemma grec1_propagate A (Fi : A -> nat -> A) (Gi : A -> nat -> I.type) ai si :
  (forall qi m, eqNai (Gi qi m)) ->
  seq_eqNai si ->
  forall n, poly_eqNai (grec1 Fi Gi ai si n).
Proof.
move=> HG Hs n k Hk.
rewrite /grec1 /size size_grec1up ltnS in Hk.
rewrite /grec1 /nth nth_grec1up.
rewrite ltnNge Hk /=.
case: ltnP => H2.
- exact: Hs.
- exact: HG.
Qed.

(* TODO size_correct *)
(* TODO recN_correct : forall N : nat, C.T ^ N -> C.T ^^ N --> (nat -> C.T) -> nat -> T. *)
(* TODO lastN_correct : C.T -> forall N : nat, T -> C.T ^ N. *)

Lemma polyC_correct ci c : ci >: c -> polyC ci >:: PolR.polyC c.
Proof.
move=> Hc [//|k].
rewrite /polyC /PolR.polyC.
rewrite nth_polyCons PolR.nth_polyCons.
rewrite nth_polyNil PolR.nth_polyNil.
exact: cont0.
Qed.

Lemma polyX_correct : polyX >:: PolR.polyX.
Proof.
case=> [|k] /=; first exact: cont0.
case: k => [|k] /=; first by change R1 with (INR 1); apply: I.fromZ_correct.
rewrite /nth /PolR.nth !nth_nil.
exact: cont0.
Qed.

End SeqPolyInt.
