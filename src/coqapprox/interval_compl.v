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

Require Import ZArith Reals Psatz.
Require Import Coquelicot.
Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_interval Interval_xreal_derive.
Require Import Ssreflect.ssreflect Ssreflect.ssrbool Ssreflect.ssrfun Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq.
Require Import MathComp.div Ssreflect.fintype MathComp.finfun MathComp.path MathComp.bigop.
Require Import Rstruct xreal_ssr_compat taylor_thm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.

(****************************************************************************)
(** Additional support results on extended reals and/or interval arithmetic *)
(****************************************************************************)

Lemma Xsub_Xreal_l x y :
  Xsub x y <> Xnan -> x = Xreal (proj_val x).
Proof. by case: x. Qed.

Lemma Xsub_Xreal_r x y :
  Xsub x y <> Xnan -> y = Xreal (proj_val y).
Proof. by case: x; case: y. Qed.

Lemma Xsub_Xnan_r x :
  Xsub x Xnan = Xnan.
Proof. by case: x. Qed.

Lemma Xneg_as_Xmul (x : ExtendedR) : Xneg x = Xmul x (Xreal (-1)).
Proof. destruct x as [|x]; trivial; simpl; f_equal; ring. Qed.

Lemma contains_trans (X : interval) (a b c : ExtendedR) :
  contains X a -> contains X b -> contains (Interval_interval.Ibnd a b) c ->
  contains X c.
Proof.
intros Ha Hb Hc.
destruct a as [|a]; destruct b as [|b]; destruct c as [|c];
  destruct X as [|l u]; trivial.
- now destruct Ha.
- now destruct Ha.
- now destruct Hb.
- destruct l as [|l]; destruct u as [|u]; trivial; simpl in *.
  + now repeat split; apply Rle_trans with (1 := proj2 Hc) (2 := proj2 Hb).
  + now repeat split; apply Rle_trans with (1 := proj1 Ha) (2 := proj1 Hc).
  + split.
    * now apply Rle_trans with (1 := proj1 Ha) (2 := proj1 Hc).
    * now apply Rle_trans with (1 := proj2 Hc) (2 := proj2 Hb).
Qed.

Notation IIbnd := Interval_interval.Ibnd (only parsing).
Notation IInan := Interval_interval.Inan (only parsing).

Local Notation subset_ := Interval_interval.subset (only parsing).

Lemma subset_refl : forall x, subset_ x x.
Proof.
case => [|l u] =>//=; rewrite /le_lower /le_upper; split.
  by case (-l)%XR => //; apply Rle_refl.
by case u => //; apply Rle_refl.
Qed.

Lemma contains_subset (X Y : interval) :
  (exists t, contains X t) ->
  (forall v : ExtendedR, contains X v -> contains Y v) ->
  subset_ X Y.
Proof.
case: X =>[|l u]; case: Y =>[|L U] //; first by move=>_ /(_ Xnan); apply.
move=>[t Ht] Hmain.
have {t Ht} [r Hr] : exists r : R, contains (IIbnd l u) (Xreal r).
  exact: contains_not_empty Ht.
have H'r := Hmain _ Hr; split; move: Hmain Hr H'r.
  case: L=>[//|L]; case: l=>[|l] Hmain Hr H'r; first exfalso.
    move/(_ (Xreal (L - 1))): Hmain.
    by move: Hr H'r; rewrite /contains; case: u; intuition psatzl R.
  case/(_ (Xreal l)): Hmain.
    by move: Hr H'r; rewrite /contains; case: u; intuition psatzl R.
  by rewrite /le_lower => top _ /=; psatzl R.
case: U=>[//|U]; case: u=>[|u] Hmain Hr H'r; first exfalso.
  move/(_ (Xreal (U + 1))): Hmain.
  by move: Hr H'r; rewrite /contains; case: l; intuition psatzl R.
case/(_ (Xreal u)): Hmain =>//.
by move: Hr H'r; rewrite /contains; case: l; intuition psatzl R.
Qed.

Definition defined (f : ExtendedR -> ExtendedR) (x : R) : bool :=
  match f (Xreal x) with
  | Xnan => false
  | Xreal _ => true
  end.

Lemma definedP f x : reflect (f (Xreal x) <> Xnan) (defined f x).
Proof. by apply: introP; rewrite /defined; case: (f _) =>//; intuition. Qed.

Lemma definedPn f x : f (Xreal x) = Xnan <-> ~~ defined f x.
Proof. by rewrite /defined; case: (f (Xreal x)). Qed.

Lemma definedPf f x : f (Xreal x) = Xnan <-> defined f x = false.
Proof. by rewrite /defined; case: (f (Xreal x)). Qed.

Lemma defined_ext g f x :
  f (Xreal x) = g (Xreal x) -> defined f x = defined g x.
Proof.
by rewrite /defined =>->.
Qed.

Lemma toXreal_nan (f : R -> R) :
  toXreal_fun f Xnan = Xnan.
Proof. done. Qed.

Definition some_real : R. exact R0. Qed.

Definition toR_fun (f : ExtendedR -> ExtendedR) (x : R) : R :=
  proj_fun some_real f x.

Lemma Xreal_toR (f : ExtendedR -> ExtendedR) (x : R) :
  defined f x ->
  Xreal (toR_fun f x) = f (Xreal x).
Proof. by rewrite /toR_fun /proj_fun /defined; case: f. Qed.

Lemma toR_toXreal (f : R -> R) :
  toR_fun (toXreal_fun f) = f.
Proof. done. Qed.

Lemma toR_toXreal_ext f g :
  g =1 toXreal_fun f ->
  toR_fun g =1 f.
Proof. by move=> Hg r; rewrite /toR_fun /proj_fun Hg. Qed.

Lemma toXreal_toR (f : ExtendedR -> ExtendedR) (x : R) :
  defined f x ->
  toXreal_fun (toR_fun f) (Xreal x) = f (Xreal x).
Proof. by rewrite /= /toR_fun /proj_fun /defined; case: (f (Xreal x)). Qed.


Definition Xsign_large_ xl xu :=
  match Xcmp xl (Xreal 0), Xcmp xu (Xreal 0) with
  | Xeq, Xeq => Xeq
  | _, Xlt => Xlt
  | _, Xeq => Xlt
  | Xgt, _ => Xgt
  | Xeq, _ => Xgt
  | _, _ => Xund
  end.

Definition Xsign_large xi :=
  match xi with
  | IIbnd xl xu => Xsign_large_ xl xu
  | IInan => Xund
  end.

Definition Xsign_strict_ xl xu :=
  match Xcmp xl (Xreal 0), Xcmp xu (Xreal 0) with
  | Xeq, Xeq => Xeq
  | _, Xlt => Xlt
  | Xgt, _ => Xgt
  | _, _ => Xund
  end.

Definition Xsign_strict xi :=
  match xi with
  | IIbnd xl xu => Xsign_strict_ xl xu
  | IInan => Xund
  end.

Definition Xge0 xi : bool :=
  if Xsign_large xi is Xgt then true else false.

Definition Xle0 xi : bool :=
  if Xsign_large xi is Xlt then true else false.

Definition Xgt0 xi : bool :=
  if Xsign_strict xi is Xgt then true else false.

Definition Xlt0 xi : bool :=
  if Xsign_strict xi is Xlt then true else false.

Definition contains_bool xi v : bool :=
match xi with
| IInan => true
| IIbnd l u =>
    match v with
    | Xnan => false
    | Xreal x =>
        match l with
        | Xnan => true
        | Xreal r => Rle_bool r x
        end && match u with
               | Xnan => true
               | Xreal r => Rle_bool x r
               end
    end
end.

Definition containsP xi v : reflect (contains xi v) (contains_bool xi v).
Proof.
apply: introP; rewrite /contains /contains_bool;
  case: xi => [|[|l][|u]]; case: v => [|v] //; try by intuition.
by case: Rle_bool_spec.
by case: Rle_bool_spec.
by do 2!case: Rle_bool_spec.
by case: Rle_bool_spec =>//; move/Rlt_not_le; intuition.
by case: Rle_bool_spec =>//; move/Rlt_not_le; intuition.
by do 2!case: Rle_bool_spec =>//;
  move/Rlt_not_le; (by intuition) || move=> H; move/Rlt_not_le; by intuition.
Qed.

Lemma contains_Xreal (xi : interval) (x : ExtendedR) :
  contains xi x -> contains xi (Xreal (proj_val x)).
Proof. by case: x =>//; case: xi. Qed.

(*******************************************************************************)
(** For convenience, define a predicate [not_empty'] equivalent to [not_empty] *)
(*******************************************************************************)

Definition not_empty' (xi : interval) := exists v : ExtendedR, contains xi v.

Lemma not_emptyE xi : not_empty' xi -> not_empty xi.
Proof.
case: xi =>[|l u] [v Hv]; first by exists R0.
case: v Hv =>[//|r] Hr.
by exists r.
Qed.

Lemma not_empty'E xi : not_empty xi -> not_empty' xi.
case=>[r Hr]; by exists (Xreal r).
Qed.

(***************************************************************)
(** Some Reals-based specs to ease the CoqApprox formalization *)
(***************************************************************)

Lemma Xreal_neg x : Xreal (Ropp x) = Xneg (Xreal x).
Proof. done. Qed.

Lemma Xreal_sub x y : Xreal (x - y) = Xsub (Xreal x) (Xreal y).
Proof. done. Qed.

Lemma Xreal_add x y : Xreal (x + y) = Xadd (Xreal x) (Xreal y).
Proof. done. Qed.

Lemma Xreal_mul x y : Xreal (x * y) = Xmul (Xreal x) (Xreal y).
Proof. done. Qed.

Lemma Xreal_sqr x : Xreal (x ²) = Xsqr (Xreal x).
Proof. done. Qed.

Lemma Xreal_power_int x n :
  x <> 0%R \/ (n >= 0)%Z -> Xreal (powerRZ x n) = Xpower_int (Xreal x) n.
Proof.
case: n => [//|//|n].
case=> [Hx|Hn]; by [rewrite /= zeroF | exfalso; auto with zarith].
Qed.

Lemma Xreal_div x y : y <> 0%R -> Xreal (x / y) = Xdiv (Xreal x) (Xreal y).
Proof. by move=> H; rewrite /Xdiv zeroF. Qed.

Lemma Xreal_inv y : y <> 0%R -> Xreal (/ y) = Xinv (Xreal y).
Proof. by move=> H; rewrite /Xinv zeroF. Qed.

Lemma Xreal_abs x : Xreal (Rabs x) = Xabs (Xreal x).
Proof. done. Qed.

Lemma Xreal_sqrt x : (0 <= x)%R -> Xreal (sqrt x) = Xsqrt (Xreal x).
Proof.
move=> H; rewrite /Xsqrt ifF //.
case: is_negative_spec =>//.
by move/Rle_not_lt in H.
Qed.

Lemma Xreal_cos x : Xreal (cos x) = Xcos (Xreal x).
Proof. done. Qed.

Lemma Xreal_sin x : Xreal (sin x) = Xsin (Xreal x).
Proof. done. Qed.

Lemma Xreal_tan x : cos x <> 0%R -> Xreal (tan x) = Xtan (Xreal x).
Proof. by move=> H; rewrite Xreal_div. Qed.

Lemma Xreal_atan x : Xreal (atan x) = Xatan (Xreal x).
Proof. done. Qed.

Lemma Xreal_exp x : Xreal (exp x) = Xexp (Xreal x).
Proof. done. Qed.

Lemma Xreal_ln x : (0 < x)%R -> Xreal (ln x) = Xln (Xreal x).
Proof. by move=> H; rewrite /Xln positiveT. Qed.

(* Check (contains_subset, subset_contains). *)

Lemma contains_Xgt (a b : ExtendedR) :
  not_empty (IIbnd a b) ->
  Xcmp a b <> Xgt.
Proof.
move=> [x Hx].
case E : (Xcmp a b) =>//.
move=> _.
rewrite /contains in Hx.
case: a b E Hx => [//|ra [//|rb /=]].
by case: Rcompare_spec =>//; psatzl R.
Qed.

Lemma Xund_imp (a b : ExtendedR) :
  Xcmp a b = Xund -> a = Xnan \/ b = Xnan.
Proof.
case: a =>[|a]; first by left.
case: b =>[|b]; first by right.
by rewrite /=; case: Rcompare_spec.
Qed.

Lemma Xund_contra (a b : ExtendedR) :
  a <> Xnan -> b <> Xnan -> Xcmp a b <> Xund.
Proof.
move=> Ha Hb K.
by case: (Xund_imp K).
Qed.

Lemma Xeq_imp (a b : ExtendedR) :
  Xcmp a b = Xeq -> a = b.
Proof.
rewrite /Xcmp.
case: a =>[|r]; case: b =>[|s] //.
by case: Rcompare_spec =>//->.
Qed.

Lemma proj_fun_id (v x : R) : proj_fun v (@id ExtendedR) x = x.
Proof. done. Qed.

Lemma notIInan_IIbnd : forall (X : interval),
  X <> IInan -> exists a : ExtendedR, exists b : ExtendedR, X = IIbnd a b.
Proof. by case =>[//|a b]; exists a; exists b. Qed.

(** * Some support lemmas about ExtendedR, I.bound_type, or I.type *)

Lemma le_upper_or (x y : ExtendedR) : le_upper x y \/ le_upper y x.
Proof.
case: x; case: y; [left|right|left|idtac]=>//.
by move=> r s; rewrite /le_lower /=; psatzl R.
Qed.

Lemma le_lower_or (x y : ExtendedR) : le_lower x y \/ le_lower y x.
Proof. by rewrite /le_lower; apply: le_upper_or. Qed.

Lemma contains_lower_le_upper (X : interval) x :
  contains X x ->
  match (Xlower X), (Xupper X) with
  | Xreal r, Xreal s => (r <= s)%Re
  | _, _ => True
  end.
Proof.
case: X =>[//|l u]; case: l=>[//|l]; case: u=>[//|u] /=.
by case: x; intuition psatzl R.
Qed.

Lemma contains_IIbnd_Xreal (a b x : ExtendedR) :
  contains (IIbnd a b) x ->
  x = Xreal (proj_val x).
Proof. by case: x. Qed.

(**************************************************************)
(** Some support results relating inequalities and [contains] *)
(**************************************************************)

Definition intvl a b x := (a <= x <= b)%R.

Lemma intvl_connected a b : connected (intvl a b).
Proof.
move=> x y Hx Hy z Hz; split.
- exact: Rle_trans (proj1 Hx) (proj1 Hz).
- exact: Rle_trans (proj2 Hz) (proj2 Hy).
Qed.

Lemma intvlE a b x : intvl a b x = contains (IIbnd (Xreal a) (Xreal b)) (Xreal x).
Proof. done. Qed.

Lemma intvl_trans x y a b z :
  intvl a b x -> intvl a b y -> intvl x y z -> intvl a b z.
Proof. by move=> H1 H2 H3; apply: (@intvl_connected a b _ _ H1 H2 _ H3). Qed.

Lemma contains_intvl_trans : forall x y X z,
  contains X (Xreal x) ->
  contains X (Xreal y) ->
  intvl x y z ->
  contains X (Xreal z).
Proof.
clear; move=> x y X z.
rewrite /contains.
case: X => [//|l u].
case: l => [|l]; case: u => [|u]; move=> [H1 H2] [H3 H4] [H5 H6]; split=>//.
exact: Rle_trans H6 H4.
exact: Rle_trans H1 H5.
exact: Rle_trans H1 H5.
exact: Rle_trans H6 H4.
Qed.

Lemma intvl_lx l u x0 :
  intvl l u x0 -> intvl l x0 x0.
Proof. by case=> [H1 H2]; split =>//; apply: Rle_refl. Qed.

Lemma intvl_xu l u x0 :
  intvl l u x0 -> intvl x0 u x0.
Proof. by case=> [H1 H2]; split =>//; apply: Rle_refl. Qed.

Lemma intvl_l l u x0 :
  intvl l u x0 -> intvl l u l.
Proof. by case=> [H1 H2]; split =>//; apply: Rle_refl || apply: Rle_trans H2. Qed.

Lemma intvl_u l u x0 :
  intvl l u x0 -> intvl l u u.
Proof. by case=> [H1 H2]; split =>//; apply: Rle_refl || apply: Rle_trans H2. Qed.

Lemma intvl_lVu l u x0 x :
  intvl l u x -> intvl l u x0 -> intvl l x0 x \/ intvl x0 u x.
Proof.
move=> [H1 H2] [H3 H4].
have [Hle|Hlt] := Rle_lt_dec x x0.
by left.
by move/Rlt_le in Hlt; right.
Qed.

(********************************************)
(** Some support results about monotonicity *)
(********************************************)

Section PredArg.
Variable P : R -> Prop.

Definition Rincr (f : R -> R) :=
  forall x y : R,
  P x -> P y ->
  (x <= y -> f x <= f y)%R.

Definition Rdecr (f : R -> R) :=
  forall x y : R,
  P x -> P y ->
  (x <= y -> f y <= f x)%R.

Definition Rmonot (f : R -> R) :=
  Rincr f \/ Rdecr f.

Definition Rpos_over (g : R -> R) :=
  forall x : R, (P x -> 0 <= g x)%R.

Definition Rneg_over (g : R -> R) :=
  forall x : R, (P x -> g x <= 0)%R.

Definition Rcst_sign (g : R -> R) :=
  Rpos_over g \/ Rneg_over g.

Lemma eq_Rcst_sign (f g : R -> R) :
  f =1 g -> Rcst_sign f -> Rcst_sign g.
Proof.
move=> H; rewrite /Rcst_sign /Rpos_over /Rneg_over.
by case=> Hf; [left|right] => x Hx; rewrite -H; apply: Hf.
Qed.

Lemma eq'_Rcst_sign (f g : R -> R) :
  (forall x, P x -> f x = g x) ->
  Rcst_sign f -> Rcst_sign g.
Proof.
move=> H; rewrite /Rcst_sign /Rpos_over /Rneg_over.
by case=> Hf; [left|right] => x Hx; rewrite -H //; apply: Hf.
Qed.

Definition Rderive_over (f f' : R -> R) :=
  forall x : R, P x -> is_derive f x (f' x).

Lemma Rderive_pos_imp_incr (f f' : R -> R) :
  connected P -> Rderive_over f f' -> Rpos_over f' -> Rincr f.
Proof.
rewrite /Rpos_over /Rincr.
move=> Hco Hder H0 x y Hx Hy Hxy; rewrite //=.
eapply (derivable_pos_imp_increasing f f' P) =>//.
move=> r Hr.
move/(_ _ Hr) in Hder.
move/(_ _ Hr) in H0.
split; last by auto with real.
exact/is_derive_Reals.
Qed.

Lemma Rderive_neg_imp_decr (f f' : R -> R) :
  connected P -> Rderive_over f f' -> Rneg_over f' -> Rdecr f.
Proof.
rewrite /Rneg_over /Rdecr.
move=> Hco Hder H0 x y Hx Hy Hxy; rewrite //=.
eapply (derivable_neg_imp_decreasing f f' P) =>//.
move=> r Hr.
move/(_ _ Hr) in Hder.
move/(_ _ Hr) in H0.
split; last by auto with real.
exact/is_derive_Reals.
Qed.

Lemma Rderive_cst_sign (f f' : R -> R) :
  connected P -> Rderive_over f f' -> Rcst_sign f' -> Rmonot f.
Proof.
move=> Hco Hder [H|H].
left; exact: Rderive_pos_imp_incr H.
right; exact: Rderive_neg_imp_decr H.
Qed.

End PredArg.

(********************************************************************)
(** Instantiation of [taylor_thm.Cor_Taylor_Lagrange] for intervals *)
(********************************************************************)

Section NDerive.
Variable xf : ExtendedR -> ExtendedR.
Let f := toR_fun xf.
Let Dn := Derive_n f.
Variable X : interval.
Variable n : nat.
Let dom r := contains X (Xreal r).
Let Hdom : connected dom. Proof (contains_connected _).
Let def r := defined xf r.
Hypothesis Hdef : forall r, dom r -> def r.
Hypothesis Hder : forall n r, dom r -> ex_derive_n f n r.

Theorem ITaylor_Lagrange x0 x :
  dom x0 ->
  dom x ->
  exists xi : R,
  dom xi /\
  (f x - \big[Rplus/0%R]_(0 <= i < n.+1)
          (Dn i x0 / INR (fact i) * (x - x0)^i))%R =
  (Dn n.+1 xi / INR (fact n.+1) * (x - x0) ^ n.+1)%R /\
  (x <= xi <= x0 \/ x0 <= xi <= x)%R.
Proof.
move=> Hx0 Hx.
case (Req_dec x0 x)=> [->|Hneq].
  exists x; split =>//=; split; last by auto with real.
  rewrite (Rminus_diag_eq x) // Rmult_0_l Rmult_0_r.
  rewrite big_nat_recl // pow_O big1 /Dn /=; try field.
  by move=> i _; rewrite Rmult_0_l Rmult_0_r.
have Hlim x1 x2 : (x1 < x2)%Re -> dom x1 -> dom x2 ->
  forall (k : nat) (r1 : R), (k <= n)%coq_nat ->
  (fun r2 : R => x1 <= r2 <= x2)%Re r1 ->
  derivable_pt_lim (Dn k) r1 (Dn (S k) r1).
  move=> Hx12 Hdom1 Hdom2 k y Hk Hy.
  have Hdy: (dom y) by move: Hdom; rewrite /connected; move/(_ x1 x2); apply.
  by apply/is_derive_Reals/Derive_correct; apply: (Hder k.+1 Hdy).
destruct (total_order_T x0 x) as [[H1|H2]|H3]; last 2 first.
    by case: Hneq.
  have H0 : (x <= x0 <= x0)%Re by auto with real.
  have H : (x <= x <= x0)%Re by auto with real.
  case: (Cor_Taylor_Lagrange x x0 n (fun n r => (Dn n r))
    (Hlim _ _ (Rgt_lt _ _ H3) Hx Hx0) x0 x H0 H) => [c [Hc Hc1]].
  exists c.
  have Hdc : dom c.
    move: Hdom; rewrite /connected; move/(_ x x0); apply=>//.
    by case: (Hc1 Hneq)=> [J|K]; auto with real; psatzl R.
  split=>//; split; last by case:(Hc1 Hneq);rewrite /=; [right|left]; intuition.
  rewrite sum_f_to_big in Hc.
  exact: Hc.
have H0 : (x0 <= x0 <= x)%Re by auto with real.
have H : (x0 <= x <= x)%Re by auto with real.
case: (Cor_Taylor_Lagrange x0 x n (fun n r => Dn n r)
  (Hlim _ _ (Rgt_lt _ _ H1) Hx0 Hx) x0 x H0 H) => [c [Hc Hc1]].
exists c.
have Hdc : dom c.
  move: Hdom; rewrite /connected; move/(_ x0 x); apply=>//.
  by case: (Hc1 Hneq)=> [J|K]; auto with real; psatzl R.
split=>//; split; last by case:(Hc1 Hneq);rewrite /=; [right|left]; intuition.
rewrite sum_f_to_big in Hc.
exact: Hc.
Qed.

End NDerive.

(******************************************************************************)
(** The sequel of the file is parameterized by an implementation of intervals *)
(******************************************************************************)

Module IntervalAux (I : IntervalOps).

Local Notation Ibnd2 x := (I.bnd x x) (only parsing).

Definition eqNai X := match I.convert X with
                      | IInan => true
                      | _ => false
                      end.

Fact eqNaiP X : reflect (I.convert X = IInan) (eqNai X).
Proof. by apply: introP; rewrite /eqNai; case: (I.convert X). Qed.

Lemma bounded_singleton_contains_lower_upper (X : I.type) :
  I.bounded X = true ->
  contains (I.convert (Ibnd2 (I.lower X))) (I.convert_bound (I.lower X)) /\
  contains (I.convert (Ibnd2 (I.upper X))) (I.convert_bound (I.upper X)).
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [H1a H1b] := I.lower_bounded_correct X H1.
have [H2a H2b] := I.upper_bounded_correct X H2.
by rewrite !I.bnd_correct /contains H1a H2a; psatzl R.
Qed.

(** The following predicate will be used by [Ztech]. *)
Definition isNNegOrNPos (X : I.type) : bool :=
  if I.sign_large X is Xund then false else true.

Lemma isNNegOrNPos_false (X : I.type) :
  I.convert X = IInan -> isNNegOrNPos X = false.
Proof.
move=> H; rewrite /isNNegOrNPos; have := I.sign_large_correct X.
by case: I.sign_large =>//; rewrite H; move/(_ Xnan I) =>//; case.
Qed.

Lemma bounded_IInan (X : I.type) :
  I.bounded X = true -> I.convert X <> IInan.
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [] := I.lower_bounded_correct X H1.
by rewrite /I.bounded_prop; case I.convert.
Qed.

Lemma bounded_IIbnd (X : I.type) :
  I.bounded X = true -> I.convert X =
  IIbnd (I.convert_bound (I.lower X)) (I.convert_bound (I.upper X)).
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [] := I.lower_bounded_correct X H1.
by rewrite /I.bounded_prop; case I.convert.
Qed.

Lemma bounded_Ilower (X : I.type) :
  I.bounded X = true -> I.convert_bound (I.lower X) =
  Xreal (proj_val (I.convert_bound (I.lower X))).
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [] := I.lower_bounded_correct X H1.
by rewrite /I.bounded_prop; case I.convert.
Qed.

Lemma bounded_Iupper (X : I.type) :
  I.bounded X = true -> I.convert_bound (I.upper X) =
  Xreal (proj_val (I.convert_bound (I.upper X))).
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
have [] := I.upper_bounded_correct X H2.
by rewrite /I.bounded_prop; case I.convert.
Qed.

(* Weaken the hyp in lemmas below ? *)
Lemma bounded_lower_Xnan (X : I.type) :
  I.bounded X = true -> I.convert_bound (I.lower X) <> Xnan.
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
by have [-> _] := I.lower_bounded_correct X H1.
Qed.

Lemma bounded_upper_Xnan (X : I.type) :
  I.bounded X = true -> I.convert_bound (I.upper X) <> Xnan.
Proof.
move=> HX.
have [H1 H2] := I.bounded_correct X HX.
by have [-> _] := I.upper_bounded_correct X H2.
Qed.

Lemma bounded_contains_lower (x : ExtendedR) (X : I.type) :
  I.bounded X = true -> contains (I.convert X) x ->
  contains (I.convert X) (Xreal (proj_val (I.convert_bound (I.lower X)))).
Proof.
move=> HX Hx.
have [H1 H2] := I.bounded_correct X HX.
have [H3 H4] := I.lower_bounded_correct X H1.
move: H4 Hx; rewrite /I.bounded_prop =>->.
rewrite -H3 /contains H3.
by case Er : x =>[//|r]; case Es: (I.convert_bound (I.upper X))=>[|s]; lra.
Qed.

(* Erik: May also prove lower/upper-related lemmas involving subset *)

Lemma bounded_contains_upper (X : I.type) (x : ExtendedR) :
  I.bounded X = true -> contains (I.convert X) x ->
  contains (I.convert X) (Xreal (proj_val (I.convert_bound (I.upper X)))).
Proof.
move=> HX Hx.
have [H1 H2] := I.bounded_correct X HX.
have [H3 H4] := I.upper_bounded_correct X H2.
move: H4 Hx; rewrite /I.bounded_prop =>->.
rewrite -H3 /contains H3.
by case Er : x =>[//|r]; case Es : (I.convert_bound (I.lower X)) =>[|s]; lra.
Qed.

Definition ge0 xi : bool :=
  if I.sign_large xi is Xgt then true else false.

Definition le0 xi : bool :=
  if I.sign_large xi is Xlt then true else false.

Definition gt0 xi : bool :=
  if I.sign_strict xi is Xgt then true else false.

Definition lt0 xi : bool :=
  if I.sign_strict xi is Xlt then true else false.

Definition neq0 xi : bool :=
  match I.sign_strict xi with
  | Xlt | Xgt => true
  | _ => false
  end.

Lemma ge0_correct X x :
  contains (I.convert X) (Xreal x) -> ge0 X -> (0 <= x)%R.
Proof.
move=> Hx; rewrite /ge0; have := I.sign_large_correct X; case: I.sign_large=>//.
by case/(_ _ Hx) =>/=.
Qed.

Lemma le0_correct X x :
  contains (I.convert X) (Xreal x) -> le0 X -> (x <= 0)%R.
Proof.
move=> Hx; rewrite /le0; have := I.sign_large_correct X; case: I.sign_large=>//.
by case/(_ _ Hx) =>/=.
Qed.

Lemma gt0_correct X x :
  contains (I.convert X) (Xreal x) -> gt0 X -> (0 < x)%R.
Proof.
move=> Hx; rewrite /gt0.
have := I.sign_strict_correct X; case: I.sign_strict=>//.
by case/(_ _ Hx) =>/=.
Qed.

Lemma lt0_correct X x :
  contains (I.convert X) (Xreal x) -> lt0 X -> (x < 0)%R.
Proof.
move=> Hx; rewrite /lt0.
have := I.sign_strict_correct X; case: I.sign_strict=>//.
by case/(_ _ Hx) =>/=.
Qed.

Lemma neq0_correct X x :
  contains (I.convert X) (Xreal x) -> neq0 X -> (x <> 0)%R.
Proof.
move=> Hx; rewrite /neq0.
have := I.sign_strict_correct X; case: I.sign_strict=>//;
  by case/(_ _ Hx) =>/=; auto with real.
Qed.

Lemma intvlP X :
  I.bounded X = true ->
  forall x,
  (contains (I.convert X) (Xreal x) <->
   intvl (proj_val (I.convert_bound (I.lower X)))
         (proj_val (I.convert_bound (I.upper X))) x).
Proof.
move=> HX x.
split.
- rewrite bounded_IIbnd // => H.
  by rewrite bounded_Ilower // bounded_Iupper in H.
- move=> H; rewrite bounded_IIbnd //.
  by rewrite bounded_Ilower // bounded_Iupper.
Qed.

Lemma Ilower_bnd (l u : I.bound_type) :
  I.convert_bound (I.lower (I.bnd l u)) = I.convert_bound l.
Proof. by rewrite I.lower_correct I.bnd_correct. Qed.

Lemma Iupper_bnd (l u : I.bound_type) :
  I.convert_bound (I.upper (I.bnd l u)) = I.convert_bound u.
Proof. by rewrite I.upper_correct I.bnd_correct. Qed.

Lemma Iupper_Xreal (X : I.type) (r : R) :
  I.convert_bound (I.upper X) = Xreal r -> I.convert X <> IInan.
Proof. by rewrite I.upper_correct; case: (I.convert X). Qed.

Lemma Ilower_Xreal (X : I.type) (r : R) :
  I.convert_bound (I.lower X) = Xreal r -> I.convert X <> IInan.
Proof. by rewrite I.lower_correct; case: (I.convert X). Qed.

Lemma upper_le (X : I.type) (x : ExtendedR (*sic*)) :
  contains (I.convert X) x -> le_upper x (I.convert_bound (I.upper X)).
Proof.
rewrite /le_upper; case E : I.convert_bound => [//|r] H.
have E' := Iupper_Xreal E.
case: x H => [|r'] H.
  by apply: E'; apply -> contains_Xnan.
case E2: (I.convert X) E' =>[//|l u] _.
rewrite E2 in H.
rewrite I.upper_correct E2 /= in E.
by move: H; rewrite /contains; case=> _; rewrite E.
Qed.

Lemma lower_le (X : I.type) (x : ExtendedR (*sic*)) :
  contains (I.convert X) x -> le_lower (I.convert_bound (I.lower X)) x.
Proof.
rewrite /le_lower; case E : I.convert_bound => [//|r] H.
have E' := Ilower_Xreal E.
case: x H => [|r'] H.
  by apply: E'; apply -> contains_Xnan.
case E2: (I.convert X) E' =>[//|l u] _.
rewrite E2 in H.
rewrite I.lower_correct E2 /= in E.
move: H; rewrite /contains; case=> H _; rewrite E in H.
by simpl; psatzl R.
Qed.

Lemma contains_lower_or_upper_Xreal (X : I.type) (xi0 : ExtendedR) (r : R) :
  contains (I.convert X) (Xreal r) -> contains (I.convert X) xi0 ->
  contains (IIbnd (I.convert_bound (I.lower X)) xi0) (Xreal r) \/
  contains (IIbnd xi0 (I.convert_bound (I.upper X))) (Xreal r).
Proof.
set x := Xreal r => Hx Hxi0.
have HL0 := lower_le Hx.
have HU0 := upper_le Hx.
have [HL|HL] := le_lower_or x xi0; have [HU|HU] := le_upper_or x xi0.
- by left; apply: le_contains.
- rewrite /le_lower in HL.
  rewrite /le_upper /= in HU HL.
  case E : xi0 Hxi0 HU HL =>[//|s /=].
  move=> Hs rs1 rs2.
  case L: (I.convert_bound (I.lower X)) => [|l];
    case U: (I.convert_bound (I.upper X)) => [|u];
    have H := contains_lower_le_upper Hx;
    intuition.
  by rewrite -I.lower_correct -I.upper_correct L U in H; psatzl R.
- by left; apply: le_contains.
by right; apply: le_contains.
Qed.

Lemma contains_lower_or_upper (X : I.type) (xi0 : ExtendedR) (x : ExtendedR) :
  I.convert X <> IInan ->
  contains (I.convert X) x -> contains (I.convert X) xi0 ->
  contains (IIbnd (I.convert_bound (I.lower X)) xi0) x \/
  contains (IIbnd xi0 (I.convert_bound (I.upper X))) x.
Proof.
move=> HX Hx Hxi0.
case: x Hx; first by move/contains_Xnan.
move=> r Hr; exact: contains_lower_or_upper_Xreal.
Qed.

(*******************************************************)
(** Support results about [I.midpoint] and [not_empty] *)
(*******************************************************)

Definition Imid i : I.type := I.bnd (I.midpoint i) (I.midpoint i).

Lemma not_empty_Imid (X : I.type) :
  not_empty (I.convert X) -> not_empty (I.convert (Imid X)).
Proof.
case=>[v Hv].
rewrite /Imid I.bnd_correct.
apply: not_emptyE.
exists (I.convert_bound (I.midpoint X)).
red.
have e : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> _] := I.midpoint_correct X e.
by auto with real.
Qed.

Lemma Imid_subset (X : I.type) :
  not_empty (I.convert X) ->
  I.subset_ (I.convert (Imid X)) (I.convert X).
Proof.
case=>[v Hv].
rewrite /Imid I.bnd_correct.
have HX : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> Hreal] := I.midpoint_correct X HX.
case E: I.convert =>[//|l u].
split.
- have := lower_le Hreal.
  have->: l = Xlower (I.convert X) by rewrite E.
  by rewrite I.lower_correct.
- have := upper_le Hreal.
  have->: u = Xupper (I.convert X) by rewrite E.
  by rewrite I.upper_correct.
Qed.

Lemma Imid_contains (X : I.type) :
  not_empty (I.convert X) ->
  contains (I.convert (Imid X)) (I.convert_bound (I.midpoint X)).
Proof.
move=>[v Hv].
rewrite /Imid I.bnd_correct.
have HX : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> Hreal] := I.midpoint_correct X HX.
by red; auto with real.
Qed.

Lemma Xreal_Imid_contains (X : I.type) :
  not_empty (I.convert X) ->
  contains (I.convert (Imid X)) (Xreal (proj_val (I.convert_bound (I.midpoint X)))).
Proof.
move=>[v Hv].
rewrite /Imid I.bnd_correct.
have HX : exists x : ExtendedR, contains (I.convert X) x by exists (Xreal v).
have [-> Hreal] := I.midpoint_correct X HX.
by red; auto with real.
Qed.

(******************************************************************************)
(** Correctness predicates dealing with reals only, weaker than [I.extension] *)
(******************************************************************************)

Definition R_extension f fi :=
  forall (b : I.type) (x : R),
    contains (I.convert b) (Xreal x) ->
    contains (I.convert (fi b))
             (Xreal (f x)).

Definition R_extension_2 f fi :=
  forall (ix iy : I.type) (x y : R),
    contains (I.convert ix) (Xreal x) ->
    contains (I.convert iy) (Xreal y) ->
    contains (I.convert (fi ix iy)) (Xreal (f x y)).

Lemma R_div_correct (prec : I.precision) :
  R_extension_2 Rdiv (I.div prec).
Proof.
move=> ix iy x y Hx Hy.
case: (is_zero_spec y) (Hy) => H; last first.
  rewrite Xreal_div //.
  exact: I.div_correct.
suff->: I.convert (I.div prec ix iy) = IInan by [].
apply contains_Xnan.
have->: Xnan = (Xdiv (Xreal x) (Xreal 0)) by simpl; rewrite zeroT.
apply: I.div_correct =>//.
by rewrite -H.
Qed.

Lemma R_neg_correct : R_extension Ropp I.neg.
Proof. move=> *; rewrite Xreal_neg; exact: I.neg_correct. Qed.

Lemma R_sub_correct prec : R_extension_2 Rminus (I.sub prec).
Proof. move=> *; rewrite Xreal_sub; exact: I.sub_correct. Qed.

Lemma R_add_correct prec : R_extension_2 Rplus (I.add prec).
Proof. move=> *; rewrite Xreal_add; exact: I.add_correct. Qed.

Lemma R_mul_correct prec : R_extension_2 Rmult (I.mul prec).
Proof. move=> *; rewrite Xreal_mul; exact: I.mul_correct. Qed.

Lemma R_sqr_correct prec : R_extension Rsqr (I.sqr prec).
Proof. move=> *; rewrite Xreal_sqr; exact: I.sqr_correct. Qed.

Lemma R_power_int_correct prec (n : Z) :
  R_extension (powerRZ ^~ n) (I.power_int prec ^~ n).
Proof.
move=> ix x Hx.
case: (is_zero_spec x) (Hx) => H; last first.
  rewrite Xreal_power_int //; last by left.
  exact: I.power_int_correct.
case: (Z_lt_le_dec n 0) => Hn.
  suff->: I.convert (I.power_int prec ix n) = IInan by [].
  apply contains_Xnan.
  suff->: Xnan = (Xpower_int (Xreal x) n) by exact: I.power_int_correct.
  by simpl; case: n Hn =>//; rewrite zeroT.
rewrite Xreal_power_int; last by right; auto with zarith.
exact: I.power_int_correct.
Qed.

Lemma R_from_nat_correct :
  forall (b : I.type) (n : nat),
  contains (I.convert (I.fromZ (Z.of_nat n)))
           (Xreal (INR n)).
Proof. move=> b n; rewrite INR_Z2R; exact: I.fromZ_correct. Qed.

Lemma R_inv_correct : forall prec, R_extension Rinv (I.inv prec).
Proof.
move=> prec ix x Hx.
case: (is_zero_spec x) => H; last first.
  rewrite Xreal_inv //.
  exact: I.inv_correct.
suff->: I.convert (I.inv prec ix) = IInan by [].
apply/contains_Xnan.
have->: Xnan = (Xinv (Xreal x)) by simpl; rewrite zeroT.
exact: I.inv_correct.
Qed.

Lemma R_abs_correct : R_extension Rabs I.abs.
Proof. move=> *; rewrite Xreal_abs; exact: I.abs_correct. Qed.

Lemma R_sqrt_correct : forall prec, R_extension sqrt (I.sqrt prec).
move=> prec ix x Hx.
case: (is_negative_spec x) => H; last first.
  rewrite Xreal_sqrt //.
  exact: I.sqrt_correct.
suff->: I.convert (I.sqrt prec ix) = IInan by [].
apply/contains_Xnan.
have->: Xnan = (Xsqrt (Xreal x)) by simpl; rewrite negativeT.
exact: I.sqrt_correct.
Qed.

Lemma R_cos_correct : forall prec, R_extension cos (I.cos prec).
Proof. red=> *; rewrite Xreal_cos; exact: I.cos_correct. Qed.

Lemma R_sin_correct : forall prec, R_extension sin (I.sin prec).
Proof. red=> *; rewrite Xreal_sin; exact: I.sin_correct. Qed.

Lemma R_tan_correct : forall prec, R_extension tan (I.tan prec).
move=> prec ix x Hx.
case: (is_zero_spec (cos x)) => H; last first.
  rewrite Xreal_tan //.
  exact: I.tan_correct.
suff->: I.convert (I.tan prec ix) = IInan by [].
apply/contains_Xnan.
have->: Xnan = (Xtan (Xreal x)) by rewrite /Xtan /= zeroT.
exact: I.tan_correct.
Qed.

Lemma R_atan_correct : forall prec, R_extension atan (I.atan prec).
Proof. red=> *; rewrite Xreal_atan; exact: I.atan_correct. Qed.

Lemma R_exp_correct : forall prec, R_extension exp (I.exp prec).
Proof. red=> *; rewrite Xreal_exp; exact: I.exp_correct. Qed.

Lemma R_ln_correct : forall prec, R_extension ln (I.ln prec).
move=> prec ix x Hx.
case: (is_positive_spec x) => H.
  rewrite Xreal_ln //.
  exact: I.ln_correct.
suff->: I.convert (I.ln prec ix) = IInan by [].
apply/contains_Xnan.
have->: Xnan = (Xln (Xreal x)) by simpl; rewrite positiveF.
exact: I.ln_correct.
Qed.

Lemma R_mask_correct : R_extension_2 (fun c x => c) I.mask.
Proof.
move=> ci xi c x Hc Hx /=.
change (Xreal c) with (Xmask (Xreal c) (Xreal x)).
exact: I.mask_correct.
Qed.

Arguments R_mask_correct [ix iy x] y _ _.
(*
Definition I_propagate fi :=
  forall b : I.type,
  contains (I.convert b) Xnan -> contains (I.convert (fi b)) Xnan.
*)

Lemma extension_propagate (f : R -> R) fi fx :
  extension f fx -> I.extension fx fi -> I.propagate fi.
Proof.
move=> Hfx Hfi x /contains_Xnan Hx.
apply/contains_Xnan.
suff->: Xnan = fx Xnan by exact: Hfi.
by move: (Hfx Xnan); case: (fx).
Qed.

Lemma extension_I2R f fi fx :
  extension f fx -> I.extension fx fi -> R_extension f fi.
Proof.
move=> Hfx Hfi X x Hx.
case Df: (defined fx x).
suff->: Xreal (f x) = fx (Xreal x) by exact: Hfi.
move: (Hfx (Xreal x)) Df; rewrite /defined.
by case: (fx) =>[//|r Hr _]; rewrite Hr.
move/definedPf in Df.
rewrite (iffLR (contains_Xnan (I.convert (fi X)))) //.
rewrite -Df.
exact: Hfi.
Qed.

Lemma extension_R2I f fi fx :
  extension f fx -> R_extension f fi -> I.propagate fi ->
  (forall x, defined fx x) ->
  I.extension fx fi.
Proof.
move=> Hfx Hfi Hp Dfx X x Hx.
case: x Hx => [|x] Hx.
  move/contains_Xnan in Hx.
  by rewrite Hp.
suff->: fx (Xreal x) = Xreal (f x) by exact: Hfi.
move: (Hfx (Xreal x)) (Dfx x); rewrite /defined.
by case: (fx) =>[//|r Hr]; rewrite Hr.
Qed.

Lemma cont0 : contains (I.convert I.zero) (Xreal 0).
Proof. by rewrite I.zero_correct //=; split; exact: Rle_refl. Qed.

Lemma only0 v : contains (I.convert I.zero) (Xreal v) -> v = 0%R.
Proof. by rewrite I.zero_correct; case; symmetry; apply Rle_antisym. Qed.

Section PrecArgument.

Variable prec : I.precision.

Lemma mul_0_contains_0_l y Y X :
  contains (I.convert Y) y ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.mul prec X Y)) (Xreal 0).
Proof.
move=> Hy H0.
have H0y ry : (Xreal 0) = (Xreal 0 * Xreal ry)%XR by rewrite /= Rmult_0_l.
case: y Hy => [|ry] Hy; [rewrite (H0y 0%R)|rewrite (H0y ry)];
  apply: I.mul_correct =>//.
by case ->: (I.convert Y) Hy.
Qed.

Lemma mul_0_contains_0_r y Y X :
  contains (I.convert Y) y ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.mul prec Y X)) (Xreal 0).
Proof.
move=> Hy H0.
have Hy0 ry : (Xreal 0) = (Xreal ry * Xreal 0)%XR by rewrite /= Rmult_0_r.
case: y Hy => [|ry] Hy; [rewrite (Hy0 0%R)|rewrite (Hy0 ry)];
  apply: I.mul_correct=>//.
by case: (I.convert Y) Hy.
Qed.

Lemma pow_contains_0 (X : I.type) (n : Z) :
  (n > 0)%Z ->
  contains (I.convert X) (Xreal 0) ->
  contains (I.convert (I.power_int prec X n)) (Xreal 0).
Proof.
move=> Hn HX.
rewrite (_: (Xreal 0) = (Xpower_int (Xreal 0) n)); first exact: I.power_int_correct.
case: n Hn =>//= p Hp; rewrite pow_ne_zero //.
by zify; auto with zarith.
Qed.

Lemma subset_sub_contains_0 x0 (X0 X : I.type) :
  contains (I.convert X0) x0 ->
  I.subset_ (I.convert X0) (I.convert X) ->
  contains (I.convert (I.sub prec X X0)) (Xreal 0).
Proof.
move=> Hx0 Hsub.
  have H1 : contains (I.convert X) x0.
    exact: (subset_contains (I.convert X0)).
have Hs := I.sub_correct prec X X0 x0 x0 H1 Hx0.
case cx0 : x0 Hs Hx0 => [|rx0].
  by case: (I.convert (I.sub prec X X0)).
rewrite (_: Xreal 0 = Xreal rx0 - Xreal rx0)%XR;
  last by rewrite /= Rminus_diag_eq.
by move=>*; apply: I.sub_correct=>//; apply: (subset_contains (I.convert X0)).
Qed.

Lemma subset_real_contains X rx ry c :
  contains (I.convert X) (Xreal rx) ->
  contains (I.convert X) (Xreal ry) -> (rx <= c <= ry)%Re ->
  contains (I.convert X) (Xreal c).
Proof.
case CX : (I.convert X) => [|l u] // => Hrx Hry Hc.
case Cl: l Hc Hrx Hry =>[|rl];
  case Cu : u =>[|ru] // [Hcx Hcy][Hxu0 Hxu][Hyu0 Hyu]; split => //.
  + by apply: (Rle_trans _ ry).
  + by apply: (Rle_trans _ rx).
  by apply: (Rle_trans _ rx).
by apply: (Rle_trans _ ry).
Qed.

Lemma Iadd_zero_subset_l (a b : I.type) :
  (exists t, contains (I.convert a) t) ->
  contains (I.convert b) (Xreal 0) ->
  I.subset_ (I.convert a) (I.convert (I.add prec b a)).
Proof.
move=> Ht Hb0.
apply: contains_subset =>// v Hav.
move: {Hav} (I.add_correct prec b a (Xreal 0) v Hb0 Hav).
by case: v =>// r; rewrite /= Rplus_0_l.
Qed.

Lemma Iadd_zero_subset_r a b :
  (exists t, contains (I.convert a) t) ->
  contains (I.convert b) (Xreal 0) ->
  I.subset_ (I.convert a) (I.convert (I.add prec a b)).
Proof.
move=> Ht Hb0; apply: contains_subset =>// v Hav.
move: {Hav} (I.add_correct prec a b v (Xreal 0) Hav Hb0).
by case:v =>// r; rewrite /= Rplus_0_r.
Qed.

Lemma Iadd_Isub_aux b a B D :
  contains (I.convert B) b ->
  contains (I.convert D) (a - b)%XR ->
  contains (I.convert (I.add prec B D)) a.
Proof.
move=> Hb Hd.
case cb : b Hb=> [|rb].
  move=> Hb; rewrite I.add_propagate_l => //=.
  by case: (I.convert B) Hb.
rewrite -cb => Hb; rewrite (_ : a = b + (a - b))%XR.
  by apply: I.add_correct.
rewrite cb; case: a Hd => //= r _.
by congr Xreal; ring.
Qed.

End PrecArgument.
End IntervalAux.
