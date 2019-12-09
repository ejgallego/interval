(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2013-2016, Inria

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

From Coq Require Import Reals ZArith Psatz.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop.

Require Import Interval.
Require Import Xreal.
Require Import Basic.
Require Import Interval_compl.
Require Import Datatypes.
Require Import Taylor_model_sharp.
Require Import Bound.
Require Import Bound_quad.
Require Import Univariate_sig.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Auxiliary lemmas on natural numbers *)

Local Open Scope nat_scope.

Lemma maxnS (m n : nat) : 0 < maxn m n.+1.
Proof. by case: m =>[//|m]; rewrite maxnSS. Qed.

Lemma maxSn (m n : nat) : 0 < maxn m.+1 n.
Proof. by rewrite maxnC maxnS. Qed.

(** * Parameterized Module for Taylor Models *)

Module TM (I : IntervalOps) <: UnivariateApprox I.
(* Erik: We might add a Boolean counterpart of not_empty in IntervalOps *)

(** ** Load the CoqApprox modules *)
Module Pol := SeqPolyInt I.
Module Bnd := PolyBoundHornerQuad I Pol.
Module Import TMI := TaylorModel I Pol Bnd.

(** ** Main type definitions *)

Inductive t_ := Const of I.type | Var | Tm of rpa.

Definition T := t_.

Definition U := (I.precision * nat)%type.

Definition i1 := I.fromZ_small 1.
Definition i2 := I.fromZ_small 2.
Definition im1 := I.fromZ_small (-1).

(** ** Auxiliary material *)

Definition tmsize (tm : rpa) := Pol.size (approx tm).

Definition tsize (t : T) : nat :=
  match t with
    | Const _ => 1
    | Var => 2
    | Tm tm => tmsize tm
  end.

Definition get_tm (u : U) X (t : T) : rpa :=
  match t with
    | Const c => TM_cst X c
    | Var => let X0 := Imid X in (TM_var X X0)
    | Tm tm => tm (* ignore u, X in this branch *)
  end.

Lemma size_get_tm u X t :
  tmsize (get_tm u X t) = tsize t.
Proof. by case: t. Qed.

(** ** Define the main validity predicate *)

Definition approximates (X : I.type) (tf : T) (f : R -> ExtendedR) : Prop :=
  match tf with
  | Const c => I.convert c = Inan \/ is_const f (I.convert X) (I.convert c)
  | Var =>
    forall x : R, contains (I.convert X) (Xreal x) -> f x = Xreal x
  | Tm tm =>
    not_empty (I.convert X) ->
    let x0 := proj_val (I.convert_bound (I.midpoint X)) in
    i_validTM x0 (I.convert X) tm f
  end.

Theorem approximates_ext f g xi t :
  (forall x, f x = g x) ->
  approximates xi t f -> approximates xi t g.
Proof.
move=> Hfg Hmain.
case: t Hmain =>[c| |tm] Hmain.
destruct Hmain as [H|Hmain].
now left.
right.
exact: is_const_ext_weak Hmain.
by move=> *; rewrite -Hfg; apply: Hmain.
move=> Hne; move/(_ Hne): Hmain.
exact: TM_fun_eq.
Qed.

Lemma contains_midpoint :
  forall X : I.type,
  not_empty (I.convert X) ->
  contains (I.convert X) (Xreal (proj_val (I.convert_bound (I.midpoint X)))).
Proof.
intros X [x Hx].
unfold Imid.
destruct (I.midpoint_correct X) as [H1 H2].
  now exists (Xreal x).
now rewrite <- H1.
Qed.

Lemma get_tm_correct u Y tf f :
  approximates Y tf f ->
  approximates Y (Tm (get_tm u Y tf)) f.
Proof.
case: tf =>[c||tm]; rewrite /approximates // => H Hne.
- destruct H as [H|H].
    split ; intros ; rewrite ?I.mask_propagate_r //.
    exact: contains_midpoint.
    exists (PolR.polyC 0).
    now apply Pol.polyC_correct ; rewrite H.
    easy.
  apply TM_cst_correct_strong =>//.
  exact: contains_midpoint.
- apply: TM_var_correct_strong=>//.
    exact: Imid_subset.
  exact: Xreal_Imid_contains.
Qed.

(** ** Main definitions and correctness claims *)

Definition const : I.type -> T := Const.

Theorem const_correct (c : I.type) (r : R) :
  contains (I.convert c) (Xreal r) ->
  forall (X : I.type),
  approximates X (const c) (fun _ => Xreal r).
Proof.
move=> Hcr X.
right.
now exists (Xreal r).
Qed.

Definition dummy : T := Const I.nai.

Theorem dummy_correct xi f :
  TM.approximates xi dummy f.
Proof.
left.
apply I.nai_correct.
Qed.

Definition var : T := Var.

Theorem var_correct (X : I.type) :
  approximates X var Xreal.
Proof. done. Qed.

Definition eval (u : U) (t : T) (Y X : I.type) : I.type :=
  if I.subset X Y then
  match t with
  | Const c => I.mask c X (* the need for I.mask comes from I.extension below *)
  | Var => X
  | Tm tm =>
    let X0 := Imid Y in
    let tm := get_tm u Y t in
    I.add u.1
      (Bnd.ComputeBound u.1 (approx tm) (I.sub u.1 X X0))
      (error tm)
  end
  else I.nai.

Theorem eval_correct u (Y : I.type) tf f :
  approximates Y tf f -> I.extension (Xbind f) (eval u tf Y).
Proof.
move=> Hf X x Hx.
rewrite /eval.
case HXY: I.subset; last by rewrite I.nai_correct.
move/I.subset_correct: (HXY) => Hsubset.
case: tf Hf => [c| |tm].
(* Const *)
case=> [H|[y Hy1 /= Hy2]].
now rewrite I.mask_propagate_l.
case: x Hx =>[|x] Hx /=.
  now apply contains_Xnan, I.mask_propagate_r, contains_Xnan.
apply I.mask_correct'.
rewrite Hy2 //.
exact: subset_contains Hx.
(* Var *)
case: x Hx => [|x] Hx //= -> //.
exact: subset_contains Hsubset _ _.
(* Tm *)
move=> Hf.
have /= {Hf} := get_tm_correct u Hf=> Htm.
have HneY: not_empty (I.convert Y).
apply: not_emptyE.
exists x; exact: subset_contains Hsubset _ _.
move/(_ HneY): Htm.
case => [Hdef Hnai Hzero _ Hmain].
have [L1 L2] := I.midpoint_correct Y (not_empty'E HneY).
set c0 := proj_val (I.convert_bound (I.midpoint Y)) in L1.
have Hc0 : contains (I.convert (Imid Y)) (Xreal c0).
  apply: Xreal_Imid_contains.
  apply: not_emptyE; exists x.
  apply: subset_contains Hx.
  exact: I.subset_correct.
have [qx Hcont Hdelta] := Hmain.
move: x Hx => [|x Hx] /=.
  move/contains_Xnan => H0.
  rewrite I.add_propagate_l //. (* does not depend on Hzero anymore *)
  apply: Bnd.ComputeBound_propagate.
  by rewrite I.sub_propagate_l.
move/(_ x) in Hdelta.
have->: f x = Xadd (Xreal (PolR.horner tt qx (Rminus x c0)))
  (Xsub (f x) (Xreal (PolR.horner tt qx (Rminus x c0)))).
case Efx : (f x) => [|r]; first by rewrite Xadd_comm.
simpl.
by congr Xreal; ring.
apply I.add_correct =>//.
  apply: Bnd.ComputeBound_correct =>//.
  exact: J.sub_correct.
case Efx: (f x) => [|fx].
apply/contains_Xnan.
apply: Hdef Efx.
exact: (subset_contains _ _ Hsubset).
rewrite Efx in Hdelta.
apply: Hdelta.
exact: (subset_contains _ _ Hsubset).
Qed.

Definition add_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let M1 := get_tm u X t1 in
  let M2 := get_tm u X t2 in
  Tm (TM_add u.1 M1 M2).

Definition add (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Const c1, Const c2 => Const (I.add u.1 c1 c2)
    | _, _ => add_slow u X t1 t2
  end.

Lemma add_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (add_slow u Y tf tg) (fun x => Xadd (f x) (g x)).
Proof.
intros Hf Hg Hne.
now apply TM_add_correct ; apply get_tm_correct.
Qed.

Theorem add_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (add u Y tf tg) (fun x => Xadd (f x) (g x)).
Proof.
move: tf tg => [cf| |tf] [cg| |tg] Hf Hg;
  try exact: add_slow_correct.
case: Hf => [Hf|[yf Hyf1 /= Hyf2]].
left.
now apply I.add_propagate_l.
case: Hg => [Hg|[yg Hyg1 /= Hyg2]].
left.
now apply I.add_propagate_r.
right.
exists (Xadd yf yg); first exact: I.add_correct.
by move=> x Hx; rewrite /= Hyf2 // Hyg2.
Qed.

Definition opp_slow (u : U) (X : I.type) (t : T) : T :=
  Tm (TM_opp (get_tm u X t)).

Definition opp (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Const c => Const (I.neg c)
    | _ => opp_slow u X t
  end.

Lemma opp_slow_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (opp_slow u Y tf) (fun x => Xneg (f x)).
Proof.
intros Hf Hne.
now apply TM_opp_correct ; apply get_tm_correct.
Qed.

Theorem opp_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (opp u Y tf) (fun x => Xneg (f x)).
Proof.
move: tf => [cf| |tf] Hmain; try exact: opp_slow_correct.
destruct Hmain as [H|[y Hy1 Hy2]].
left.
now apply J.neg_propagate.
right.
exists (Xneg y); first exact: I.neg_correct.
by move=> x Hx; rewrite /= Hy2.
Qed.

Definition sub_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let M1 := get_tm u X t1 in
  let M2 := get_tm u X t2 in
  Tm (TM_sub u.1 M1 M2).

Definition sub (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Const c1, Const c2 => Const (I.sub u.1 c1 c2)
  (*| Var, Var => Const I.zero : FIXME *)
    | _, _ => sub_slow u X t1 t2
  end.

Lemma sub_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (sub_slow u Y tf tg) (fun x => Xsub (f x) (g x)).
Proof.
intros Hf Hg Hne.
now apply TM_sub_correct ; apply get_tm_correct.
Qed.

Theorem sub_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (sub u Y tf tg) (fun x => Xsub (f x) (g x)).
Proof.
move: tf tg => [cf| |tf] [cg| |tg] Hf Hg;
  try exact: sub_slow_correct.
case: Hf => [Hf|[yf Hyf1 /= Hyf2]].
left.
now apply I.sub_propagate_l.
case: Hg => [Hg|[yg Hyg1 /= Hyg2]].
left.
now apply I.sub_propagate_r.
right.
exists (Xsub yf yg); first exact: I.sub_correct.
by move=> x Hx; rewrite /= Hyf2 // Hyg2.
Qed.

Definition mul_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let M1 := get_tm u X t1 in
  let M2 := get_tm u X t2 in
  let X0 := Imid X in
  Tm (TM_mul u.1 M1 M2 X0 X u.2).

Definition mul (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Const c1, Const c2 => Const (I.mul u.1 c1 c2)
    | Const c1, _ => Tm (TM_mul_mixed u.1 c1 (get_tm u X t2) )
    | _, Const c2 => Tm (TM_mul_mixed u.1 c2 (get_tm u X t1) )
    | _, _ => mul_slow u X t1 t2
  end.

Lemma mul_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (mul_slow u Y tf tg) (fun x => Xmul (f x) (g x)).
Proof.
intros Hf Hg Hne.
apply TM_mul_correct ; try apply get_tm_correct ; try easy.
exact: Xreal_Imid_contains.
Qed.

Theorem mul_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (mul u Y tf tg) (fun x => Xmul (f x) (g x)).
Proof.
move: tf tg => [cf| |tf] [cg| |tg] Hf Hg;
  try exact: mul_slow_correct.
(* Const . Const *)
case: Hf => [Hf|[yf Hyf1 /= Hyf2]].
  left.
  now apply I.mul_propagate_l.
case: Hg => [Hg|[yg Hyg1 /= Hyg2]].
  left.
  now apply I.mul_propagate_r.
right.
exists (Xmul yf yg); first exact: I.mul_correct.
by move=> x Hx; rewrite /= Hyf2 // Hyg2.
(* Const . Var *)
intros Hne.
destruct Hf as [Hf|Hf].
  apply TM_mul_mixed_nai with (f := g) (1 := Hf).
  now apply get_tm_correct.
apply: TM_mul_mixed_correct_strong =>//.
now apply get_tm_correct.
(* Const . Tm *)
intros Hne.
destruct Hf as [Hf|Hf].
  apply TM_mul_mixed_nai with (f := g) (1 := Hf).
  now apply get_tm_correct.
apply: TM_mul_mixed_correct_strong =>//.
now apply get_tm_correct.
(* Var . Const *)
intros Hne.
apply: (@TM_fun_eq (fun x => Xmul (g x) (f x)) _) =>//.
  by move=> *; exact: Xmul_comm.
destruct Hg as [Hg|Hg].
  apply TM_mul_mixed_nai with (f := f) (1 := Hg).
  now apply get_tm_correct.
apply: TM_mul_mixed_correct_strong =>//.
now apply get_tm_correct.
(* Tm . Const *)
intros Hne.
apply: (@TM_fun_eq (fun x => Xmul (g x) (f x)) _) =>//.
  by move=> *; exact: Xmul_comm.
destruct Hg as [Hg|Hg].
  apply TM_mul_mixed_nai with (f := f) (1 := Hg).
  now apply get_tm_correct.
apply: TM_mul_mixed_correct_strong =>//.
now apply get_tm_correct.
Qed.

Definition div_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let M1 := get_tm u X t1 in
  let M2 := get_tm u X t2 in
  let X0 := Imid X in
  Tm (TM_div u.1 M1 M2 X0 X u.2).

Definition div (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Const c1, Const c2 => Const (I.div u.1 c1 c2)
    | _, Const c2 => Tm (TM_div_mixed_r u.1 (get_tm u X t1) c2)
  (*| Var, Var => Const (I.fromZ 1) : FIXME *)
    | _, _ => div_slow u X t1 t2
  end.

Lemma div_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (div_slow u Y tf tg) (fun x => Xdiv (f x) (g x)).
Proof.
intros Hf Hg Hne.
apply TM_div_correct ; try apply get_tm_correct ; try easy.
exact: Xreal_Imid_contains.
Qed.

Theorem div_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (div u Y tf tg) (fun x => Xdiv (f x) (g x)).
Proof.
move: tf tg => [cf| |tf] [cg| |tg] Hf Hg;
  try exact: div_slow_correct.
(* Const . Const *)
case: Hf => [Hf|[yf Hyf1 /= Hyf2]].
  left.
  now apply I.div_propagate_l.
case: Hg => [Hg|[yg Hyg1 /= Hyg2]].
  left.
  now apply I.div_propagate_r.
right.
exists (Xdiv yf yg); first exact: I.div_correct.
by move=> x Hx; rewrite /= Hyf2 // Hyg2.
(* Var . Const *)
intros Hne.
destruct Hg as [Hg|Hg].
  apply TM_div_mixed_r_nai with (f := f) (1 := Hg).
  now apply get_tm_correct.
apply: TM_div_mixed_r_correct_strong =>//.
apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
exact: Xreal_Imid_contains.
(* Const . Tm *)
intros Hne.
destruct Hg as [Hg|Hg].
  apply TM_div_mixed_r_nai with (f := f) (1 := Hg).
  now apply get_tm_correct.
apply: TM_div_mixed_r_correct_strong =>//.
now apply get_tm_correct.
Qed.

Definition abs (u : U) (X : I.type) (t : T) : T :=
  let e := eval u t X X in
  match I.sign_large e with
  | Xeq | Xgt => t
  | Xlt => opp u X t
  | Xund => Tm (TM_any u.1 (I.abs e) X u.2)
  end.

Lemma Isign_large_Xabs (u : U) (tf : T) (Y X : I.type) f :
  approximates Y tf f ->
  match I.sign_large (eval u tf Y X) with
    | Xeq =>
      forall x, contains (I.convert X) (Xreal x) ->
      f x = Xabs (f x) (* weak but sufficient *)
    | Xgt =>
      forall x, contains (I.convert X) (Xreal x) ->
      f x = Xabs (f x)
    | Xlt =>
      forall x, contains (I.convert X) (Xreal x) ->
      Xneg (f x) = Xabs (f x)
    | Xund => True
  end.
Proof.
intros Hmain.
case: I.sign_large (I.sign_large_correct (eval u tf Y X)) =>//.
- move=> H x Hx.
  rewrite (H (f x)) /= ?Rabs_R0 //.
  exact: eval_correct Hx.
- move=> H x Hx.
  set fx := f x.
  have [|Hfx Hsign] := H fx.
  exact: eval_correct Hx.
  rewrite /Xabs Hfx /=; congr Xreal.
  by rewrite Rabs_left1.
move=> H x Hx.
set fx := f x.
have [|Hfx Hsign] := H fx.
exact: eval_correct Hx.
rewrite /Xabs Hfx /=; congr Xreal.
by rewrite Rabs_right; auto with real.
Qed.

Local Ltac byp a b := move=> x Hx; rewrite -a //; exact: b.
Local Ltac foo :=
  by move=> Hne; apply: TM_any_correct;
  [ exact: contains_midpoint
  | intros x Hx; apply: I.abs_correct; exact: eval_correct Hx].

Theorem abs_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (abs u Y tf) (fun x => Xabs (f x)).
Proof.
move=> Hf.
rewrite /abs.
case: I.sign_large (@Isign_large_Xabs u tf Y Y f Hf) => Habs;
  case: tf Hf => [cf| |tf] Hmain //.
- destruct Hmain as [Hf|Hf].
  now left.
  right.
  apply: is_const_ext Hf.
  intros x Hx.
  now apply Habs.
- byp Habs Hmain.
- move=> Hne; apply: (@TM_fun_eq f).
  byp Habs Hf.
  exact: Hmain.
- destruct Hmain as [Hf|[y Hy1 Hy2]].
  left.
  now apply J.neg_propagate.
  right.
  exists (Xneg y).
  exact: I.neg_correct.
  move => /= x Hx.
  by rewrite -Habs // Hy2.
- red=> Hne.
  apply (TM_fun_eq Habs).
  apply: TM_opp_correct.
  apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
  exact: Xreal_Imid_contains.
- red=> Hne.
  apply (TM_fun_eq Habs).
  apply: TM_opp_correct.
  exact: Hmain.
- destruct Hmain as [Hf|[y Hy1 Hy2]].
  now left.
  right.
  exists y => //= x Hx.
  by rewrite -Habs // Hy2.
- byp Habs Hmain.
- move=> Hne; move: (Hmain Hne); apply: TM_fun_eq; byp Habs Hmain.
- foo.
- foo.
- foo.
Qed.

Definition Iconst (i : I.type) :=
  I.bounded i && I.subset i (I.bnd (I.lower i) (I.lower i)).

Lemma Iconst_true_correct i x :
  Iconst i = true -> contains (I.convert i) x -> x = Xlower (I.convert i).
Proof.
rewrite /Iconst.
case E1 : I.bounded => // .
have [/(I.lower_bounded_correct _) /= [F1 F2]
      /(I.upper_bounded_correct _) /= [F3 F4]] :=
     I.bounded_correct _ E1.
move/I.subset_correct => /=.
rewrite I.bnd_correct /subset.
case E2 : I.convert => [|x1 y1] //= .
case E3 : x => [|r] //.
case E4 : x1 => [|r1]; first by rewrite F1 /le_lower => [[]].
rewrite /le_lower F1 /=.
case E5 : y1 => [|r2]; first by rewrite F1 /le_upper => [[]].
move=> [H1 H2 H3].
by rewrite (_ : r1 = r) //; lra.
Qed.

Definition nearbyint (m : rounding_mode)
     (u : U) (X : I.type) (t : T) : T :=
  let e := eval u t X X in
  let e1 := I.nearbyint m e in
  if Iconst e1 then Const (I.bnd (I.lower e1) (I.lower e1))
  else
  let (p, i) :=
     match m with
     | rnd_UP =>
         let vm1 := I.lower im1 in
         let v1 := I.upper i1 in
         let i := I.bnd vm1 v1 in
         (I.div u.1 i1 i2, I.div u.1 i i2)
     | rnd_DN =>
         let vm1 := I.lower im1 in
         let v1 := I.upper i1 in
         let i := I.bnd vm1 v1 in
         (I.div u.1 im1 i2, I.div u.1 i i2)
     | rnd_ZR =>
          match I.sign_large e with
         | Xlt =>
             let vm1 := I.lower im1 in
             let v1 := I.upper i1 in
             let i := I.bnd vm1 v1 in
             (I.div u.1 i1 i2, I.div u.1 i i2)
         | Xund =>
            let vm1 := I.lower im1  in
            let v1 := I.upper i1 in
            (I.zero, I.bnd vm1 v1)
         | _ =>
             let vm1 := I.lower im1 in
             let v1 := I.upper i1 in
             let i := I.bnd vm1 v1 in
             (I.div u.1 im1 i2, I.div u.1 i i2)
         end
     | rnd_NE =>
         let vm1 := I.lower im1 in
         let v1 := I.upper i1 in
         let i := I.bnd vm1 v1 in
         (I.zero, I.div u.1 i i2)
     end in
  add u X t (Tm {|approx := Pol.polyC p;
                  error := I.mask i e1 |}).

Lemma contains_fromZ_lower_upper z1 z2 i :
  (-256 <= z1 <= 0)%Z -> (0 <= z2 <= 256)%Z ->
  contains
  (I.convert
     (I.mask (I.bnd (I.lower (I.fromZ_small z1)) (I.upper (I.fromZ_small z2))) i))
  (Xreal 0).
Proof.
move=> z1N z2P.
apply: I.mask_correct'.
rewrite I.bnd_correct.
refine (_ (I.fromZ_small_correct z1 _) (I.fromZ_small_correct z2 _)) ; [|lia..].
rewrite I.lower_correct.
rewrite I.upper_correct.
set i1 := I.convert _.
set i2 := I.convert _.
assert (H1 := IZR_le _ _ (proj2 z1N)).
assert (H2 := IZR_le _ _ (proj1 z2P)).
case: i1 => [|[|x1] [|x2]] /=;
    case: i2 => [|[|x3] [|x4]] //=; lra.
Qed.

Lemma contains_fromZ_lower_upper_div prec z1 z2 z3 i :
  (-256 <= z1 <= 0)%Z -> (0 <= z2 <= 256)%Z -> (0 < z3 <= 256)%Z ->
  contains
  (I.convert
     (I.mask
       (I.div prec
          (I.bnd (I.lower (I.fromZ_small z1)) (I.upper (I.fromZ_small z2)))
           (I.fromZ_small z3)) i))
    (Xreal 0).
Proof.
move=> z1N z2P z3P.
apply: I.mask_correct'.
rewrite (_ : Xreal _ = Xdiv (Xreal 0) (Xreal (IZR z3))); last first.
  rewrite /= /Xdiv'.
  case: is_zero_spec => [/eq_IZR| _]; first by lia.
  by congr (Xreal); rewrite /Rdiv; ring.
apply I.div_correct; last by apply: I.fromZ_small_correct; lia.
rewrite I.bnd_correct.
refine (_ (I.fromZ_small_correct z1 _) (I.fromZ_small_correct z2 _)) ; [|lia..].
rewrite I.lower_correct.
rewrite I.upper_correct.
set i1 := I.convert _.
set i2 := I.convert _.
assert (H1 := IZR_le _ _ (proj2 z1N)).
assert (H2 := IZR_le _ _ (proj1 z2P)).
case: i1 => [|[|x1] [|x2]] /=;
    case: i2 => [|[|x3] [|x4]] //=; lra.
Qed.

Theorem nearbyint_correct m u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (nearbyint m u Y tf) (fun x => Xnearbyint m (f x)).
Proof.
move=> Hf.
rewrite /nearbyint.
set i :=  I.nearbyint _ _.
set i1 := I.bnd _ _.
set i2 := I.bnd _ _.
set i3 := I.div _ _ _.
set i4 := I.div _ _ _.
set i5 := I.div _ _ _.
case E1 : Iconst => /=.
- have H := Iconst_true_correct E1.
- right.
  exists (Xlower (I.convert i)); last first.
  move=> x Hx; apply: H.
  apply:  I.nearbyint_correct.
    by have := eval_correct u Hf Hx.
  rewrite I.bnd_correct /=.
  rewrite <- I.lower_correct.
  case/andP: E1 => /I.bounded_correct [/I.lower_bounded_correct [-> _] _] _.
  lra.
apply: (@approximates_ext
         (fun x : R =>
                   Xadd (f x)
                            (Xsub (Xlift (Rnearbyint m) (f x)) (f x)))).
  by move=> x; case: (f x) => //= r; congr Xreal; lra.
set vv := match m with rnd_UP => _ | rnd_DN => _ | rnd_NE => _ |rnd_ZR => _  end.
rewrite (surjective_pairing vv).
apply: add_correct => //=.
intros He.
split=> //=.
- move=> x Hx.
  have /(@I.nearbyint_correct m) := eval_correct u Hf Hx.
  rewrite -/i /=.
  case: (f x) => //= Hi _.
  apply: I.mask_propagate_r.
  by case: I.convert Hi.
- move=> HY.
  have F1 : contains (I.convert Y) Xnan by rewrite HY.
  apply: I.mask_propagate_r.
  have /= := eval_correct u Hf F1.
  have := I.nearbyint_correct m (eval u tf Y Y) Xnan.
  case: I.convert => //=.
  rewrite -/i.
  by case: I.convert => /=.
- rewrite {}/vv; case m => //=;
    try apply: contains_fromZ_lower_upper_div; try lia.
  case: I.sign_large;
    try apply: contains_fromZ_lower_upper_div; try lia.
  by apply: contains_fromZ_lower_upper; lia.
- exact: contains_midpoint.
move: E1.
have F1 : Pol.contains_pointwise (Pol.polyC i3) (PolR.polyC (1/2)).
  apply: Pol.polyC_correct.
  rewrite (_ : Xreal _ =  Xdiv (Xreal 1) (Xreal 2)).
    apply: I.div_correct; exact: I.fromZ_small_correct.
  rewrite /= /Xdiv'.
  now rewrite is_zero_false.
have F2 : contains (I.convert (I.mask i4 i)) (Xreal (- (1/2))).
  apply: I.mask_correct'.
  rewrite (_ :  Xreal (- (1 / 2)) =
                Xdiv (Xreal (-1)) (Xreal 2)); last first.
    rewrite /= /Xdiv'.
    by case: is_zero_spec; try lra; move=> _; congr Xreal; lra.
  apply: I.div_correct; last by exact: I.fromZ_small_correct.
  rewrite I.bnd_correct I.lower_correct I.upper_correct.
  refine (_ (I.fromZ_small_correct (-1) _) (I.fromZ_small_correct 1 _)) ; [|easy..].
  by ((do 2 case: I.convert) => //= [] [|x1] [|y1] //; try lra) =>
       [] [|x2] [|y2] //; lra.
have F3 r :
  contains (I.convert (I.mask i4 i))
  (Xreal (Rnearbyint rnd_UP r - r - 1 / 2)).
  apply: I.mask_correct' => /=.
  set ir := IZR _.
  rewrite (_ : Xreal _ =
            Xdiv (Xreal (2 * (ir - r - 1/2))) (Xreal 2)); last first.
      rewrite /= /Xdiv'.
      case: is_zero_spec; try lra; move=> _.
      by congr Xreal; lra.
  apply: I.div_correct; last by exact: I.fromZ_small_correct.
  rewrite I.bnd_correct.
  rewrite /contains.
  refine (_ (I.fromZ_small_correct (-1) _) (I.fromZ_small_correct 1 _)) ; [|easy..].
  rewrite I.lower_correct.
  rewrite I.upper_correct.
  set iv1 := I.convert _.
  set iv2 := I.convert _.
  have  HR := Rnearbyint_error_UP r.
  rewrite /= -/ir in HR.
  by case: iv1 => [|[|x1] [|x2]] /=;
    case: iv2 => [|[|x3] [|x4]] //=; try lra.
have F4 : Pol.contains_pointwise (Pol.polyC i5) (PolR.polyC (- (1/2))).
  apply: Pol.polyC_correct.
  rewrite (_ : Xreal _ =  Xdiv (Xreal (-1)) (Xreal 2)).
    by apply: I.div_correct; exact: I.fromZ_small_correct.
  rewrite /= /Xdiv'.
  by case: is_zero_spec; try lra; move=> _; congr Xreal; lra.
have F5 : contains (I.convert (I.mask i4 i)) (Xreal (1/2)).
  apply: I.mask_correct'.
  rewrite (_ :  Xreal (1 / 2) =
                Xdiv (Xreal 1) (Xreal 2)); last first.
    rewrite /= /Xdiv'.
    by case: is_zero_spec; try lra; move=> _; congr Xreal; lra.
  apply: I.div_correct; last by exact: I.fromZ_small_correct.
  rewrite I.bnd_correct I.lower_correct I.upper_correct.
  refine (_ (I.fromZ_small_correct (-1) _) (I.fromZ_small_correct 1 _)) ; [|easy..].
  by ((do 2 case: I.convert) => //= [] [|x1] [|y1] //; try lra) =>
       [] [|x2] [|y2] //; lra.
have F6 r :
  contains (I.convert (I.mask i4 i))
  (Xreal (Rnearbyint rnd_DN r - r + 1 / 2)).
  apply: I.mask_correct' => /=.
  set ir := IZR _.
  rewrite (_ : Xreal _ =
            Xdiv (Xreal (2 * (ir - r + 1/2))) (Xreal 2)); last first.
      rewrite /= /Xdiv'.
      case: is_zero_spec; try lra; move=> _.
      by congr Xreal; lra.
  apply: I.div_correct; last by exact: I.fromZ_small_correct.
  rewrite I.bnd_correct.
  rewrite /contains.
  refine (_ (I.fromZ_small_correct (-1) _) (I.fromZ_small_correct 1 _)) ; [|easy..].
  rewrite I.lower_correct.
  rewrite I.upper_correct.
  set iv1 := I.convert _.
  set iv2 := I.convert _.
  have  HR := Rnearbyint_error_DN r.
  rewrite /= -/ir in HR.
  by case: iv1 => [|[|x1] [|x2]] /=;
    case: iv2 => [|[|x3] [|x4]] //=; try lra.
move: F2 F3 F5 F6.
rewrite {}/vv {}/i1 {}/i.
case: m => //=; set i := I.nearbyint _ _ => F2 F3 F5 F6 E1.
- exists (PolR.polyC (1/2)) => //= y _.
  rewrite Rmult_0_l Rplus_0_l.
  case: (f y) => [|r] //=.
  by rewrite Rminus_0_l.
- exists (PolR.polyC (-(1/2))) => //= y _.
  rewrite Rmult_0_l Rplus_0_l /Rminus Ropp_involutive.
  case: (f y) => //=.
  by rewrite Rplus_0_l.
- case: I.sign_large (I.sign_large_correct
                         (eval u tf Y Y)) => Hsign.
  - exists (PolR.polyC (-(1/2))) => //= y Cy.
    rewrite Rmult_0_l Rplus_0_l.
    case Er : (f y) => [|r] //=.
      by rewrite Rminus_0_l Ropp_involutive.
    rewrite {1}/Rminus Ropp_involutive.
    rewrite Raux.Ztrunc_floor //.
    have : f y = Xreal 0.
      apply: Hsign.
      by apply: (eval_correct u Hf Cy).
    by rewrite Er => [[]]; lra.
  - exists (PolR.polyC (1/2)) => //= y Cy.
    rewrite Rmult_0_l Rplus_0_l.
    case Er : (f y) => [|r] //=.
      by rewrite Rminus_0_l.
    rewrite Raux.Ztrunc_ceil //.
    have [_ /=] := Hsign _ (eval_correct u Hf Cy).
    by rewrite Er.
  - exists (PolR.polyC (-(1/2))) => //= y Cy.
    rewrite Rmult_0_l Rplus_0_l.
    case Er : (f y) => [|r] /=.
      by rewrite Rminus_0_l Ropp_involutive.
    rewrite Raux.Ztrunc_floor //.
      rewrite /Rminus Ropp_involutive.
      by apply F6.
    have [_ /=] := Hsign _ (eval_correct u Hf Cy).
    by rewrite Er.
  - exists (PolR.polyC 0) => //= [|y _].
      apply: Pol.polyC_correct.
      by apply: J.zero_correct.
    rewrite Rmult_0_l Rplus_0_l.
    case Er : (f y) => [|r] /=.
      rewrite Rminus_0_l.
      apply: I.mask_correct'.
      rewrite I.bnd_correct I.lower_correct I.upper_correct.
      refine (_ (I.fromZ_small_correct (-1) _) (I.fromZ_small_correct 1 _)) ; [|easy..].
      by ((do 2 case: I.convert) => //= [] [|x1] [|y1] //; try lra) =>
         [] [|x2] [|y2] //; lra.
    apply: I.mask_correct'.
    rewrite I.bnd_correct.
    rewrite /contains.
    refine (_ (I.fromZ_small_correct (-1) _) (I.fromZ_small_correct 1 _)) ; [|easy..].
    rewrite I.lower_correct.
    rewrite I.upper_correct.
    set iv1 := I.convert _.
    set iv2 := I.convert _.
    have  HR := Rnearbyint_error_ZR r.
    rewrite /= in HR.
    by case: iv1 => [|[|x1] [|x2]] /=;
       case: iv2 => [|[|x3] [|x4]] //=; try lra.
exists (PolR.polyC 0) => //= [|y Cy].
  apply: Pol.polyC_correct.
  by apply: J.zero_correct.
rewrite Rmult_0_l Rplus_0_r Rminus_0_r.
case: (f y) => /=.
  apply: I.mask_correct'.
  rewrite (_ :  Xreal _ =
                Xdiv (Xreal 0) (Xreal 2)); last first.
    rewrite /= /Xdiv'.
    by case: is_zero_spec; try lra; move=> _; congr Xreal; lra.
  apply: I.div_correct; last by exact: I.fromZ_small_correct.
  rewrite I.bnd_correct I.lower_correct I.upper_correct.
  refine (_ (I.fromZ_small_correct (-1) _) (I.fromZ_small_correct 1 _)) ; [|easy..].
  by ((do 2 case: I.convert) => //= [] [|x1] [|y1] //; try lra) =>
       [] [|x2] [|y2] //; lra.
move=> r.
apply: I.mask_correct'.
set ir := IZR _.
rewrite (_ : Xreal _ =
          Xdiv (Xreal (2 * (ir - r))) (Xreal 2)); last first.
  rewrite /= /Xdiv'.
  case: is_zero_spec; try lra; move=> _.
  by congr Xreal; lra.
apply: I.div_correct; last by exact: I.fromZ_small_correct.
rewrite I.bnd_correct.
rewrite /contains.
refine (_ (I.fromZ_small_correct (-1) _) (I.fromZ_small_correct 1 _)) ; [|easy..].
rewrite I.lower_correct.
rewrite I.upper_correct.
set iv1 := I.convert _.
set iv2 := I.convert _.
have  HR := Rnearbyint_error_NE r.
rewrite /= -/ir in HR.
by case: iv1 => [|[|x1] [|x2]] /=;
   case: iv2 => [|[|x3] [|x4]] //=; try lra.
Qed.

(** ** Generic implementation of basic functions *)

Definition fun_gen
  (fi : I.precision -> I.type -> I.type)
  (ftm : I.precision -> TM_type)
  (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Const c => Const (fi u.1 c)
    | Var => let X0 := Imid X in Tm (ftm u.1 X0 X u.2)
    | Tm tm => let X0 := Imid X in
      Tm (TM_comp u.1 (ftm u.1) tm X0 X u.2)
  end.

Lemma fun_gen_correct
  (fi : I.precision -> I.type -> I.type)
  (ftm : I.precision -> TM_type)
  (fx : R -> ExtendedR)
  (ft := fun_gen fi ftm) :
  (forall prec : I.precision, I.extension (Xbind fx) (fi prec)) ->
  (forall prec X0 X n, tmsize (ftm prec X0 X n) = n.+1) ->
  (forall prec x0 X0 X n,
    subset' (I.convert X0) (I.convert X) ->
    contains (I.convert X0) (Xreal x0) ->
    i_validTM x0 (I.convert X) (ftm prec X0 X n) fx) ->
  forall (u : U) (X : I.type) (tf : T) (f : R -> ExtendedR),
  approximates X tf f ->
  approximates X (ft u X tf) (fun x => Xbind fx (f x)).
Proof.
move=> Hext Hsiz Hvalid u X [c| |tm] f Hmain.
- destruct Hmain as [Hf|[y Hy1 Hy2]].
    left.
    apply contains_Xnan.
    apply (Hext u.1 c (Xbind fx Xnan)).
    now apply contains_Xnan.
  right.
  exists (Xbind fx y); first exact: Hext.
  by move=> x Hx; rewrite /= Hy2.
- move=> HneY.
  apply: (@TM_fun_eq fx).
  by move=> *; rewrite Hmain.
  apply: Hvalid.
  exact: Imid_subset.
  exact: Xreal_Imid_contains.
- move=> HneY; move/(_ HneY) in Hmain.
  have [Hdef Hnai Hzero Hsubset Htm] := Hmain.
  apply (TM_comp_correct u.1) =>//.
  exact: Xreal_Imid_contains.
  move=> *; exact: Hvalid.
Qed.

(*
Definition prim (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Dummy => Dummy
    | Const c => let X0 := Imid X in
        Tm (TM_integral u.1 X0 X (TM_cst u.1 c X0 X u.2))
    | Var => let X0 := Imid X in
        Tm (TM_integral u.1 X0 X (TM_var u.1 X0 X u.2))
    | Tm tm => let X0 := Imid X in
        Tm (TM_integral u.1 X0 X tm)
  end.
*)

(*
Definition prim (u : U) (X X1 Y1 : I.type) (t : T) : T :=
  if I.subset X1 X then
    let X0 := Imid X in
    let tm := match t with
              | Dummy => TM_any u.1 I.nai X u.2
              | Const c => TM_cst c
              | Var => TM_var X0
              | Tm tm => tm
              end in
    let tm0 := TM_integral u.1 X0 X tm in
    let c := I.add u.1 Y1 (I.neg (Bnd.ComputeBound u.1 (approx tm0) X1)) in
    Tm (RPA (Pol.set_nth (approx tm0) 0 c) (I.add u.1 (error tm0) (error tm0)))
  else Tm (TM_any u.1 I.nai X u.2).

Conjecture prim_correct :
  forall u (X X1 Y1 : I.type) tf f f0 x1 y1,
  contains (I.convert X1) (Xreal x1) ->
  contains (I.convert Y1) (Xreal y1) ->
  approximates X tf f ->
  (forall r : R, f0 r = toR_fun f r) ->
  approximates X (prim u X X1 Y1 tf) (fun x => match x with
                                         | Xnan => Xnan
                                         | Xreal r => Xreal (RInt f0 x1 r + y1)
                                         end).
*)

Definition inv := Eval hnf in fun_gen I.inv TM_inv.

Theorem inv_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (inv u Y tf) (fun x => Xinv (f x)).
Proof.
apply: fun_gen_correct =>//.
- exact: I.inv_correct.
- exact: size_TM_inv.
- exact: TM_inv_correct.
Qed.

Definition sqrt := Eval hnf in fun_gen I.sqrt TM_sqrt.

Theorem sqrt_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (sqrt u Y tf) (fun x => Xsqrt (f x)).
Proof.
apply: fun_gen_correct =>//.
- exact: I.sqrt_correct.
- exact: size_TM_sqrt.
- exact: TM_sqrt_correct.
Qed.

Definition exp := Eval hnf in fun_gen I.exp TM_exp.

Theorem exp_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (exp u Y tf) (fun x => Xexp (f x)).
Proof.
apply: fun_gen_correct =>//.
- exact: I.exp_correct.
- exact: size_TM_exp.
- exact: TM_exp_correct.
Qed.

Definition ln := Eval hnf in fun_gen I.ln TM_ln.

Theorem ln_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (ln u Y tf) (fun x => Xln (f x)).
Proof.
apply: fun_gen_correct =>//.
- exact: I.ln_correct.
- exact: size_TM_ln.
- exact: TM_ln_correct.
Qed.

Definition cos := Eval hnf in fun_gen I.cos TM_cos.

Theorem cos_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (cos u Y tf) (fun x => Xcos (f x)).
Proof.
apply: fun_gen_correct =>//.
- exact: I.cos_correct.
- exact: size_TM_cos.
- exact: TM_cos_correct.
Qed.

Definition sin := Eval hnf in fun_gen I.sin TM_sin.

Theorem sin_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (sin u Y tf) (fun x => Xsin (f x)).
Proof.
apply: fun_gen_correct =>//.
- exact: I.sin_correct.
- exact: size_TM_sin.
- exact: TM_sin_correct.
Qed.

Definition tan := Eval hnf in fun_gen I.tan TM_tan.

Theorem tan_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (tan u Y tf) (fun x => Xtan (f x)).
Proof.
apply: fun_gen_correct =>//.
- exact: I.tan_correct.
- exact: size_TM_tan.
- exact: TM_tan_correct.
Qed.

Definition atan := Eval hnf in fun_gen I.atan TM_atan.

Theorem atan_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (atan u Y tf) (fun x => Xatan (f x)).
Proof.
apply: fun_gen_correct =>//.
- exact: I.atan_correct.
- exact: size_TM_atan.
- exact: TM_atan_correct.
Qed.

Definition power_int p := Eval cbv delta[fun_gen] beta in
  match p with
(*| 0%Z => fun u xi t => Const (I.fromZ 1) *)
  | 1%Z => fun u xi t => t
  | _ => fun_gen
           (fun prec x => I.power_int prec x p)
           (fun prec => TM_power_int prec p)
  end.

Theorem power_int_correct :
  forall (p : Z) u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (power_int p u Y tf) (fun x => Xbind (fun y => Xpower_int (Xreal y) p) (f x)).
Proof.
move=> p u Y tf f Hmain.
have [Hp|Hp] := Z.eq_dec p 1%Z.
(* . *)
rewrite Hp.
apply (@approximates_ext f)=>//.
move=> x; rewrite /Xinv.
case: (f x) =>[//|r].
by rewrite /= Rmult_1_r.
(* . *)
case: p Hp =>[|p'|p']=>//; (try case: p'=>[p''|p''|]) =>// H;
apply: (fun_gen_correct
  (fi := fun prec x => I.power_int prec x _)
  (ftm := fun prec => TM_power_int prec _)
  (fx := fun x => Xpower_int (Xreal x) _)) =>//;
try (by move=> *; apply: I.power_int_correct);
try (by move=> *; rewrite /tmsize size_TM_power_int);
by move=> *; apply: TM_power_int_correct.
Qed.

Definition sqr := power_int 2.

Theorem sqr_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (sqr u Y tf) (fun x => Xsqr (f x)).
Proof.
move=> u Y tf f Hf.
apply: (@approximates_ext (fun x => Xpower_int (f x) 2%Z)).
move=> x; rewrite /Xpower_int /Xsqr.
case: (f x) =>[//|r].
by rewrite /= Rmult_1_r.
exact: power_int_correct.
Qed.

End TM.
