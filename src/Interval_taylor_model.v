(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2013-2015, Inria

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

Require Import Reals ZArith.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.ssrfun mathcomp.ssreflect.eqtype mathcomp.ssreflect.ssrnat mathcomp.ssreflect.seq mathcomp.ssreflect.bigop.
Require Import Interval_interval.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_specific_ops.
Require Import Interval_bigint_carrier.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import interval_compl.
Require Import poly_datatypes.
Require Import taylor_model_int_sharp.
Require Import xreal_ssr_compat.
Require Import poly_bound.
Require Import poly_bound_quad.
Require Import Interval_univariate Rstruct.

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

Inductive t_ := Dummy | Const of I.type | Var | Tm of rpa.

Definition T := t_.

Definition U := (I.precision * nat)%type.

(** ** Auxiliary material *)

Definition isDummy (t : T) : bool := if t is Dummy then true else false.

Definition tmsize (tm : rpa) := Pol.size (approx tm).

Definition tsize (t : T) : nat :=
  match t with
    | Dummy => 1
    | Const _ => 1
    | Var => 2
    | Tm tm => tmsize tm
  end.

Definition get_tm (u : U) X (t : T) : rpa :=
  match t with
    | Dummy => TM_any u.1 I.nai X (* initially u.2 => preferably 0... *) 0
    | Const c => TM_cst X c
    | Var => let X0 := Imid X in (TM_var X X0)
    | Tm tm => tm (* ignore u, X in this branch *)
  end.

Lemma size_get_tm u X t :
  tmsize (get_tm u X t) = tsize t.
Proof. by case: t. Qed.

Definition not_nil (tf : T) : bool :=
  match tf with
    | Dummy => true
    | Const _ => true
    | Var => true
    | Tm tm => tmsize tm != 0
  end.

Lemma not_nilE (t : T) : (not_nil t) = (0 < tsize t).
Proof. by apply/idP/idP; case: t =>//= tm; rewrite lt0n //; move/negP. Qed.

(** ** Define the main validity predicate *)

Definition approximates (X : I.type) (tf : T) (f : R -> ExtendedR) : Prop :=
  let X0 := Imid X in
  not_nil tf /\
  match tf with
  | Dummy => True
  | Const c => is_const f X c
  | Var =>
    forall x : R, contains (I.convert X) (Xreal x) -> f x = Xreal x
  | Tm tm =>
    not_empty (I.convert X) ->
    i_validTM (I.convert X0) (I.convert X) tm f
  end.

Theorem approximates_ext f g xi t :
  (forall x, f x = g x) ->
  approximates xi t f -> approximates xi t g.
Proof.
move=> Hfg [Hcont Hmain].
split=>//.
case: t Hmain {Hcont} =>[|c| |tm] Hmain; rewrite -?Hfg //.
exact: is_const_ext_weak Hmain.
by move=> *; rewrite -Hfg; apply: Hmain.
move=> Hne; move/(_ Hne): Hmain.
exact: TM_fun_eq.
Qed.

Lemma get_tm_correct u Y tf f :
  approximates Y tf f ->
  approximates Y (Tm (get_tm u Y tf)) f.
Proof.
case: tf =>[|c||tm]; rewrite /approximates //; case => ? H; split=>//=.
- move=> ?; apply: TM_any_correct.
  exact: not_empty_Imid.
  exact: Imid_subset.
  by rewrite I.nai_correct.
- move=> Hne.
  apply TM_cst_correct_strong =>//.
  exact: Imid_subset.
  exact: not_empty_Imid.
- move=> Hne.
  apply: TM_var_correct_strong=>//.
    exact: Imid_subset.
  by move/not_empty_Imid: Hne.
Qed.

(** ** Main definitions and correctness claims *)

Definition const : I.type -> T := Const.

Theorem const_correct (c : I.type) (r : R) :
  contains (I.convert c) (Xreal r) ->
  forall (X : I.type),
  approximates X (const c) (fun _ => Xreal r).
Proof. move=> Hcr X; split=>//=; by exists (Xreal r). Qed.

Definition dummy : T := Dummy.

Theorem dummy_correct xi f :
  TM.approximates xi dummy f.
Proof. done. Qed.

Definition var : T := Var.

Theorem var_correct (X : I.type) :
  approximates X var Xreal.
Proof. done. Qed.

Definition eval (u : U) (t : T) (Y X : I.type) : I.type :=
  if I.subset X Y then
  match t with
  | Dummy => I.nai
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
case: tf Hf => [ |c| |tm].
(* Dummy *)
by rewrite I.nai_correct.
(* Const *)
case=> _ [y Hy1 /= Hy2].
case: x Hx =>[|x] Hx /=.
  move/contains_Xnan in Hx.
  have H0 : contains (I.convert Y) (Xreal 0).
  by apply: subset_contains Hsubset _ _; rewrite Hx.
  have->: Xnan = Xmask (f R0) Xnan by [].
  apply: I.mask_correct =>//.
  by rewrite Hy2.
  by rewrite Hx.
have->: f x = Xmask (f x) (Xreal x) by [].
apply: I.mask_correct=>//.
rewrite Hy2 //.
exact: subset_contains Hsubset _ _.
(* Var *)
case => /= _.
case: x Hx => [|x] Hx //= -> //.
exact: subset_contains Hsubset _ _.
(* Tm *)
move=> Hf.
have /= {Hf} := get_tm_correct u Hf=> Htm.
have {Htm} [Hnil Htm] := Htm.
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
move/(_ c0 Hc0) in Hmain.
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
  exact: R_sub_correct.
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
    | Dummy, _ | _, Dummy => Dummy
    | Const c1, Const c2 => Const (I.add u.1 c1 c2)
    | _, _ => add_slow u X t1 t2
  end.

Lemma add_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (add_slow u Y tf tg) (fun x => Xadd (f x) (g x)).
Proof.
move=> [[Hnil Hf] [_ Hg]].
split=>//.
rewrite not_nilE /add_slow /= /tmsize size_TM_add -!/(tmsize _) !size_get_tm.
rewrite not_nilE in Hnil.
by rewrite -(prednK Hnil) maxSn.
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
case: tf Hf {Hnil} => [|cf||tmf] Hf;
  case: tg Hg => [|cg||tmg] Hg /=;
  try (have {Hf} Hf := Hf Hne);
  try (have {Hg} Hg := Hg Hne);
  apply: TM_add_correct;
  try (apply: TM_any_correct;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem add_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (add u Y tf tg) (fun x => Xadd (f x) (g x)).
Proof.
move: tf tg => [|cf| |tf] [|cg| |tg] Hf Hg;
  try apply: dummy_correct;
  try exact: add_slow_correct.
split=>//.
case: Hf => _ [yf Hyf1 /= Hyf2].
case: Hg => _ [yg Hyg1 /= Hyg2].
exists (Xadd yf yg); first exact: I.add_correct.
by move=> x Hx; rewrite /= Hyf2 // Hyg2.
Qed.

Definition opp_slow (u : U) (X : I.type) (t : T) : T :=
  Tm (TM_opp (get_tm u X t)).

Definition opp (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Dummy => Dummy
    | Const c => Const (I.neg c)
    | _ => opp_slow u X t
  end.

Lemma opp_slow_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (opp_slow u Y tf) (fun x => Xneg (f x)).
Proof.
move=> [Hnil Hmain].
split=>//.
rewrite not_nilE /opp_slow /= /tmsize size_TM_opp -!/(tmsize _) !size_get_tm.
by rewrite not_nilE in Hnil.
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
case: tf Hmain {Hnil} => [|cf||tmf] Hf;
  try (have {Hf} Hf := Hf Hne);
  apply: TM_opp_correct;
  try (apply: TM_any_correct;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem opp_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (opp u Y tf) (fun x => Xneg (f x)).
Proof.
move: tf => [|cf| |tf] [Hnil Hmain]; try exact: opp_slow_correct.
exact: dummy_correct.
split=>//.
have [y Hy1 /= Hy2] := Hmain.
exists (Xneg y); first exact: I.neg_correct.
by move=> x Hx; rewrite /= Hy2.
Qed.

Definition sub_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let M1 := get_tm u X t1 in
  let M2 := get_tm u X t2 in
  Tm (TM_sub u.1 M1 M2).

Definition sub (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Dummy, _ | _, Dummy => Dummy
    | Const c1, Const c2 => Const (I.sub u.1 c1 c2)
  (*| Var, Var => Const I.zero : FIXME *)
    | _, _ => sub_slow u X t1 t2
  end.

Lemma sub_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (sub_slow u Y tf tg) (fun x => Xsub (f x) (g x)).
Proof.
move=> [Hnil Hf] [_ Hg].
split=>//.
rewrite not_nilE /sub_slow /= /tmsize size_TM_sub -!/(tmsize _) !size_get_tm.
rewrite not_nilE in Hnil.
by rewrite -(prednK Hnil) maxSn.
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
case: tf Hf {Hnil} => [|cf||tmf] Hf;
  case: tg Hg => [|cg||tmg] Hg /=;
  try (have {Hf} Hf := Hf Hne);
  try (have {Hg} Hg := Hg Hne);
  apply: TM_sub_correct;
  try (apply: TM_any_correct;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem sub_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (sub u Y tf tg) (fun x => Xsub (f x) (g x)).
Proof.
move: tf tg => [|cf| |tf] [|cg| |tg] Hf Hg;
  try apply: dummy_correct;
  try exact: sub_slow_correct.
split=>//.
case: Hf => _ [yf Hyf1 /= Hyf2].
case: Hg => _ [yg Hyg1 /= Hyg2].
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
    | Dummy, _ | _, Dummy => Dummy
    | Const c1, Const c2 => Const (I.mul u.1 c1 c2)
    | Const c1, _ => Tm (TM_mul_mixed u.1 c1 (get_tm u X t2) )
    | _, Const c2 => Tm (TM_mul_mixed u.1 c2 (get_tm u X t1) )
    | _, _ => mul_slow u X t1 t2
  end.

Lemma mul_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (mul_slow u Y tf tg) (fun x => Xmul (f x) (g x)).
Proof.
move=> [Hnil Hf] [_ Hg].
split=>//.
(* ... *)
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
case: tf Hf {Hnil} => [|cf||tmf] Hf;
  case: tg Hg => [|cg||tmg] Hg /=;
  try (have {Hf} Hf := Hf Hne);
  try (have {Hg} Hg := Hg Hne);
  apply: TM_mul_correct =>//;
  (* then *)
  try (apply: TM_any_correct;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try by auto 2.
Qed.

Theorem mul_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (mul u Y tf tg) (fun x => Xmul (f x) (g x)).
Proof.
move: tf tg => [|cf| |tf] [|cg| |tg] Hf Hg;
  try apply: dummy_correct;
  try exact: mul_slow_correct.
(* Const . Const *)
split=>//.
case: Hf => _ [yf Hyf1 /= Hyf2].
case: Hg => _ [yg Hyg1 /= Hyg2].
exists (Xmul yf yg); first exact: I.mul_correct.
by move=> x Hx; rewrite /= Hyf2 // Hyg2.
(* Const . Var *)
have [Hnil1 H1] := Hf.
have [Hnil2 H2] := Hg.
split=>//.
red=>Hne.
apply: TM_mul_mixed_correct_strong =>//.
  exact: not_empty_Imid.
apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
exact: not_empty_Imid.
(* Const . Tm *)
have [Hnil1 H1] := Hf;
have [Hnil2 H2] := Hg;
split=>//.
  by rewrite /= /tmsize size_TM_mul_mixed.
red=>Hne.
have {H2} H2 := H2 Hne.
apply: TM_mul_mixed_correct_strong =>//.
exact: not_empty_Imid.
(* Var . Const *)
have [Hnil1 H1] := Hf;
have [Hnil2 H2] := Hg;
split=>//.
red=>Hne.
apply: (@TM_fun_eq (fun x => g x * f x)%XR _) =>//.
by move=> *; exact: Xmul_comm.
apply: TM_mul_mixed_correct_strong =>//.
  exact: not_empty_Imid.
apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
exact: not_empty_Imid.
(* Tm . Const *)
have [Hnil1 H1] := Hf;
have [Hnil2 H2] := Hg;
split=>//.
  by rewrite /= /tmsize size_TM_mul_mixed.
red=>Hne.
have Hdf := H1 Hne.
apply: (@TM_fun_eq (fun x => g x * f x)%XR _) =>//.
by move=> *; exact: Xmul_comm.
apply: TM_mul_mixed_correct_strong =>//.
exact: not_empty_Imid.
Qed.

Definition div_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let M1 := get_tm u X t1 in
  let M2 := get_tm u X t2 in
  let X0 := Imid X in
  Tm (TM_div u.1 M1 M2 X0 X u.2).

Definition div (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Dummy, _ | _, Dummy => Dummy
    | Const c1, Const c2 => Const (I.div u.1 c1 c2)
    | _, Const c2 => Tm (TM_div_mixed_r u.1 (get_tm u X t1) c2)
  (*| Var, Var => Const (I.fromZ 1) : FIXME *)
    | _, _ => div_slow u X t1 t2
  end.

Lemma div_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (div_slow u Y tf tg) (fun x => Xdiv (f x) (g x)).
Proof.
move=> [Hnil Hf] [_ Hg].
split=>//.
rewrite /div_slow.
(* ... *)
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
apply TM_div_correct=>//.
(* . *)
case: tf Hf Hg {Hnil}; case: tg =>// *;
  try (apply: TM_any_correct;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
(* . *)
case: tf Hf Hg {Hnil}; case: tg =>// *;
  try (apply: TM_any_correct;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem div_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (div u Y tf tg) (fun x => Xdiv (f x) (g x)).
Proof.
move: tf tg => [|cf| |tf] [|cg| |tg] Hf Hg;
  try apply: dummy_correct;
  try exact: div_slow_correct.
(* Const . Const *)
split=>//.
case: Hf => _ [yf Hyf1 /= Hyf2].
case: Hg => _ [yg Hyg1 /= Hyg2].
exists (Xdiv yf yg); first exact: I.div_correct.
by move=> x Hx; rewrite /= Hyf2 // Hyg2.
(* Var . Const *)
have [Hnil1 H1] := Hf;
have [Hnil2 H2] := Hg;
split=>//.
red=>Hne.
apply: TM_div_mixed_r_correct_strong =>//.
  exact: not_empty_Imid.
apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
exact: not_empty_Imid.
(* Const . Tm *)
have [Hnil1 H1] := Hf.
have [Hnil2 H2] := Hg.
split=>//.
  by rewrite /= /tmsize size_TM_div_mixed_r.
red=>Hne.
apply: TM_div_mixed_r_correct_strong =>//.
  exact: not_empty_Imid.
exact: H1.
Qed.

Definition abs (u : U) (X : I.type) (t : T) : T :=
  if isDummy t then Dummy else
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
      Xabs (f x) = f x (* weak but sufficient *)
    | Xgt =>
      forall x, contains (I.convert X) (Xreal x) ->
      Xabs (f x) = f x
    | Xlt =>
      forall x, contains (I.convert X) (Xreal x) ->
      Xabs (f x) = Xneg (f x)
    | Xund => True
  end.
Proof.
case=> [Hnil Hmain].
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

Local Ltac byp a b := move=> x Hx; rewrite a //; exact: b.
Local Ltac foo :=
  by move=> Hne; apply: TM_any_correct;
  [ exact: not_empty_Imid | exact: Imid_subset
  | intros x Hx; apply: I.abs_correct; exact: eval_correct Hx].

Theorem abs_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (abs u Y tf) (fun x => Xabs (f x)).
Proof.
move=> Hf; case: (Hf) => [Hnil Hmain].
rewrite /abs.
case E: (isDummy tf); first by split; rewrite 1?Hnan.
split.
- case: I.sign_large=>//.
    rewrite /opp /=.
    case: tf Hf Hnil {Hmain E} => [| | |tf] Hf //=.
      by rewrite /tmsize size_TM_opp.
    by rewrite /not_nil /tmsize size_TM_any.
case: I.sign_large (@Isign_large_Xabs u tf Y Y f Hf) => Habs;
  case: tf Hf Hnil Hmain Habs {E} => [|cf| |tf] Hf Hnil Hmain Habs //.
- have [[|y] Hy1 /= Hy2] := Hmain.
    exists Xnan => //= x Hx.
    by rewrite Hy2.
    exists (Xreal y) => //= x Hx.
    by rewrite Habs // Hy2.
- byp Habs Hmain.
- move=> Hne; apply: (@TM_fun_eq f).
  byp Habs Hmain.
  exact: Hmain.
- have [[|y] Hy1 /= Hy2] := Hmain.
    exists (Xneg Xnan).
    exact: I.neg_correct.
    move => /= x Hx.
    by rewrite Hy2.
    exists (Xneg (Xreal y)).
    exact: I.neg_correct.
    move => /= x Hx.
    by rewrite Habs // Hy2.
- red=> Hne.
  apply: (@TM_fun_eq (fun x => Xneg (f x))).
  move=> *; symmetry; exact: Habs.
  apply: TM_opp_correct.
  apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
  apply Imid_contains in Hne.
  apply: not_emptyE; by eexists; apply Hne.
- red=> Hne.
  apply: (@TM_fun_eq (fun x => Xneg (f x))).
  move=> *; symmetry; exact: Habs.
  apply: TM_opp_correct.
  exact: Hmain.
- have [[|y] Hy1 /= Hy2] := Hmain.
    exists Xnan => //= x Hx.
    by rewrite Hy2.
    exists (Xreal y) => //= x Hx.
    by rewrite Habs // Hy2.
- byp Habs Hmain.
- move=> Hne; move: (Hmain Hne); apply: TM_fun_eq; byp Habs Hmain.
- foo.
- foo.
- foo.
- foo.
Qed.

(** ** Generic implementation of basic functions *)

Definition fun_gen
  (fi : I.precision -> I.type -> I.type)
  (ftm : I.precision -> TM_type)
  (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Dummy => Dummy
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
  (forall prec X0 X n,
    subset (I.convert X0) (I.convert X) ->
    not_empty (I.convert X0) ->
    i_validTM (I.convert X0) (I.convert X) (ftm prec X0 X n) fx) ->
  forall (u : U) (X : I.type) (tf : T) (f : R -> ExtendedR),
  approximates X tf f ->
  approximates X (ft u X tf) (fun x => Xbind fx (f x)).
Proof.
move=> Hext Hsiz Hvalid u X [|c| |tm] f [Hnil Hmain].
- exact: dummy_correct.
- split => //=.
  have [y Hy1 /= Hy2] := Hmain.
  exists (Xbind fx y); first exact: Hext.
  by move=> x Hx; rewrite /= Hy2.
- split=>//=.
  by rewrite Hsiz.
  move=> HneY.
  apply: (@TM_fun_eq fx).
  by move=> *; rewrite Hmain.
  apply: Hvalid.
  exact: Imid_subset.
  apply not_empty_Imid in HneY.
  have [y Hy] := HneY; by exists y.
- split.
  rewrite /not_nil /ft /fun_gen /tmsize size_TM_comp //.
  by move=> Y0 Y k; move: (Hsiz u.1 Y0 Y k); rewrite /tmsize =>->.
  move=> HneY; move/(_ HneY) in Hmain.
  have [Hdef Hnai Hzero Hsubset Htm] := Hmain.
  have Hne' := not_empty_Imid HneY.
  have [m Hm] := Hne'.
  apply (TM_comp_correct u.1) =>//.
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
move=> p u Y tf f Hf.
have [Hnil Hmain] := Hf.
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
