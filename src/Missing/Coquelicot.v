(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2015-2016, Inria.
Copyright (C) 2015-2016, IRIT.

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

From Coq Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.

Require Import Stdlib.
Require Import MathComp.

Lemma continuous_Rinv x :
  x <> 0 ->
  continuous (fun x => / x) x.
Proof.
move => Hxneq0.
apply continuity_pt_filterlim. (* strange: apply works but not apply: *)
apply: continuity_pt_inv => // .
apply continuity_pt_filterlim.
apply: continuous_id.
Qed.

Lemma continuous_Rinv_comp (f : R -> R) x:
  continuous f x ->
  f x <> 0 ->
  continuous (fun x => / (f x)) x.
Proof.
move => Hcont Hfxneq0.
apply: continuous_comp => //.
by apply: continuous_Rinv.
Qed.

Lemma continuous_cos x : continuous cos x.
Proof.
apply continuity_pt_filterlim.
by apply: continuity_cos => // .
Qed.

Lemma continuous_cos_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => cos (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => //.
by apply: continuous_cos.
Qed.

Lemma continuous_sin x : continuous sin x.
Proof.
apply continuity_pt_filterlim.
by apply: continuity_sin => // .
Qed.

Lemma continuous_sin_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => sin (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => //.
by apply: continuous_sin.
Qed.

Lemma continuous_tan x : cos x <> 0 -> continuous tan x.
Proof.
move => Hcos.
rewrite /tan.
apply: continuous_mult; first by apply: continuous_sin.
by apply: continuous_Rinv_comp; first by apply: continuous_cos.
Qed.

Lemma continuous_atan x : continuous atan x.
Proof.
apply: ex_derive_continuous.
apply: ex_derive_Reals_1.
exact: derivable_pt_atan.
Qed.

Lemma continuous_atan_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => atan (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => //.
by apply: continuous_atan.
Qed.

Lemma continuous_exp x : continuous exp x.
Proof.
apply: ex_derive_continuous.
apply: ex_derive_Reals_1.
exact: derivable_pt_exp.
Qed.

Lemma continuous_exp_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => exp (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => //.
by apply: continuous_exp.
Qed.

Lemma continuous_sqrt (x : R) : continuous sqrt x.
Proof.
destruct (Rle_or_lt 0 x) as [Hx|Hx].
apply continuity_pt_filterlim.
by apply: continuity_pt_sqrt.
assert (Hs: forall t, t < 0 -> sqrt t = 0).
  intros t Ht.
  unfold sqrt.
  case Rcase_abs.
  easy.
  intros Ht'.
  now elim Rge_not_lt with (1 := Ht').
intros P H.
rewrite Hs // in H.
unfold filtermap.
eapply locally_open.
apply open_lt. 2: exact Hx.
move => /= t Ht.
rewrite Hs //.
now apply locally_singleton.
Qed.

Lemma continuous_sqrt_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => sqrt (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => // .
by apply: continuous_sqrt.
Qed.

Lemma continuous_ln x : (0 < x) -> continuous ln x.
Proof.
move => Hxgt0.
apply: ex_derive_continuous.
exists (/x).
apply is_derive_Reals.
exact: derivable_pt_lim_ln.
Qed.

Lemma continuous_Rabs_comp f (x : R) :
  continuous f x -> continuous (fun x0 => Rabs (f x0)) x.
Proof.
move => Hcontfx.
apply: continuous_comp => // .
apply: continuous_Rabs.
Qed.

Lemma is_RInt_translation_add V g a b x Ig :
  @is_RInt V g (a + x) (b + x) Ig ->
  is_RInt (fun y : R => g (y + x)%R) a b Ig.
Proof.
have -> : a + x = (1 * a + x) by rewrite Rmult_1_l.
have -> : b + x = (1 * b + x) by rewrite Rmult_1_l.
move /is_RInt_comp_lin.
apply: is_RInt_ext => t.
now rewrite Rmult_1_l scal_one.
Qed.

Lemma is_RInt_translation_sub V g x a b Ig :
  @is_RInt V g (a - x) (b - x) Ig ->
  is_RInt (fun y : R => g (y - x)) a b Ig.
Proof.
exact: is_RInt_translation_add.
Qed.

Lemma ex_RInt_translation_add V g x a b :
  @ex_RInt V g a b -> @ex_RInt V (fun t => g (t + x)) (a - x) (b - x).
Proof.
intros [Ig HI].
exists Ig.
apply: is_RInt_translation_add.
by rewrite 2!Rplus_assoc Rplus_opp_l 2!Rplus_0_r.
Qed.

Lemma ex_RInt_translation_sub V g a b x :
  @ex_RInt V g a b -> @ex_RInt V (fun t => g (t - x)) (a + x) (b + x).
Proof.
intros [Ig HI].
exists Ig.
apply: is_RInt_translation_sub.
by rewrite /Rminus 2!Rplus_assoc Rplus_opp_r 2!Rplus_0_r.
Qed.

Lemma RInt_translation_add V g a b x :
  ex_RInt g (a + x) (b + x) ->
  @RInt V (fun y : R => g (y + x)%R) a b = RInt g (a + x) (b + x).
Proof.
intros HI.
apply is_RInt_unique.
apply is_RInt_translation_add.
exact: RInt_correct.
Qed.

Lemma RInt_translation_sub V g a b x :
  ex_RInt g (a - x) (b - x) ->
  @RInt V (fun y : R => g (y - x)%R) a b = RInt g (a - x) (b - x).
Proof.
intros HI.
apply is_RInt_unique.
apply is_RInt_translation_sub.
exact: RInt_correct.
Qed.

Lemma ball_to_lra a y eps : ball a eps y <-> a - eps < y < a + eps.
Proof.
split.
- rewrite /ball /= /AbsRing_ball /abs /= /minus; move/Rabs_def2.
  by rewrite  /plus /= /opp /=; lra.
- move => Haeps. rewrite /ball /= /AbsRing_ball /abs /= /minus /= /plus /opp /= .
  rewrite /Rabs. case: Rcase_abs; lra.
Qed.

Lemma Derive_nS f n :
  Derive_n f n.+1 = Derive_n (Derive f) n.
Proof.
elim: n => [//|n IHn].
by rewrite -[in LHS]addn1 /= -addnE addn1 IHn. (* SSReflect trick *)
Qed.

Lemma ex_derive_nSS f n :
  ex_derive_n f n.+2 = ex_derive_n (Derive f) n.+1.
Proof.
case: n => [//|n].
by rewrite /ex_derive_n Derive_nS.
Qed.

Lemma ex_derive_n_is_derive_n :
  forall f n x l, is_derive_n f n x l -> ex_derive_n f n x.
Proof.
intros f [|n] x l.
easy.
rewrite /is_derive_n /ex_derive_n => H.
eexists.
apply H.
Qed.

Lemma ex_derive_is_derive :
  forall (f : R -> R) x l, is_derive f x l -> ex_derive f x.
Proof.
move=> f x l; rewrite /is_derive_n /ex_derive_n => H.
eexists; exact: H.
Qed.

Lemma is_derive_ext_alt f g x (f' : R -> R) (P : R -> Prop) :
  P x ->
  open P ->
  (forall t : R, P t -> f t = g t) ->
  (forall t : R, P t -> is_derive f t (f' t)) ->
  is_derive g x (f' x).
Proof.
move=> Hx HP Hfg Hf.
apply: (is_derive_ext_loc f); last exact: Hf.
exact: (@locally_open _ P _ HP Hfg).
Qed.


(** The following two tactics allows one to easily start proving goals
    that have the form [forall n x, is_derive_n f n x (D n x)]
    or the form [forall n x, P x -> is_derive_n f n x (D n x)]

    Then, we obtain 3 (resp. 4) subgoals that can be proved by relying
    on the [auto_derive] Coquelicot tactic.

    See [is_derive_n_exp] or [is_derive_n_tan] for usage examples.
*)

Ltac help_is_derive_n_whole fresh_n fresh_x :=
  match goal with
  [ |- forall n x, is_derive_n ?f n x (@?D n x) ] =>
  let IHn := fresh "IH" fresh_n in
  case;
  [(*1: f is defined*) try done
  |elim=> [/=|fresh_n IHn] fresh_x;
  [(*2: f is derivable*) (*OPTIONAL: (try auto_derive); try done *)
  |apply: (@is_derive_ext _ _ (D fresh_n.+1) (Derive_n f fresh_n.+1) fresh_x _);
  [let t := fresh "t" in
   by move=> t; rewrite (is_derive_n_unique _ _ _ _ (IHn t))
  |(*3: the invariant holds*)
   clear IHn]]]
  end.

Ltac help_is_derive_n fresh_n fresh_x :=
  match goal with
  [ |- forall n x, @?P x -> is_derive_n ?f n x (@?D n x) ] =>
  let IHn := fresh "IH" fresh_n in
  let Hx := fresh "H" fresh_x in
  case;
  [(*1: f is defined*) try done
  |elim=> [/=|fresh_n IHn] fresh_x;
  [(*2: f is derivable*) (*OPTIONAL: move=> Hx; auto_derive; try done *)
  |move=> Hx;
   apply: (@is_derive_ext_alt
     (D fresh_n.+1) (Derive_n f fresh_n.+1) x (D fresh_n.+2) P Hx);
   clear fresh_x Hx;
  [(*3: P is open*)
  |let t := fresh "t" in
   let Ht := fresh "Ht" in
   by move=> t Ht; rewrite (is_derive_n_unique _ _ _ _ (IHn t Ht))
  |(*4: the invariant holds*)
   clear IHn]]]
  end.

Lemma is_derive_n_exp : forall n x, is_derive_n exp n x (exp x).
Proof.
help_is_derive_n_whole n x.
- by auto_derive; last by rewrite Rmult_1_l.
- by auto_derive; last by rewrite Rmult_1_l.
Qed.

Lemma is_derive_n_pow :
  forall m, (0 < m)%nat -> forall n x,
  is_derive_n (fun x => x ^ m)%R n x
  (\big[Rmult/1%R]_(i < n) INR (m - i) * x ^ (m - n))%R.
Proof.
move=> m Hm; help_is_derive_n_whole n x.
- move=> x; rewrite big1 /= ?(addn0, subn0, Rmult_1_l) //.
  by case.
- auto_derive =>//.
  by rewrite big_ord_recl big_ord0 /= subn0 subn1 /= Rmult_1_l Rmult_1_r.
- auto_derive =>//.
  rewrite [in RHS]big_ord_recr /= /Rdiv; rewrite Rmult_assoc; congr Rmult.
  by rewrite Rmult_1_l !subnS.
Qed.

Lemma is_derive_n_inv_pow :
  forall m, (0 < m)%nat -> forall n x, x <> 0 ->
  is_derive_n (fun x => / x ^ m)%R n x
  (\big[Rmult/1%R]_(i < n) - INR (m + i) / x ^ (m + n))%R.
Proof.
move=> m Hm; help_is_derive_n n x.
- move=> x Hx; rewrite big1 /= ?addn0; first by field; apply: pow_nonzero.
  by case.
- move=> Hx; auto_derive; first by apply: pow_nonzero.
  rewrite big_ord_recl big_ord0 /= addn0 addn1 /= Rmult_1_l Rmult_1_r.
  apply: Rdiv_eq_reg.
  rewrite -(prednK Hm); simpl; ring.
  apply: Rmult_neq0; exact: pow_nonzero.
  by apply: Rmult_neq0; try apply: pow_nonzero.
- exact: open_neq.
- move=> t Ht; auto_derive; first exact: pow_nonzero.
  rewrite [in RHS]big_ord_recr /= /Rdiv; rewrite Rmult_assoc; congr Rmult.
  rewrite Rmult_1_l; apply: Rdiv_eq_reg; first last.
  exact: pow_nonzero.
  apply: Rmult_neq0; exact: pow_nonzero.
  rewrite !addnS /=; ring.
Qed.

Lemma is_derive_n_powerRZ m n x :
  (0 <= m)%Z \/ x <> 0 ->
  is_derive_n (powerRZ^~ m) n x
  (match m with
   | Z0 => if n is O then 1%R else 0%R
   | Z.pos p => \big[Rmult/1%R]_(i < n) INR (Pos.to_nat p - i) *
                x ^ (Pos.to_nat p - n)
   | Z.neg p => \big[Rmult/1%R]_(i < n) - INR (Pos.to_nat p + i) *
                / x ^ (Pos.to_nat p + n)
   end).
Proof.
move=> Hor.
rewrite /powerRZ; case: m Hor => [|p|p] Hor.
- case: n => [|n] //; exact: is_derive_n_const.
- by apply: is_derive_n_pow; apply/ltP/Pos2Nat.is_pos.
- apply: is_derive_n_inv_pow; first exact/ltP/Pos2Nat.is_pos.
  by case: Hor; first by case.
Qed.

Lemma ex_derive_n_powerRZ m n x :
  (0 <= m)%Z \/ x <> 0 ->
  ex_derive_n (powerRZ^~ m) n x.
Proof.
by move=> Hor; eapply ex_derive_n_is_derive_n; eapply is_derive_n_powerRZ.
Qed.

Lemma is_derive_n_Rpower n a x :
  0 < x ->
  is_derive_n (Rpower^~ a) n x
  (\big[Rmult/1%R]_(i < n) (a - INR i) * Rpower x (a - INR n)).
Proof.
move: a x; elim: n => [|n IHn] a x Hx.
  rewrite big_ord0.
  by rewrite /= Rmult_1_l Rminus_0_r.
apply is_derive_Sn.
apply: locally_open x Hx.
apply open_gt.
move => /= x Hx.
eexists.
now apply is_derive_Reals, derivable_pt_lim_power.
apply is_derive_n_ext_loc with (fun x => a * Rpower x (a - 1)).
apply: locally_open x Hx.
apply open_gt.
move => /= x Hx.
apply sym_eq, is_derive_unique.
now apply is_derive_Reals, derivable_pt_lim_power.
rewrite big_ord_recl; rewrite [INR ord0]/= Rminus_0_r Rmult_assoc.
apply is_derive_n_scal_l.
rewrite S_INR.
replace (a - (INR n + 1)) with (a - 1 - INR n) by ring.
rewrite (eq_bigr (P := xpredT) (fun i2 : 'I_n => a - 1 - INR i2)); last first.
move=> [i Hi] _; rewrite plus_INR /=; ring.
exact: IHn.
Qed.

Lemma is_derive_n_inv n x :
  x <> 0 ->
  is_derive_n Rinv n x
  (\big[Rmult/1%R]_(i < n) - INR (1 + i) * / x ^ (1 + n))%R.
Proof.
move=> Hx.
have := is_derive_n_powerRZ (-1) n x (or_intror Hx).
apply: is_derive_n_ext.
by move=> t; rewrite /= Rmult_1_r.
Qed.

Lemma is_derive_n_ln n x :
  0 < x ->
  is_derive_n ln n x
  (match n with
   | 0 => ln x
   | n.+1 => (\big[Rmult/1%R]_(i < n) - INR (1 + i) * / x ^ (1 + n))%R
   end).
Proof.
case: n => [|n] Hx; first done.
apply is_derive_Sn.
apply: locally_open x Hx.
apply open_gt.
move => /= x Hx.
eexists.
now apply is_derive_Reals, derivable_pt_lim_ln.
have := is_derive_n_inv n x (Rgt_not_eq _ _ Hx).
apply: is_derive_n_ext_loc.
apply: locally_open x Hx.
apply open_gt.
move => /= x Hx.
apply sym_eq, is_derive_unique.
now apply is_derive_Reals, derivable_pt_lim_ln.
Qed.

Lemma is_derive_ln x :
  0 < x -> is_derive ln x (/ x)%R.
Proof. move=> H; exact/is_derive_Reals/derivable_pt_lim_ln. Qed.

Lemma is_derive_n_sqrt n x :
  0 < x ->
  is_derive_n sqrt n x
  (\big[Rmult/1%R]_(i < n) (/2 - INR i) * Rpower x (/2 - INR n)).
Proof.
move=> Hx.
have := is_derive_n_Rpower n (/2) x Hx.
apply: is_derive_n_ext_loc.
apply: locally_open x Hx.
apply open_gt.
exact Rpower_sqrt.
Qed.

Lemma is_derive_n_invsqrt n x :
  0 < x ->
  is_derive_n (fun t => / sqrt t) n x
  (\big[Rmult/1%R]_(i < n) (-/2 - INR i) * Rpower x (-/2 - INR n)).
Proof.
move=> Hx.
have := is_derive_n_Rpower n (-/2) x Hx.
apply: is_derive_n_ext_loc.
apply: locally_open x Hx.
apply open_gt.
by move=> x Hx; rewrite Rpower_Ropp Rpower_sqrt.
Qed.

Lemma is_derive_2n_sin n x :
  is_derive_n sin (n + n) x ((-1)^n * sin x).
Proof.
elim: n x => [|n IHn] x.
by rewrite /= Rmult_1_l.
rewrite -addSnnS 2!addSn /=.
apply is_derive_ext with (f := fun x => (-1)^n * cos x).
move => /= {x} x.
apply sym_eq, is_derive_unique.
eapply is_derive_ext.
move => /= {x} x.
apply sym_eq, is_derive_n_unique.
apply IHn.
apply is_derive_scal.
apply is_derive_Reals, derivable_pt_lim_sin.
replace (-1 * (-1)^n * sin x) with ((-1)^n * -sin x) by ring.
apply is_derive_scal.
apply is_derive_Reals, derivable_pt_lim_cos.
Qed.

Lemma is_derive_n_sin n (x : R) :
  is_derive_n sin n x (if odd n then (-1)^n./2 * cos x
                       else ((-1)^n./2 * sin x)).
Proof.
rewrite -{1}(odd_double_half n); case: odd => /=.
2: rewrite -addnn; exact: is_derive_2n_sin.
set n' := n./2.
eapply is_derive_ext.
move => /= {x} x.
apply sym_eq, is_derive_n_unique.
rewrite -addnn; apply: is_derive_2n_sin.
apply is_derive_scal.
apply is_derive_Reals, derivable_pt_lim_sin.
Qed.

Lemma is_derive_2n_cos n x :
  is_derive_n cos (n + n) x ((-1)^n * cos x).
Proof.
elim: n x => [|n IHn] x.
by rewrite /= Rmult_1_l.
rewrite -addSnnS 2!addSn /=.
apply is_derive_ext with (f := fun x => (-1)^n * -sin x).
move => /= {x} x.
apply sym_eq, is_derive_unique.
eapply is_derive_ext.
move => /= {x} x.
apply sym_eq, is_derive_n_unique.
apply IHn.
apply is_derive_scal.
apply is_derive_Reals, derivable_pt_lim_cos.
replace (-1 * (-1)^n * cos x) with ((-1)^n * -cos x) by ring.
apply is_derive_scal.
apply: is_derive_opp.
apply is_derive_Reals, derivable_pt_lim_sin.
Qed.

Lemma is_derive_n_cos n (x : R) :
  is_derive_n cos n x (if odd n then (-1)^(n./2) * - sin x
                       else ((-1)^(n./2) * cos x)).
Proof.
rewrite -{1}(odd_double_half n); case: odd => /=.
2: rewrite -addnn; exact: is_derive_2n_cos.
set n' := n./2.
eapply is_derive_ext.
move => /= {x} x.
apply sym_eq, is_derive_n_unique.
rewrite -addnn; apply: is_derive_2n_cos.
apply is_derive_scal.
apply is_derive_Reals, derivable_pt_lim_cos.
Qed.

Definition is_derive_atan x :
  is_derive atan x (/ (1 + x²)).
Proof.
rewrite Rsqr_pow2.
apply is_derive_Reals, derivable_pt_lim_atan.
Qed.

Definition is_derive_tan x :
  cos x <> 0%R -> is_derive tan x (tan x ^ 2 + 1)%R.
Proof. now intros Hx; unfold tan; auto_derive; trivial; field_simplify. Qed.

Lemma filterlimi_lim_ext_loc {T U} {F G} {FF : Filter F} (f : T -> U) (g : T -> U -> Prop) :
  F (fun x => g x (f x)) ->
  filterlim f F G ->
  filterlimi g F G.
Proof.
intros HF Hf P HP.
generalize (filter_and (fun x => g x (f x)) _ HF (Hf P HP)).
unfold filtermapi.
apply: filter_imp.
intros x [H1 H2].
now exists (f x).
Qed.

Lemma prod_to_single {T U V : UniformSpace} {F: (U -> Prop) -> Prop} {FF : Filter F}
  (G : (V -> Prop) -> Prop) x (f : T -> U -> V) :
  filterlim (fun tu : T * U => f tu.1 tu.2) (filter_prod (at_point x) F) G <->
  filterlim (fun u : U => f x u) F G.
Proof.
split => H P GP.
- rewrite /filtermap.
  destruct (H _ GP) as [Q R HAQ HFR HPf].
  apply: filter_imp HFR => y HRy.
  exact: HPf.
- specialize (H P GP).
  econstructor.
  exact: Logic.eq_refl.
  exact: H.
  by move => t u <-.
Qed.

Lemma prodi_to_single_l {T U V : UniformSpace} {F: (U -> Prop) -> Prop} {FF : Filter F}
  (G : (V -> Prop) -> Prop) x (f : T -> U -> V -> Prop) :
  filterlimi (fun tu : T * U => f tu.1 tu.2) (filter_prod (at_point x) F) G <->
  filterlimi (fun u : U => f x u) F G.
Proof.
split => H P GP.
- rewrite /filtermapi.
  destruct (H _ GP) as [Q R HAQ HFR HPf].
  apply: filter_imp HFR => y HRy.
  exact: HPf.
- specialize (H P GP).
  econstructor.
  exact: Logic.eq_refl.
  exact: H.
  by move => t u <-.
Qed.

Lemma prodi_to_single_r {T U V : UniformSpace} {F: (U -> Prop) -> Prop} {FF : Filter F}
  (G : (V -> Prop) -> Prop) x (f : U -> T -> V -> Prop) :
  filterlimi (fun tu : U * T => f tu.1 tu.2) (filter_prod F (at_point x)) G <->
  filterlimi (fun u : U => f u x) F G.
Proof.
split => H P GP.
- rewrite /filtermapi.
  destruct (H _ GP) as [Q R HAQ HFR HPf].
  apply: filter_imp HAQ => y HRy.
  exact: HPf.
- specialize (H P GP).
  econstructor.
  exact: H.
  exact: Logic.eq_refl.
  move => t u /= .
  by case => y Hy <-; exists y.
Qed.

Lemma is_RInt_gen_exp_infty a lam (Hlam : 0 < lam) :
  is_RInt_gen (fun x => exp (- (lam * x))) (at_point a) (Rbar_locally p_infty) (exp (-(lam * a)) / lam).
Proof.
rewrite /is_RInt_gen.
rewrite prodi_to_single_l.
apply: (filterlimi_lim_ext_loc (* (fun x => - (exp(- lam * x) - exp(-lam * a)) / lam) *)).
  exists a.
  move => x Hx.
  apply: (is_RInt_derive (fun x => - exp (-(lam * x)) / lam)).
    move => x0 Hx0.
    by auto_derive => // ; try field; lra.
  move => x0 Hx0.
  apply: continuous_exp_comp.
  apply: continuous_opp.
  apply: continuous_mult.
    exact: continuous_const.
    exact: continuous_id.

rewrite /=.
apply: (filterlim_ext (fun x => minus (exp (-(lam * a)) / lam) (exp (-(lam * x)) / lam))).
move => x;rewrite /minus plus_comm; congr plus. rewrite /opp /=; field; lra.
rewrite /opp /=; field; lra.
rewrite /minus.
apply: (filterlim_comp _ _ _ (fun x => opp (exp (-(lam * x)) / lam)) (fun x => plus (exp (- (lam * a)) / lam) x) (Rbar_locally p_infty) (locally (0)) (locally (exp (- (lam * a)) / lam))); last first.
  rewrite -[X in (_ _ _ (locally X))]Rplus_0_r.
  apply: (continuous_plus (fun x => exp (-(lam*a)) / lam) (fun x => x) 0).
  exact: continuous_const.
  exact: continuous_id.
  apply: filterlim_comp; last first. rewrite -[0]Ropp_involutive. exact: filterlim_opp.
have -> : - 0 = Rbar_mult (Finite 0) (Finite (/ lam)) by rewrite /=; ring.
rewrite /Rdiv.
apply: (is_lim_mult (fun x => exp (-(lam * x))) (fun x => / lam) p_infty 0 (/ lam)) => // .
  apply: is_lim_comp.
    exact: is_lim_exp_m.
    apply: (is_lim_ext (fun x => (-lam) * x)).
      move => y; ring.
    have -> : m_infty = (Rbar_mult (- lam) p_infty).
      rewrite /Rbar_mult /Rbar_mult'.
      case: (Rle_dec 0 (-lam)) => [Hy1|Hy1] //.
      exfalso; lra.
    apply: (is_lim_mult (fun x => (- lam)) (fun x => x) p_infty (-lam) p_infty) => // .
      exact: is_lim_const.
      rewrite /ex_Rbar_mult; lra.
      exists 0 => // .
exact: is_lim_const.
Qed.

Lemma ex_RInt_gen_Chasles :
  forall {V : NormedModule R_AbsRing} {Fa Fc : (R -> Prop) -> Prop},
  forall {FFa : Filter Fa} {FFc : Filter Fc},
  forall (f : R -> V) (b : R),
  ex_RInt_gen f Fa (at_point b) ->
  ex_RInt_gen f (at_point b) Fc ->
  ex_RInt_gen f Fa Fc.
Proof.
intros V Fa Fc FFa FFc f b [Iab Hab] [Ibc Hbc].
exists (plus Iab Ibc).
now apply is_RInt_gen_Chasles with b.
Qed.

Lemma RInt_gen_Chasles :
  forall {V : CompleteNormedModule R_AbsRing} {Fa Fc : (R -> Prop) -> Prop},
  forall {FFa : ProperFilter' Fa} {FFc : ProperFilter' Fc},
  forall (f : R -> V) (b : R),
  ex_RInt_gen f Fa (at_point b) ->
  ex_RInt_gen f (at_point b) Fc ->
  plus (RInt_gen f Fa (at_point b)) (RInt_gen f (at_point b) Fc) = RInt_gen f Fa Fc.
Proof.
intros V Fa Fc FFa FFc f b Hab Hbc.
apply esym, is_RInt_gen_unique.
apply: is_RInt_gen_Chasles.
now apply RInt_gen_correct.
now apply RInt_gen_correct.
Qed.

Lemma RInt_gen_ext :
  forall {V : CompleteNormedModule R_AbsRing} {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f g : R -> V),
  filter_prod Fa Fb (fun ab =>
    forall x, Rmin (fst ab) (snd ab) < x < Rmax (fst ab) (snd ab) -> f x = g x) ->
  RInt_gen f Fa Fb = RInt_gen g Fa Fb.
Proof.
intros V Fa Fb FFa FFb f g Heq.
apply eq_close.
apply @close_iota.
split.
now apply is_RInt_gen_ext.
apply is_RInt_gen_ext.
revert Heq.
apply filter_imp.
intros [u v] H t Ht.
now rewrite <- H.
Qed.

Lemma RInt_gen_ext_eq :
  forall {V : CompleteNormedModule R_AbsRing} {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter Fa} {FFb : ProperFilter Fb} (f g : R -> V),
  (forall x, f x = g x) ->
  RInt_gen f Fa Fb = RInt_gen g Fa Fb.
Proof.
intros V Fa Fb FFa FFb f g Heq.
apply (RInt_gen_ext f g).
apply filter_forall.
now intros uv x _.
Qed.
