Require Import Reals Psatz.
Require Import Coquelicot.
Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool Ssreflect.eqtype Ssreflect.ssrnat Ssreflect.seq Ssreflect.fintype MathComp.bigop.
Require Import Rstruct Interval_missing reals_tac.

Section MissingContinuity.

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

End MissingContinuity.

Section MissingIntegrability.

Lemma ex_RInt_Rabs f a b : ex_RInt f a b -> ex_RInt (fun x => Rabs (f x)) a b.
move => Hintfx.
by apply: ex_RInt_norm.
Qed.

End MissingIntegrability.


Section Integrability.

Variables (V : CompleteNormedModule R_AbsRing) (g : R -> V) (a b c d : R).

Lemma ex_RInt_Chasles_sub :
 a <= b -> b <= c -> c <= d -> ex_RInt g a d -> ex_RInt g b c.
Proof.
move=> leab lebc lecd hiad; apply: (ex_RInt_Chasles_1 _ _ _ d) => //.
by apply: (ex_RInt_Chasles_2 _ a) => //; split=> //; apply: (Rle_trans _ c).
Qed.

End Integrability.

(* Below : a couple of helper lemmas about maj/min of integrals *)
(* We should probably also add the more general case of ra <= rb *)
Section IntegralEstimation.

Variables (f : R -> R) (ra rb : R).

Hypothesis ltab : ra < rb.

Hypothesis fint : ex_RInt f ra rb.

Lemma RInt_le_r (u : R) :
 (forall x : R, ra <= x <= rb -> f x <= u) -> RInt f ra rb / (rb - ra) <= u.
Proof.
move=> hfu; apply/Rle_div_l;first by apply: Rgt_minus.
have -> : u * (rb - ra) = RInt (fun _ => u) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
  exact: ex_RInt_const.
move => x Hx; apply: hfu.
split.
- exact: (Rlt_le _ _ (proj1 Hx)).
- exact: (Rlt_le _ _ (proj2 Hx)).
Qed.

Lemma RInt_le_l (l : R) :
  (forall x : R, ra <= x <= rb -> l <= f x) -> l <= RInt f ra rb / (rb - ra).
Proof.
move=> hfl; apply/Rle_div_r; first by apply: Rgt_minus.
have -> : l * (rb - ra) = RInt (fun _ => l) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
move => x Hx; apply: hfl.
split.
- exact: (Rlt_le _ _ (proj1 Hx)).
- exact: (Rlt_le _ _ (proj2 Hx)).
Qed.

Lemma RInt_le_r_strict (u : R) :
 (forall x : R, ra < x < rb -> f x <= u) -> RInt f ra rb / (rb - ra) <= u.
Proof.
move=> hfu; apply/Rle_div_l;first by apply: Rgt_minus.
have -> : u * (rb - ra) = RInt (fun _ => u) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
Qed.

Lemma RInt_le_l_strict (l : R) :
  (forall x : R, ra < x < rb -> l <= f x) -> l <= RInt f ra rb / (rb - ra).
Proof.
move=> hfl; apply/Rle_div_r; first by apply: Rgt_minus.
have -> : l * (rb - ra) = RInt (fun _ => l) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
Qed.

End IntegralEstimation.

(********************************************************************)
(** The following support results deal with "iterated derivatives". *)
(********************************************************************)

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

Lemma is_derive_nSS f n l :
  is_derive_n f n.+2 l = is_derive_n (Derive f) n.+1 l.
Proof.
case: n => [//|n].
by rewrite /is_derive_n Derive_nS.
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

(*
(* First attempt regarding automation: *)

Ltac start_derive_n n x :=
  let IHn := fresh "IHn" in
  let Hx := fresh "Hx" in
  case: n x;
  [try done|elim=> [/=|n IHn] x;
           [try (move=> Hx); auto_derive; try done|idtac]].
*)

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

    See [is_derive_n_exp] or [is_derive_n_inv_pow] for usage examples.
*)

Ltac help_is_derive_n_whole :=
  match goal with
  [ |- forall n x, is_derive_n ?f n x (@?D n x) ] =>
  let n := fresh "n" in
  let x := fresh "x" in
  let IHn := fresh "IHn" in
  case;
  [(*1: f is defined*) try done
  |elim=> [/=|n IHn] x;
  [(*2: f is derivable*) (*OPTIONAL: (try auto_derive); try done *)
  |apply: (@is_derive_ext _ _ (D n.+1) (Derive_n f n.+1) x _);
  [let t := fresh "t" in
   by move=> t; rewrite (is_derive_n_unique _ _ _ _ (IHn t))
  |(*3: the invariant holds*)]]]
  end.

Ltac help_is_derive_n :=
  match goal with
  [ |- forall n x, @?P x -> is_derive_n ?f n x (@?D n x) ] =>
  let n := fresh "n" in
  let x := fresh "x" in
  let IHn := fresh "IHn" in
  let Hx := fresh "Hx" in
  case;
  [(*1: f is defined*) try done
  |elim=> [/=|n IHn] x;
  [(*2: f is derivable*) (*OPTIONAL: move=> Hx; auto_derive; try done *)
  |move=> Hx;
   apply: (@is_derive_ext_alt (D n.+1) (Derive_n f n.+1) x (D n.+2) P Hx);
   clear x Hx;
  [(*3: P is open*)
  |let t := fresh "t" in
   let Ht := fresh "Ht" in
   by move=> t Ht; rewrite (is_derive_n_unique _ _ _ _ (IHn t Ht))
  |(*4: the invariant holds*)]]]
  end.

Lemma is_derive_n_exp : forall n x, is_derive_n exp n x (exp x).
Proof.
help_is_derive_n_whole.
- by auto_derive; last by rewrite Rmult_1_l.
- by auto_derive; last by rewrite Rmult_1_l.
Qed.

(* TODO: Compléter à partir des anciennes preuves de derive_compl.v
   PUIS RENOMMER LES LEMMES EN [is_derive_n_*]
*)

Lemma is_derive_n_pow :
  forall m, (0 < m)%N -> forall n x,
  is_derive_n (fun x => x ^ m)%R n x
  (\big[Rmult/1%R]_(i < n) INR (m - i) * x ^ (m - n))%R.
Proof.
move=> m Hm; help_is_derive_n_whole.
- move=> x; rewrite big1 /= ?(addn0, subn0, Rmult_1_l) //.
  by case.
- auto_derive =>//.
  by rewrite big_ord_recl big_ord0 /= subn0 subn1 /= Rmult_1_l Rmult_1_r.
- auto_derive =>//.
  rewrite [in RHS]big_ord_recr /= /Rdiv; rewrite Rmult_assoc; congr Rmult.
  by rewrite Rmult_1_l !subnS.
Qed.

Lemma is_derive_n_inv_pow :
  forall m, (0 < m)%N -> forall n x, x <> 0 ->
  is_derive_n (fun x => / x ^ m)%R n x
  (\big[Rmult/1%R]_(i < n) - INR (m + i) / x ^ (m + n))%R.
Proof.
move=> m Hm; help_is_derive_n.
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

Lemma Zneg_not_ge0 p : (0 <= Z.neg p)%Z -> False.
Proof. by have /Z.lt_nge := Zlt_neg_0 p. Qed.

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
  by case: Hor; first by move/Zneg_not_ge0.
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

Lemma ex_derive_n_Rpower a n x :
  0 < x -> ex_derive_n (Rpower ^~ a) n x.
Proof.
by move=> Hx; apply: ex_derive_n_is_derive_n (is_derive_n_Rpower n a x Hx).
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

Definition is_derive_tan x :
  cos x <> 0%R -> is_derive tan x (tan x ^ 2 + 1)%R.
Proof. now intros Hx; unfold tan; auto_derive; trivial; field_simplify. Qed.

Lemma ex_derive_n_atan :
  forall n (x : R), ex_derive_n atan n x.
Proof.
Admitted.

Lemma ex_derive_n_tan :
  forall n x, cos x <> 0 -> ex_derive_n tan n x.
Proof.
Admitted.
