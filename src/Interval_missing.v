Require Export Fcore_Raux.

Lemma Rplus_lt_reg_l :
  forall r r1 r2 : R,
  (r + r1 < r + r2)%R -> (r1 < r2)%R.
Proof.
intros.
solve [ apply Rplus_lt_reg_l with (1 := H) |
        apply Rplus_lt_reg_r with (1 := H) ].
Qed.

Lemma Rplus_lt_reg_r :
  forall r r1 r2 : R,
  (r1 + r < r2 + r)%R -> (r1 < r2)%R.
Proof.
intros.
apply Rplus_lt_reg_l with r.
now rewrite 2!(Rplus_comm r).
Qed.

Lemma Rmult_le_compat_neg_r :
  forall r r1 r2 : R,
  (r <= 0)%R -> (r1 <= r2)%R -> (r2 * r <= r1 * r)%R.
intros.
rewrite (Rmult_comm r2).
rewrite (Rmult_comm r1).
apply Rmult_le_compat_neg_l.
exact H.
exact H0.
Qed.

Lemma Rmult_eq_compat_r :
  forall r r1 r2 : R,
  r1 = r2 -> (r1 * r)%R = (r2 * r)%R.
intros.
rewrite (Rmult_comm r1).
rewrite (Rmult_comm r2).
apply Rmult_eq_compat_l.
exact H.
Qed.

Lemma Rmult_eq_reg_r :
  forall r r1 r2 : R,
  (r1 * r)%R = (r2 * r)%R -> r <> 0%R -> r1 = r2.
intros.
apply Rmult_eq_reg_l with (2 := H0).
do 2 rewrite (Rmult_comm r).
exact H.
Qed.

Lemma Rmin_Rle :
  forall r1 r2 r,
  (Rmin r1 r2 <= r)%R <-> (r1 <= r)%R \/ (r2 <= r)%R.
intros.
unfold Rmin.
split.
case (Rle_dec r1 r2) ; intros.
left. exact H.
right. exact H.
intros [H|H] ; case (Rle_dec r1 r2) ; intros H0.
exact H.
apply Rle_trans with (2 := H).
apply Rlt_le.
apply Rnot_le_lt with (1 := H0).
apply Rle_trans with r2 ; assumption.
exact H.
Qed.

Lemma Rmin_best :
  forall r1 r2 r,
  (r <= r1)%R -> (r <= r2)%R -> (r <= Rmin r1 r2)%R.
intros.
unfold Rmin.
now case (Rle_dec r1 r2).
Qed.

Lemma Rmax_best :
  forall r1 r2 r,
  (r1 <= r)%R -> (r2 <= r)%R -> (Rmax r1 r2 <= r)%R.
intros.
unfold Rmax.
now case (Rle_dec r1 r2).
Qed.

Lemma Rle_Rinv_pos :
  forall x y : R,
  (0 < x)%R -> (x <= y)%R -> (/y <= /x)%R.
intros.
apply Rle_Rinv.
exact H.
apply Rlt_le_trans with x ; assumption.
exact H0.
Qed.

Lemma Rle_Rinv_neg :
  forall x y : R,
  (y < 0)%R -> (x <= y)%R -> (/y <= /x)%R.
intros.
apply Ropp_le_cancel.
repeat rewrite Ropp_inv_permute.
apply Rle_Rinv.
auto with real.
apply Rlt_le_trans with (Ropp y).
auto with real.
auto with real.
auto with real.
apply Rlt_dichotomy_converse.
left. exact H.
apply Rlt_dichotomy_converse.
left.
apply Rle_lt_trans with y ; assumption.
Qed.

Lemma Rmult_le_pos_pos :
  forall x y : R,
  (0 <= x)%R -> (0 <= y)%R -> (0 <= x * y)%R.
exact Rmult_le_pos.
Qed.

Lemma Rmult_le_pos_neg :
  forall x y : R,
  (0 <= x)%R -> (y <= 0)%R -> (x * y <= 0)%R.
intros.
rewrite <- (Rmult_0_r x).
apply Rmult_le_compat_l ; assumption.
Qed.

Lemma Rmult_le_neg_pos :
  forall x y : R,
  (x <= 0)%R -> (0 <= y)%R -> (x * y <= 0)%R.
intros.
rewrite <- (Rmult_0_l y).
apply Rmult_le_compat_r ; assumption.
Qed.

Lemma Rmult_le_neg_neg :
  forall x y : R,
  (x <= 0)%R -> (y <= 0)%R -> (0 <= x * y)%R.
intros.
rewrite <- (Rmult_0_r x).
apply Rmult_le_compat_neg_l ; assumption.
Qed.

Lemma Zpower_pos_powerRZ :
  forall n m,
  IZR (Zpower_pos n m) = powerRZ (IZR n) (Zpos m).
intros.
rewrite Zpower_pos_nat.
simpl.
induction (nat_of_P m).
apply refl_equal.
unfold Zpower_nat.
simpl.
rewrite mult_IZR.
apply Rmult_eq_compat_l.
exact IHn0.
Qed.

Lemma pow_powerRZ (r : R) (n : nat) :
  (r ^ n)%R = powerRZ r (Z_of_nat n).
Proof.
induction n; [easy|simpl].
now rewrite SuccNat2Pos.id_succ.
Qed.

Definition Zlt_0_Zpower_pos := Zpower_pos_gt_0.

Lemma Zlt_0_Zpower :
  forall a b, (0 < a)%Z -> (0 <= b)%Z ->
  (0 < Zpower a b)%Z.
intros a b H.
case b ; intros ; simpl.
exact (refl_equal _).
apply Zlt_0_Zpower_pos.
exact H.
elim H0.
exact (refl_equal _).
Qed.

Lemma Zpower_le_exp_compat :
  forall u a b,
  Zlt 0 u -> Zle a b ->
  (u^a <= u^b)%Z.
intros until 1.
unfold Zpower.
case b ; case a ; intros ;
  try discriminate ;
  try ( elim H0 ; split ; fail ).
apply (Zlt_le_succ 0).
exact (Zlt_0_Zpower u (Zpos p) H H0).
change (Zpower u (Zpos p) <= Zpower u (Zpos p0))%Z.
cutrewrite (Zpos p0 = Zpos p + (Zpos p0 - Zpos p))%Z.
assert (0 <= Zpos p0 - Zpos p)%Z.
apply Zle_minus_le_0.
exact H0.
assert (0 <= Zpos p)%Z.
apply Zlt_le_weak.
apply Zgt_lt.
apply Zgt_pos_0.
rewrite Zpower_exp ; [ idtac | exact (Zle_ge _ _ H2) | exact (Zle_ge _ _ H1) ].
pattern (u ^ Zpos p)%Z at 1 ; rewrite <- Zmult_1_r.
apply Zmult_le_compat_l.
apply (Zlt_le_succ 0).
exact (Zlt_0_Zpower _ _ H H1).
apply Zlt_le_weak.
apply (Zlt_0_Zpower _ _ H H2).
ring.
apply Zlt_le_weak.
apply Zlt_0_Zpower_pos.
exact H.
Qed.

Lemma Rabs_def1_le :
  forall x a,
  (x <= a)%R -> (-a <= x)%R ->
  (Rabs x <= a)%R.
intros.
case (Rcase_abs x) ; intros.
rewrite (Rabs_left _ r).
rewrite <- (Ropp_involutive a).
apply Ropp_le_contravar.
exact H0.
rewrite (Rabs_right _ r).
exact H.
Qed.

Lemma Rabs_def2_le :
  forall x a,
  (Rabs x <= a)%R ->
  (-a <= x <= a)%R.
intros x a H.
assert (0 <= a)%R.
apply Rle_trans with (2 := H).
apply Rabs_pos.
generalize H. clear H.
unfold Rabs.
case (Rcase_abs x) ; split.
rewrite <- (Ropp_involutive x).
apply Ropp_le_contravar.
exact H.
apply Rlt_le.
apply Rlt_le_trans with (1 := r).
exact H0.
generalize (Rge_le _ _ r).
clear r.
intro.
apply Rle_trans with (2 := H1).
rewrite <- Ropp_0.
apply Ropp_le_contravar.
exact H0.
exact H.
Qed.

Theorem derivable_pt_lim_eq :
  forall f g,
 (forall x, f x = g x) ->
  forall x l,
  derivable_pt_lim f x l -> derivable_pt_lim g x l.
intros f g H x l.
unfold derivable_pt_lim.
intros.
destruct (H0 _ H1) as (delta, H2).
exists delta.
intros.
do 2 rewrite <- H.
apply H2 ; assumption.
Qed.

Definition locally_true x (P : R -> Prop) :=
  exists delta, (0 < delta)%R /\
  forall h, (Rabs h < delta)%R -> P (x + h)%R.

Theorem derivable_pt_lim_eq_locally :
  forall f g x l,
  locally_true x (fun v => f v = g v) ->
  derivable_pt_lim f x l -> derivable_pt_lim g x l.
intros f g x l (delta1, (Hd, Heq)) Hf eps Heps.
destruct (Hf eps Heps) as (delta2, H0).
clear Hf.
assert (0 < Rmin delta1 delta2)%R.
apply Rmin_pos.
exact Hd.
exact (cond_pos delta2).
exists (mkposreal (Rmin delta1 delta2) H).
intros.
rewrite <- Heq.
pattern x at 2 ; rewrite <- Rplus_0_r.
rewrite <- Heq.
rewrite Rplus_0_r.
apply H0.
exact H1.
apply Rlt_le_trans with (1 := H2).
simpl.
apply Rmin_r.
rewrite Rabs_R0.
exact Hd.
apply Rlt_le_trans with (1 := H2).
simpl.
apply Rmin_l.
Qed.

Theorem locally_true_and :
  forall P Q x,
  locally_true x P ->
  locally_true x Q ->
  locally_true x (fun x => P x /\ Q x).
intros P Q x HP HQ.
destruct HP as (e1, (He1, H3)).
destruct HQ as (e2, (He2, H4)).
exists (Rmin e1 e2).
split.
apply Rmin_pos ; assumption.
intros.
split.
apply H3.
apply Rlt_le_trans with (1 := H).
apply Rmin_l.
apply H4.
apply Rlt_le_trans with (1 := H).
apply Rmin_r.
Qed.

Theorem locally_true_imp :
  forall P Q : R -> Prop,
 (forall x, P x -> Q x) ->
  forall x,
  locally_true x P ->
  locally_true x Q.
intros P Q H x (d, (Hd, H0)).
exists d.
split.
exact Hd.
intros.
apply H.
apply H0.
exact H1.
Qed.

Theorem continuity_pt_lt :
  forall f x y,
  (f x < y)%R ->
  continuity_pt f x ->
  locally_true x (fun u => (f u < y)%R).
intros.
assert (0 < y - f x)%R.
apply Rplus_lt_reg_l with (f x).
rewrite Rplus_0_r.
replace (f x + (y - f x))%R with y. 2: ring.
exact H.
destruct (H0 _ H1) as (delta, (Hdelta, H2)).
clear H0.
exists delta.
split.
exact Hdelta.
intros.
case (Req_dec h 0) ; intro H3.
rewrite H3.
rewrite Rplus_0_r.
exact H.
generalize (H2 (x + h)%R). clear H2.
unfold R_met, R_dist, D_x, no_cond.
simpl.
intro.
apply Rplus_lt_reg_r with (- f x)%R.
apply Rle_lt_trans with (1 := RRle_abs (f (x + h) - f x)%R).
apply H2.
assert (x + h - x = h)%R. ring.
split.
split.
exact I.
intro H5.
elim H3.
rewrite <- H4.
rewrite <- H5.
exact (Rplus_opp_r _).
rewrite H4.
exact H0.
Qed.

Theorem continuity_pt_gt :
  forall f x y,
  (y < f x)%R ->
  continuity_pt f x ->
  locally_true x (fun u => (y < f u)%R).
intros.
generalize (Ropp_lt_contravar _ _ H).
clear H. intro H.
generalize (continuity_pt_opp _ _ H0).
clear H0. intro H0.
destruct (continuity_pt_lt (opp_fct f) _ _ H H0) as (delta, (Hdelta, H1)).
exists delta.
split.
exact Hdelta.
intros.
apply Ropp_lt_cancel.
exact (H1 _ H2).
Qed.

Theorem continuity_pt_ne :
  forall f x y,
  f x <> y ->
  continuity_pt f x ->
  locally_true x (fun u => f u <> y).
intros.
destruct (Rdichotomy _ _ H) as [H1|H1].
destruct (continuity_pt_lt _ _ _ H1 H0) as (delta, (Hdelta, H2)).
exists delta.
split.
exact Hdelta.
intros.
apply Rlt_not_eq.
exact (H2 _ H3).
destruct (continuity_pt_gt _ _ _ H1 H0) as (delta, (Hdelta, H2)).
exists delta.
split.
exact Hdelta.
intros.
apply Rgt_not_eq.
exact (H2 _ H3).
Qed.

Theorem derivable_pt_lim_tan :
  forall x,
  (cos x <> 0)%R ->
  derivable_pt_lim tan x (1 + Rsqr (tan x))%R.
intros x Hx.
change (derivable_pt_lim (sin/cos) x (1 + Rsqr (tan x))%R).
replace (1 + Rsqr (tan x))%R with ((cos x * cos x - (-sin x) * sin x) / Rsqr (cos x))%R.
apply derivable_pt_lim_div.
apply derivable_pt_lim_sin.
apply derivable_pt_lim_cos.
exact Hx.
unfold Rsqr, tan.
field.
exact Hx.
Qed.

Theorem derivable_pt_lim_atan :
  forall x,
  derivable_pt_lim atan x (Rinv (1 + Rsqr x)).
Proof.
intros x.
apply derive_pt_eq_1 with (pr := derivable_pt_atan x).
rewrite <- (Rmult_1_l (Rinv _)).
apply derive_pt_atan.
Qed.

Definition connected (P : R -> Prop) :=
  forall x y, P x -> P y ->
  forall z, (x <= z <= y)%R -> P z.

Definition singleton x y :=
  match Req_EM_T x y with
  | left _ => True
  | right _ => False
  end.

Definition union P Q (x : R) :=
  P x \/ Q x.

Definition intersection P Q (x : R) :=
  P x /\ Q x.

Definition hull P x :=
  exists u, exists v, P u /\ P v /\ (u <= x <= v)%R.

Lemma hull_connected :
  forall P, connected (hull P).
intros P a b (ua, (_, (Hua, (_, (Ha, _))))) (_, (vb, (_, (Hvb, (_, Hb))))) c Hc.
exists ua.
exists vb.
refine (conj Hua (conj Hvb (conj _ _))).
exact (Rle_trans _ _ _ Ha (proj1 Hc)).
exact (Rle_trans _ _ _ (proj2 Hc) Hb).
Qed.

Theorem derivable_pos_imp_increasing :
  forall f f' dom,
  connected dom ->
 (forall x, dom x -> derivable_pt_lim f x (f' x) /\ (0 <= f' x)%R) ->
  forall u v, dom u -> dom v -> (u <= v)%R -> (f u <= f v)%R.
intros f f' dom Hdom Hd u v Hu Hv [Huv|Huv].
assert (forall w, (u <= w <= v)%R -> derivable_pt_lim f w (f' w)).
intros w Hw.
refine (proj1 (Hd _ _)).
exact (Hdom _ _ Hu Hv _ Hw).
destruct (MVT_cor2 _ _ _ _ Huv H) as (w, (Hw1, Hw2)).
replace (f v) with (f u + (f v - f u))%R by ring.
rewrite Hw1.
pattern (f u) at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
apply Rmult_le_pos.
refine (proj2 (Hd _ _)).
refine (Hdom _ _ Hu Hv _ _).
exact (conj (Rlt_le _ _ (proj1 Hw2)) (Rlt_le _ _ (proj2 Hw2))).
rewrite <- (Rplus_opp_r u).
unfold Rminus.
apply Rplus_le_compat_r.
exact (Rlt_le _ _ Huv).
rewrite Huv.
apply Rle_refl.
Qed.

Theorem derivable_neg_imp_decreasing :
  forall f f' dom,
  connected dom ->
 (forall x, dom x -> derivable_pt_lim f x (f' x) /\ (f' x <= 0)%R) ->
  forall u v, dom u -> dom v -> (u <= v)%R -> (f v <= f u)%R.
intros f f' dom Hdom Hd u v Hu Hv Huv.
apply Ropp_le_cancel.
refine (derivable_pos_imp_increasing (opp_fct f) (opp_fct f') _ Hdom _ _ _ Hu Hv Huv).
intros.
destruct (Hd x H) as (H1, H2).
split.
apply derivable_pt_lim_opp with (1 := H1).
rewrite <- Ropp_0.
apply Ropp_le_contravar with (1 := H2).
Qed.

Theorem derivable_zero_imp_constant :
  forall f dom,
  connected dom ->
 (forall x, dom x -> derivable_pt_lim f x R0) ->
  forall u v, dom u -> dom v -> (f u = f v)%R.
intros f dom Hdom Hd.
(* generic case *)
assert (forall u v, dom u -> dom v -> (u <= v)%R -> f u = f v).
intros u v Hu Hv Huv.
apply Rle_antisym.
apply (derivable_pos_imp_increasing f (fct_cte R0)) with (1 := Hdom) ; try assumption.
intros.
split.
now apply Hd.
apply Rle_refl.
apply (derivable_neg_imp_decreasing f (fct_cte R0)) with (1 := Hdom) ; try assumption.
intros.
split.
now apply Hd.
apply Rle_refl.
(* . *)
intros u v Hu Hv.
destruct (Rle_or_lt u v) as [Huv|Huv].
now apply H.
generalize (Rlt_le _ _ Huv).
intros Huv2.
apply sym_eq.
now apply H.
Qed.

Lemma alternated_series_ineq' :
  forall u l,
  Un_decreasing u ->
  Un_cv u 0 ->
  Un_cv (fun n => sum_f_R0 (tg_alt u) n) l ->
  forall n,
  (0 <= (-1)^(S n) * (l - sum_f_R0 (tg_alt u) n) <= u (S n))%R.
Proof.
intros u l Du Cu Cl n.
destruct (Even.even_or_odd n) as [H|H].
- destruct (Div2.even_2n n H) as [p Hp].
  rewrite NPeano.double_twice in Hp.
  destruct (alternated_series_ineq u l p Du Cu Cl) as [H1 H2].
  rewrite Hp, pow_1_odd.
  split.
  + rewrite Ropp_mult_distr_l_reverse, Rmult_1_l.
    apply Ropp_0_ge_le_contravar.
    now apply Rle_ge, Rle_minus.
  + apply Rplus_le_reg_r with (- sum_f_R0 (tg_alt u) (2 * p))%R.
    ring_simplify.
    replace (- sum_f_R0 (tg_alt u) (2 * p) + u (S (2 * p)))%R
      with (- (sum_f_R0 (tg_alt u) (2 * p) + (-1) * u (S (2 * p))))%R by ring.
    rewrite <- (pow_1_odd p).
    now apply Ropp_le_contravar.
- destruct (Div2.odd_S2n n H) as [p Hp].
  rewrite NPeano.double_twice in Hp.
  assert (H0: S (S (2 * p)) = 2 * (p + 1)) by ring.
  rewrite Hp.
  rewrite H0 at 1 2.
  rewrite pow_1_even, Rmult_1_l.
  split.
  + apply Rle_0_minus.
    now apply alternated_series_ineq.
  + apply Rplus_le_reg_l with (sum_f_R0 (tg_alt u) (S (2 * p))).
    ring_simplify.
    rewrite <- (Rmult_1_l (u (S (S (2 * p))))).
    rewrite <- (pow_1_even (p + 1)).
    rewrite <- H0.
    destruct (alternated_series_ineq u l (p + 1) Du Cu Cl) as [_ H1].
    now rewrite <- H0 in H1.
Qed.

Lemma Un_decreasing_exp :
  forall x : R,
  (0 <= x <= 1)%R ->
  Un_decreasing (fun n => / INR (fact n) * x ^ n)%R.
Proof.
intros x Hx n.
change (fact (S n)) with (S n * fact n).
rewrite mult_INR.
rewrite Rinv_mult_distr.
simpl pow.
rewrite <- (Rmult_1_r (/ _ * _ ^ n)).
replace (/ INR (S n) * / INR (fact n) * (x * x ^ n))%R
  with (/ INR (fact n) * x ^ n * (/ INR (S n) * x))%R by ring.
apply Rmult_le_compat_l.
apply Rmult_le_pos.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_fact.
now apply pow_le.
rewrite <- (Rmult_1_r 1).
apply Rmult_le_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_Sn.
apply Hx.
rewrite <- Rinv_1.
apply Rle_Rinv_pos.
apply Rlt_0_1.
apply (le_INR 1).
apply le_n_S, le_0_n.
apply Hx.
now apply not_0_INR.
apply INR_fact_neq_0.
Qed.

Lemma Un_decreasing_cos :
  forall x : R,
  (Rabs x <= 1)%R ->
  Un_decreasing (fun n => / INR (fact (2 * n)) * x ^ (2 * n))%R.
Proof.
intros x Hx n.
replace (2 * S n) with (2 + 2 * n) by ring.
rewrite pow_add.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
rewrite pow_sqr.
apply pow_le.
apply Rle_0_sqr.
change (fact (2 + 2 * n)) with ((2 + 2 * n) * ((1 + 2 * n) * fact (2 * n))).
rewrite mult_assoc, mult_comm.
rewrite mult_INR.
rewrite <- (Rmult_1_r (/ INR (fact _))).
rewrite Rinv_mult_distr.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_fact.
rewrite <- (Rmult_1_r 1).
apply Rmult_le_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_Sn.
unfold pow.
rewrite Rmult_1_r.
apply Rle_0_sqr.
rewrite <- Rinv_1.
apply Rle_Rinv_pos.
apply Rlt_0_1.
apply (le_INR 1).
apply le_n_S, le_0_n.
replace R1 with (1 * (1 * 1))%R by ring.
apply pow_maj_Rabs with (1 := Hx).
apply INR_fact_neq_0.
now apply not_0_INR.
Qed.

Lemma Un_cv_subseq :
  forall (u : nat -> R) (f : nat -> nat) (l : R),
  (forall n, f n < f (S n)) ->
  Un_cv u l -> Un_cv (fun n => u (f n)) l.
Proof.
intros u f l Hf Cu eps He.
destruct (Cu eps He) as [N HN].
exists N.
intros n Hn.
apply HN.
apply le_trans with (1 := Hn).
clear -Hf.
induction n.
apply le_0_n.
specialize (Hf n).
omega.
Qed.

Definition sinc (x : R) := projT1 (exist_sin (Rsqr x)).

Lemma sin_sinc :
  forall x,
  sin x = (x * sinc x)%R.
Proof.
intros x.
unfold sin, sinc.
now case exist_sin.
Qed.

Lemma sinc_0 :
  sinc 0 = R1.
Proof.
unfold sinc.
case exist_sin.
simpl.
unfold sin_in.
intros y Hy.
apply uniqueness_sum with (1 := Hy).
intros eps He.
exists 1.
intros n Hn.
rewrite (tech2 _ 0) by easy.
simpl sum_f_R0 at 1.
rewrite sum_eq_R0.
unfold R_dist, sin_n.
simpl.
replace (1 / 1 * 1 + 0 - 1)%R with R0 by field.
now rewrite Rabs_R0.
clear.
intros m _.
rewrite Rsqr_0, pow_i.
apply Rmult_0_r.
apply lt_0_Sn.
Qed.

Lemma Un_decreasing_sinc :
  forall x : R,
  (Rabs x <= 1)%R ->
  Un_decreasing (fun n : nat => (/ INR (fact (2 * n + 1)) * x ^ (2 * n)))%R.
Proof.
intros x Hx n.
replace (2 * S n) with (2 + 2 * n) by ring.
rewrite pow_add.
rewrite <- Rmult_assoc.
apply Rmult_le_compat_r.
rewrite pow_sqr.
apply pow_le.
apply Rle_0_sqr.
change (fact (2 + 2 * n + 1)) with ((2 + 2 * n + 1) * ((1 + 2 * n + 1) * fact (2 * n + 1))).
rewrite mult_assoc, mult_comm.
rewrite mult_INR.
rewrite <- (Rmult_1_r (/ INR (fact _))).
rewrite Rinv_mult_distr.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_fact.
rewrite <- (Rmult_1_r 1).
apply Rmult_le_compat.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply (lt_INR 0).
apply lt_O_Sn.
unfold pow.
rewrite Rmult_1_r.
apply Rle_0_sqr.
rewrite <- Rinv_1.
apply Rle_Rinv_pos.
apply Rlt_0_1.
apply (le_INR 1).
apply le_n_S, le_0_n.
replace R1 with (1 * (1 * 1))%R by ring.
apply pow_maj_Rabs with (1 := Hx).
apply INR_fact_neq_0.
now apply not_0_INR.
Qed.

Lemma atan_plus_PI4 :
  forall x, (-1 < x)%R ->
  (atan ((x - 1) / (x + 1)) + PI / 4)%R = atan x.
Proof.
intros x Hx.
assert (H1: ((x - 1) / (x + 1) < 1)%R).
  apply Rmult_lt_reg_r with (x + 1)%R.
  Fourier.fourier.
  unfold Rdiv.
  rewrite Rmult_1_l, Rmult_assoc, Rinv_l, Rmult_1_r.
  Fourier.fourier.
  apply Rgt_not_eq.
  Fourier.fourier.
assert (H2: (- PI / 2 < atan ((x - 1) / (x + 1)) + PI / 4 < PI / 2)%R).
  split.
  rewrite <- (Rplus_0_r (- PI / 2)).
  apply Rplus_lt_compat.
  apply atan_bound.
  apply PI4_RGT_0.
  apply Rplus_lt_reg_r with (-(PI / 4))%R.
  rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
  replace (PI/2 + - (PI/4))%R with (PI/4)%R by field.
  rewrite <- atan_1.
  now apply atan_increasing.
apply tan_is_inj.
exact H2.
apply atan_bound.
rewrite atan_right_inv.
rewrite tan_plus.
rewrite atan_right_inv.
rewrite tan_PI4.
field.
split.
apply Rgt_not_eq.
Fourier.fourier.
apply Rgt_not_eq.
ring_simplify.
apply Rlt_0_2.
apply Rgt_not_eq, cos_gt_0.
unfold Rdiv.
rewrite <- Ropp_mult_distr_l_reverse.
apply atan_bound.
apply atan_bound.
rewrite cos_PI4.
apply Rgt_not_eq.
unfold Rdiv.
rewrite Rmult_1_l.
apply Rinv_0_lt_compat.
apply sqrt_lt_R0.
apply Rlt_0_2.
apply Rgt_not_eq, cos_gt_0.
unfold Rdiv.
now rewrite <- Ropp_mult_distr_l_reverse.
apply H2.
rewrite tan_PI4, Rmult_1_r.
rewrite atan_right_inv.
apply Rgt_not_eq.
now apply Rgt_minus.
Qed.
