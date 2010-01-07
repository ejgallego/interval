Require Import Reals.
Require Import ZArith.

Lemma Rplus_le_reg_r :
  forall r r1 r2 : R,
  (r1 + r <= r2 + r)%R -> (r1 <= r2)%R.
intros.
apply Rplus_le_reg_l with r.
do 2 rewrite (Rplus_comm r).
exact H.
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

Lemma minus_IZR :
  forall n m : Z,
  IZR (n - m) = (IZR n - IZR m)%R.
intros.
unfold Zminus.
rewrite plus_IZR.
rewrite Ropp_Ropp_IZR.
apply refl_equal.
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

Lemma Zlt_0_Zpower_pos :
  forall a b, (0 < a)%Z ->
  (0 < Zpower_pos a b)%Z.
intros.
apply lt_IZR.
rewrite Zpower_pos_powerRZ.
apply powerRZ_lt.
apply (IZR_lt 0).
exact H.
Qed.

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

Fixpoint P2R (p : positive) :=
  match p with
  | xH => 1%R
  | xO xH => 2%R
  | xO t => (2 * P2R t)%R
  | xI xH => 3%R
  | xI t => (1 + 2 * P2R t)%R
  end.

Definition Z2R n :=
  match n with
  | Zpos p => P2R p
  | Zneg p => Ropp (P2R p)
  | Z0 => R0
  end.

Lemma P2R_INR :
  forall n, P2R n = INR (nat_of_P n).
induction n ; simpl ; try (
  rewrite IHn ;
  rewrite <- (mult_INR 2) ;
  rewrite <- (nat_of_P_mult_morphism 2) ;
  change (2 * n)%positive with (xO n)).
(* xI *)
rewrite (Rplus_comm 1).
change (nat_of_P (xO n)) with (Pmult_nat n 2).
case n ; intros ; simpl ; try apply refl_equal.
case (Pmult_nat p 4) ; intros ; try apply refl_equal.
rewrite Rplus_0_l.
apply refl_equal.
apply Rplus_comm.
(* xO *)
case n ; intros ; apply refl_equal.
(* xH *)
apply refl_equal.
Qed.

Lemma Z2R_IZR :
  forall n, Z2R n = IZR n.
intro.
case n ; intros ; simpl.
apply refl_equal.
apply P2R_INR.
apply Ropp_eq_compat.
apply P2R_INR.
Qed.

Lemma plus_Z2R :
  forall m n, (Z2R (m + n) = Z2R m + Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply plus_IZR.
Qed.

Lemma minus_Z2R :
  forall m n, (Z2R (m - n) = Z2R m - Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply minus_IZR.
Qed.

Lemma mult_Z2R :
  forall m n, (Z2R (m * n) = Z2R m * Z2R n)%R.
intros.
repeat rewrite Z2R_IZR.
apply mult_IZR.
Qed.

Lemma le_Z2R :
  forall m n, (Z2R m <= Z2R n)%R -> (m <= n)%Z.
intros m n.
repeat rewrite Z2R_IZR.
apply le_IZR.
Qed.

Lemma Z2R_le :
  forall m n, (m <= n)%Z -> (Z2R m <= Z2R n)%R.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_le.
Qed.

Lemma lt_Z2R :
  forall m n, (Z2R m < Z2R n)%R -> (m < n)%Z.
intros m n.
repeat rewrite Z2R_IZR.
apply lt_IZR.
Qed.

Lemma Z2R_lt :
  forall m n, (m < n)%Z -> (Z2R m < Z2R n)%R.
intros m n.
repeat rewrite Z2R_IZR.
apply IZR_lt.
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
apply Rplus_lt_reg_r with (f x).
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
do 2 rewrite (Rplus_comm (- f x)).
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

Definition Ratan_seq x :=
  fun n => (x ^ (2 * n + 1) / INR (2 * n + 1))%R.

Lemma Ratan_seq_decreasing :
  forall x, (0 <= x <= 1)%R ->
  Un_decreasing (Ratan_seq x).
intros x Hx n.
unfold Ratan_seq, Rdiv.
apply Rmult_le_compat.
apply pow_le.
exact (proj1 Hx).
apply Rlt_le.
apply Rinv_0_lt_compat.
apply lt_INR_0.
omega.
destruct (proj1 Hx) as [Hx1|Hx1].
destruct (proj2 Hx) as [Hx2|Hx2].
(* . 0 < x < 1 *)
rewrite <- (Rinv_involutive x).
assert (/ x <> 0)%R by auto with real.
repeat rewrite <- Rinv_pow with (1 := H).
apply Rlt_le.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat ; apply pow_lt ; auto with real.
apply Rlt_pow.
rewrite <- Rinv_1.
apply Rinv_lt_contravar.
rewrite Rmult_1_r.
exact Hx1.
exact Hx2.
omega.
apply Rgt_not_eq.
exact Hx1.
(* . x = 1 *)
rewrite Hx2.
do 2 rewrite pow1.
apply Rle_refl.
(* . x = 0 *)
rewrite <- Hx1.
do 2 (rewrite pow_i ; [ idtac | omega ]).
apply Rle_refl.
apply Rlt_le.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat ; apply lt_INR_0 ; omega.
apply lt_INR.
omega.
Qed.

Lemma Ratan_seq_converging :
  forall x, (0 <= x <= 1)%R ->
  Un_cv (Ratan_seq x) 0.
intros x Hx eps Heps.
destruct (archimed (/ eps)) as (HN,_).
assert (0 < up (/ eps))%Z.
apply lt_IZR.
apply Rlt_trans with (2 := HN).
apply Rinv_0_lt_compat.
exact Heps.
case_eq (up (/ eps)) ;
  intros ; rewrite H0 in H ; try discriminate H.
rewrite H0 in HN.
simpl in HN.
pose (N := nat_of_P p).
fold N in HN.
clear H H0.
exists N.
intros n Hn.
unfold R_dist.
rewrite Rminus_0_r.
unfold Ratan_seq.
rewrite Rabs_right.
apply Rle_lt_trans with (1 ^ (2 * n + 1) / INR (2 * n + 1))%R.
unfold Rdiv.
apply Rmult_le_compat_r.
apply Rlt_le.
apply Rinv_0_lt_compat.
apply lt_INR_0.
omega.
apply pow_incr.
exact Hx.
rewrite pow1.
apply Rle_lt_trans with (/ INR (2 * N + 1))%R.
unfold Rdiv.
rewrite Rmult_1_l.
apply Rle_Rinv_pos.
apply lt_INR_0.
omega.
apply le_INR.
omega.
rewrite <- (Rinv_involutive eps).
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat.
auto with real.
apply lt_INR_0.
omega.
apply Rlt_trans with (INR N).
destruct (archimed (/ eps)) as (H,_).
assert (0 < up (/ eps))%Z.
apply lt_IZR.
apply Rlt_trans with (2 := H).
apply Rinv_0_lt_compat.
exact Heps.
exact HN.
apply lt_INR.
omega.
apply Rgt_not_eq.
exact Heps.
apply Rle_ge.
unfold Rdiv.
apply Rmult_le_pos.
apply pow_le.
exact (proj1 Hx).
apply Rlt_le.
apply Rinv_0_lt_compat.
apply lt_INR_0.
omega.
Qed.

Definition Ratan_01 : forall x : R, (0 <= x <= 1)%R -> R.
intros x Hx.
destruct (alternated_series (Ratan_seq x)
  (Ratan_seq_decreasing _ Hx) (Ratan_seq_converging _ Hx)) as (y, _).
exact y.
Defined.

Definition Ratan_1 : R.
refine (Ratan_01 1 _).
split.
auto with real.
apply Rle_refl.
Defined.

Definition Ratan_pos : forall x : R, (0 < x)%R -> R.
intros x Hx.
destruct (Rlt_le_dec 1 x).
refine (2 * Ratan_1 - Ratan_01 (/ x) _)%R.
split ; apply Rlt_le.
auto with real.
rewrite <- Rinv_1.
auto with real.
apply (Ratan_01 x).
split.
apply Rlt_le.
exact Hx.
exact r.
Defined.

Definition atan (x : R) : R.
intros x.
destruct (total_order_T x 0) as [[H|H]|H].
refine (Ratan_pos (-x) _).
auto with real.
exact R0.
exact (Ratan_pos x H).
Defined.

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