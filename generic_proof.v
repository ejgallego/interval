Require Import Reals.
Require Import missing.
Require Import Bool.
Require Import ZArith.
Require Import xreal.
Require Import definitions.
Require Import generic.

Definition exp_factor radix e :=
  match e with
  | Zpos p => Z2R (Zpower_pos (Zpos radix) p)
  | Zneg p => Rinv (Z2R (Zpower_pos (Zpos radix) p))
  | Z0 => R1
  end.

(*
Definition HtoR radix m e :=
  (Z2R (Zpos m) * powerRZ (Z2R (Zpos radix)) e)%R.

Definition FtoR radix (s : bool) m e :=
  if s then Ropp (HtoR radix m e) else HtoR radix m e.
*)

Lemma FtoR_split :
  forall radix s m e,
  FtoR radix s m e =
    if s then Ropp (Z2R (Zpos m) * exp_factor radix e)%R
    else (Z2R (Zpos m) * exp_factor radix e)%R.
intros.
unfold FtoR, exp_factor.
case s ; case e ; intros ; try (simpl ; ring) ;
  unfold Rdiv ; try rewrite mult_Z2R ; simpl ; ring.
Qed.

Lemma Zpos_not_R0 :
  forall n,
  Z2R (Zpos n) <> R0.
intros.
rewrite Z2R_IZR.
apply not_O_IZR.
discriminate.
Qed.

Lemma Zpos_Rpos :
  forall n,
  (0 < Z2R (Zpos n))%R.
intros.
rewrite Z2R_IZR.
unfold IZR.
apply INR_pos.
Qed.

Lemma exp_factor_powerRZ :
  forall radix e,
  exp_factor radix e = powerRZ (IZR (Zpos radix)) e.
intros.
unfold powerRZ, exp_factor.
case e ; intros.
apply refl_equal.
rewrite Z2R_IZR.
rewrite Zpower_pos_powerRZ.
apply refl_equal.
apply f_equal.
rewrite Z2R_IZR.
rewrite Zpower_pos_powerRZ.
apply refl_equal.
Qed.

Lemma exp_factor_Rpos :
  forall radix e,
  (0 < exp_factor radix e)%R.
intros.
rewrite exp_factor_powerRZ.
apply powerRZ_lt.
unfold IZR.
apply INR_pos.
Qed.

Lemma exp_factor_not_R0 :
  forall radix e,
  exp_factor radix e <> R0.
intros.
apply Rgt_not_eq.
unfold Rgt.
apply exp_factor_Rpos.
Qed.

Lemma exp_factor_mul :
  forall radix e1 e2,
  exp_factor radix (e1 + e2) = (exp_factor radix e1 * exp_factor radix e2)%R.
intros.
repeat rewrite exp_factor_powerRZ.
apply powerRZ_add.
apply not_O_IZR.
discriminate.
Qed.

Lemma exp_factor_inv :
  forall radix e,
  exp_factor radix (-e) = (/ exp_factor radix e)%R.
intros.
apply Rmult_eq_reg_r with (2 := exp_factor_not_R0 radix e).
rewrite <- exp_factor_mul.
rewrite Zplus_opp_l.
apply Rinv_l_sym.
apply exp_factor_not_R0.
Qed.

Lemma FtoR_Rpos :
  forall radix m e,
  (0 < FtoR radix false m e)%R.
intros.
rewrite FtoR_split.
simpl.
apply Rmult_lt_0_compat.
exact (Zpos_Rpos _).
apply exp_factor_Rpos.
Qed.

Lemma FtoR_neg :
  forall radix s m e,
  (- FtoR radix s m e = FtoR radix (negb s) m e)%R.
intros.
repeat rewrite FtoR_split.
case s ; simpl.
apply Ropp_involutive.
apply refl_equal.
Qed.

Lemma FtoR_Rneg :
  forall radix m e,
  (FtoR radix true m e < 0)%R.
intros.
change true with (negb false).
rewrite <- FtoR_neg.
apply Ropp_lt_gt_0_contravar.
unfold Rgt.
apply FtoR_Rpos.
Qed.

Lemma FtoR_abs :
  forall radix s m e,
  (Rabs (FtoR radix s m e) = FtoR radix false m e)%R.
intros.
case s.
rewrite Rabs_left.
rewrite FtoR_neg.
apply refl_equal.
apply FtoR_Rneg.
apply Rabs_right.
left.
unfold Rgt.
apply FtoR_Rpos.
Qed.

Lemma FtoR_add :
  forall radix s m1 m2 e,
  (FtoR radix s m1 e + FtoR radix s m2 e)%R = FtoR radix s (m1 + m2) e.
intros.
repeat rewrite FtoR_split.
change (Zpos (m1 + m2)) with (Zpos m1 + Zpos m2)%Z.
rewrite plus_Z2R.
rewrite Rmult_plus_distr_r.
case s ; simpl ; try rewrite Ropp_plus_distr ; apply refl_equal.
Qed.

Lemma FtoR_mul :
  forall radix s1 s2 m1 m2 e1 e2,
  (FtoR radix s1 m1 e1 * FtoR radix s2 m2 e2)%R =
  FtoR radix (xorb s1 s2) (m1 * m2) (e1 + e2).
intros.
repeat rewrite FtoR_split.
change (Zpos (m1 * m2)) with (Zpos m1 * Zpos m2)%Z.
rewrite mult_Z2R.
rewrite exp_factor_mul.
case s1 ; case s2 ; simpl ; ring.
Qed.

Lemma shift_correct :
  forall radix m e,
  Zpos (shift radix m e) = (Zpos m * Zpower_pos (Zpos radix) e)%Z.
intros.
Admitted.

Lemma FtoR_shift :
  forall radix s m e p,
  FtoR radix s m (e + Zpos p) = FtoR radix s (shift radix m p) e.
intros.
repeat rewrite FtoR_split.
apply (f_equal (fun v => if s then Ropp v else v)).
rewrite Zplus_comm.
rewrite exp_factor_mul.
rewrite <- Rmult_assoc.
apply Rmult_eq_compat_r.
unfold exp_factor.
rewrite <- mult_Z2R.
rewrite shift_correct.
apply refl_equal.
Qed.

(*
Lemma HtoR_pos :
  forall radix m e, (0 < HtoR radix m e)%R.
intros.
unfold HtoR.
apply Rmult_lt_0_compat.
apply radix_pos.
apply exp_factor_pos.
Qed.

Lemma HtoR_neg :
  forall radix m e, (- HtoR radix m e < 0)%R.
intros.
apply Ropp_lt_gt_0_contravar.
exact (HtoR_pos _ _ _).
Qed.

Lemma FtoR_HtoR :
  forall radix s m1 e1 m2 e2,
  HtoR radix m1 e1 = HtoR radix m2 e2 ->
  FtoR radix s m1 e1 = FtoR radix s m2 e2.
intros.
case s ; simpl.
rewrite H.
apply refl_equal.
exact H.
Qed.
*)

(*
 * Fneg
 *)

Theorem Fneg_correct :
  forall radix (f : float radix),
  FtoX (Fneg f) = Xneg (FtoX f).
intros.
case f ; intros.
apply refl_equal.
simpl.
rewrite Ropp_0.
apply refl_equal.
simpl.
rewrite FtoR_neg.
apply refl_equal.
Qed.

(*
 * Fabs
 *)

Theorem Fabs_correct :
  forall radix (f : float radix),
  FtoX (Fabs f) = Xabs (FtoX f).
intros.
case f ; intros.
apply refl_equal.
simpl.
rewrite Rabs_R0.
apply refl_equal.
simpl.
rewrite FtoR_abs.
apply refl_equal.
Qed.

(*
 * Fscale
 *)

Theorem Fscale_correct :
  forall radix (f : float radix) d,
  FtoX (Fscale f d) = Xmul (FtoX f) (Xreal (exp_factor radix d)).
intros.
case f ; simpl ; intros.
apply refl_equal.
rewrite Rmult_0_l.
apply refl_equal.
apply f_equal.
repeat rewrite FtoR_split.
rewrite exp_factor_mul.
case b ; simpl ; ring.
Qed.

(*
 * Fcmp
 *)

Lemma Fcmp_aux2_correct :
  forall radix m1 m2 e1 e2,
  Fcmp_aux2 radix m1 e1 m2 e2 =
  Xcmp (Xreal (FtoR radix false m1 e1)) (Xreal (FtoR radix false m2 e2)).
intros.
Admitted.

Ltac refl_exists := repeat eapply ex_intro ; repeat split ; try (simpl ; apply refl_equal).

Theorem Fcmp_correct :
  forall radix (x y : float radix),
  Fcmp x y = Xcmp (FtoX x) (FtoX y).
intros.
case x ; intros ; simpl ; try apply refl_equal ;
  case y ; intros ; simpl ; try apply refl_equal ; clear.
rewrite Rcompare_refl.
apply refl_equal.
case b.
rewrite Rcompare_correct_gt.
apply refl_equal.
apply FtoR_Rneg.
rewrite Rcompare_correct_lt.
apply refl_equal.
apply FtoR_Rpos.
case b ; apply refl_equal.
case b.
rewrite Rcompare_correct_lt.
apply refl_equal.
apply FtoR_Rneg.
rewrite Rcompare_correct_gt.
apply refl_equal.
apply FtoR_Rpos.
case b ; case b0.
rewrite Fcmp_aux2_correct.
simpl.
change true with (negb false).
repeat rewrite <- FtoR_neg.
generalize (FtoR radix false p0 z0).
generalize (FtoR radix false p z).
intros.
generalize (Rcompare_correct r0 r).
case (Rcompare r0 r) ; intro H.
rewrite H.
rewrite Rcompare_refl.
apply refl_equal.
rewrite Rcompare_correct_lt.
apply refl_equal.
apply Ropp_lt_contravar.
exact H.
rewrite Rcompare_correct_gt.
apply refl_equal.
apply Ropp_lt_contravar.
exact H.
rewrite Rcompare_correct_lt.
apply refl_equal.
apply Rlt_trans with R0.
apply FtoR_Rneg.
apply FtoR_Rpos.
rewrite Rcompare_correct_gt.
apply refl_equal.
apply Rlt_trans with R0.
apply FtoR_Rneg.
apply FtoR_Rpos.
rewrite Fcmp_aux2_correct.
apply refl_equal.
Qed.

(*
 * Fmin
 *)

Theorem Fmin_correct :
  forall radix (x y : float radix),
  FtoX (Fmin x y) = Xmin (FtoX x) (FtoX y).
intros.
unfold Fmin, Xmin, Rmin.
rewrite (Fcmp_correct radix x y).
case_eq (FtoX x) ; [ split | intros xr Hx ].
case_eq (FtoX y) ; [ split | intros yr Hy ].
simpl.
destruct (Rle_dec xr yr) as [[H|H]|H].
rewrite Rcompare_correct_lt.
exact Hx.
exact H.
rewrite H.
rewrite Rcompare_refl.
rewrite Hx.
apply f_equal with (1 := H).
rewrite Rcompare_correct_gt.
exact Hy.
apply Rnot_le_lt with (1 := H).
Qed.

(*
 * Fmax
 *)

Theorem Fmax_correct :
  forall radix (x y : float radix),
  FtoX (Fmax x y) = Xmax (FtoX x) (FtoX y).
intros.
unfold Fmax, Xmax, Rmax.
rewrite (Fcmp_correct radix x y).
case_eq (FtoX x) ; [ split | intros xr Hx ].
case_eq (FtoX y) ; [ split | intros yr Hy ].
simpl.
destruct (Rle_dec xr yr) as [[H|H]|H].
rewrite Rcompare_correct_lt.
exact Hy.
exact H.
rewrite H.
rewrite Rcompare_refl.
exact Hy.
rewrite Rcompare_correct_gt.
exact Hx.
apply Rnot_le_lt with (1 := H).
Qed.

Definition correctly_located scale x m pos :=
  match pos with
  | pos_Eq => (x = Z2R m * scale)%R
  | pos_Lo => (Z2R m * scale < x < (Z2R m + /2) * scale)%R
  | pos_Mi => (x = (Z2R m + /2) * scale)%R
  | pos_Up => ((Z2R m + /2) * scale < x < Z2R (m + 1) * scale)%R
  end.

Lemma adjust_pos_correct :
  forall scale x pos1 m d r,
  (0 < scale)%R ->
  (0 <= r < Zpos d)%Z ->
  correctly_located scale x (Zpos m * Zpos d + r) pos1 ->
  correctly_located (Z2R (Zpos d) * scale)%R x (Zpos m) (adjust_pos r d pos1).
intros scale x pos1 m d r H0.
unfold correctly_located.
repeat rewrite plus_Z2R.
repeat rewrite mult_Z2R.
repeat rewrite Rmult_plus_distr_r.
rewrite Rmult_assoc.
assert (Hd: (1 <= Zpos d)%Z).
generalize (Zgt_pos_0 d).
omega.
induction r.
(* remainder is 0 *)
rewrite Rmult_0_l.
rewrite Rplus_0_r.
intros _ H1.
induction pos1 ; unfold adjust_pos.
(* - pos1 is posEq *)
exact H1.
(* - pos1 is posLo *)
replace (match d with
  | xI _ => pos_Lo
  | xO _ => pos_Lo
  | 1%positive => pos_Lo
  end) with pos_Lo.
2 : case d ; intros ; apply refl_equal.
split.
exact (proj1 H1).
apply Rlt_le_trans with (1 := proj2 H1).
apply Rplus_le_compat_l.
apply Rmult_le_compat_l.
auto with real.
pattern scale at 1 ; rewrite <- Rmult_1_l.
apply Rmult_le_compat_r.
exact (Rlt_le _ _ H0).
apply Z2R_le with (1 := Hd).
(* - pos1 is posMi *)
case (Zle_lt_or_eq _ _ Hd) ; intros.
replace (match d with
  | xI _ => pos_Lo
  | xO _ => pos_Lo
  | 1%positive => pos_Mi
  end) with pos_Lo.
rewrite H1.
split.
pattern (Z2R (Zpos m) * (Z2R (Zpos d) * scale))%R at 1 ; rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
auto with real.
exact H0.
apply Rplus_lt_compat_l.
apply Rmult_lt_compat_l.
auto with real.
pattern scale at 1 ; rewrite <- Rmult_1_l.
apply Rmult_lt_compat_r.
exact H0.
apply Z2R_lt with (1 := H).
generalize H ; case d ; intros ; try apply refl_equal.
discriminate H2.
injection H. intro. rewrite <- H2.
pattern (Z2R 1 * scale)%R at 2 ; rewrite Rmult_1_l.
rewrite H.
exact H1.
(* - pos1 is posUp *)
case (Zle_lt_or_eq _ _ Hd) ; intros.
replace (match d with
  | xI _ => pos_Lo
  | xO _ => pos_Lo
  | 1%positive => pos_Up
  end) with pos_Lo.
split.
apply Rle_lt_trans with (2 := proj1 H1).
pattern (Z2R (Zpos m) * (Z2R (Zpos d) * scale))%R at 1 ; rewrite <- Rplus_0_r.
apply Rplus_le_compat_l.
apply Rmult_le_pos.
auto with real.
exact (Rlt_le _ _ H0).
apply Rlt_le_trans with (1 := proj2 H1).
apply Rplus_le_compat_l.
apply (Rmult_le_reg_l 2).
auto with real.
rewrite Rmult_1_l.
rewrite <- Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_l.
apply Rmult_le_compat_r.
exact (Rlt_le _ _ H0).
change 2%R with (Z2R 2).
apply Z2R_le.
omega.
apply (not_O_INR 2).
discriminate.
generalize H ; case d ; intros ; try apply refl_equal.
discriminate H2.
injection H. intro. rewrite <- H2.
repeat rewrite Rmult_1_l.
rewrite <- H2 in H1.
rewrite Rmult_1_l in H1.
exact H1.
(* remainder is positive *)
intros Hr H1.
induction pos1 ; unfold adjust_pos.
(* - pos1 is pos_Eq *)
generalize (refl_equal d).
pattern d at 2 3 ; case d ; intros.
(* - - divisor is odd *)
case (Z_lt_le_dec (Zpos p0) (Zpos p)) ; intro.
generalize (Zlt_gt _ _ z).
unfold Zgt.
intro H2. rewrite H2. clear H2.
rewrite H1.
split.
apply Rplus_lt_compat_l.
apply (Rmult_lt_reg_l 2).
auto with real.
rewrite <- Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_l.
rewrite <- Rmult_assoc.
apply Rmult_lt_compat_r.
exact H0.
rewrite <- (mult_Z2R 2).
apply Z2R_lt.
rewrite H.
rewrite Zpos_xI.
omega.
apply (not_O_INR 2).
discriminate.
apply Rplus_lt_compat_l.
rewrite Rmult_1_l.
apply Rmult_lt_compat_r.
exact H0.
apply Z2R_lt.
exact (proj2 Hr).
replace (match (Zpos p ?= Zpos p0)%Z with
  | Eq => pos_Lo
  | Lt => pos_Lo
  | Gt => pos_Up
  end) with pos_Lo.
rewrite H1.
split.
pattern (Z2R (Zpos m) * (Z2R (Zpos d) * scale))%R at 1 ; rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
apply Zpos_Rpos.
exact H0.
apply Rplus_lt_compat_l.
rewrite <- Rmult_assoc.
apply Rmult_lt_compat_r.
exact H0.
apply (Rmult_lt_reg_l 2).
auto with real.
rewrite <- Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_l.
rewrite <- (mult_Z2R 2).
apply Z2R_lt.
rewrite H.
rewrite Zpos_xI.
omega.
apply (not_O_INR 2).
discriminate.
unfold Zle in z.
induction (Zpos p ?= Zpos p0)%Z ; try apply refl_equal.
elim z.
apply refl_equal.
(* - - divisor is even *)
generalize (refl_equal (Zpos p ?= Zpos p0)%Z).
pattern (Zpos p ?= Zpos p0)%Z at -1 ; case (Zpos p ?= Zpos p0)%Z ; intro.
(* - - - r = d / 2 *)
rewrite H1.
apply Rplus_eq_compat_l.
rewrite H.
rewrite Zpos_xO.
rewrite mult_Z2R.
repeat rewrite <- Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_l.
rewrite (Zcompare_Eq_eq _ _ H2).
apply refl_equal.
apply (not_O_INR 2).
discriminate.
(* - - - r < d / 2 *)
rewrite H1.
split.
pattern (Z2R (Zpos m) * (Z2R (Zpos d) * scale))%R at 1 ; rewrite <- Rplus_0_r.
apply Rplus_lt_compat_l.
apply Rmult_lt_0_compat.
apply Zpos_Rpos.
exact H0.
apply Rplus_lt_compat_l.
rewrite <- Rmult_assoc.
apply Rmult_lt_compat_r.
exact H0.
apply (Rmult_lt_reg_l 2).
auto with real.
rewrite <- Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_l.
rewrite <- (mult_Z2R 2).
apply Z2R_lt.
rewrite H.
rewrite (Zpos_xO p0).
assert (Zpos p < Zpos p0)%Z.
exact H2.
omega.
apply (not_O_INR 2).
discriminate.
(* - - - r > d / 2 *)
rewrite H1.
split.
apply Rplus_lt_compat_l.
rewrite H.
rewrite Zpos_xO.
rewrite mult_Z2R.
repeat rewrite <- Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_l.
apply Rmult_lt_compat_r.
exact H0.
apply Z2R_lt.
apply Zgt_lt.
exact H2.
apply (not_O_INR 2).
discriminate.
apply Rplus_lt_compat_l.
rewrite Rmult_1_l.
apply Rmult_lt_compat_r.
exact H0.
apply Z2R_lt.
exact (proj2 Hr).
(* - - divisor is one *)
rewrite H in Hr.
apply False_ind.
generalize (proj2 Hr).
unfold Zlt. simpl.
case p ; intros ; discriminate.
Admitted.

Definition is_bounded radix prec (f : float radix) :=
  match f with
  | Fzero => true
  | Fnan => false
  | Float _ m _ => Zle_bool (Zpos (count_digits radix m)) (Zpos prec)
  end.

Implicit Arguments is_bounded.

Lemma identity_is_around :
  forall radix prec x,
  is_around radix prec x x.
unfold is_around.
intros.
split ; trivial.
Qed.

Lemma bounded_is_correctly_rounded :
  forall radix mode prec (f : float radix),
  is_bounded prec f = true ->
  is_correctly_rounded radix mode prec (FtoX f) (FtoX f).
intros until f.
case f.
intro. discriminate.
intros _.
simpl.
split.
left. apply refl_equal.
split.
apply identity_is_around.
case mode ; try apply Rle_refl.
intros.
case (Req_dec R0 g) ; intros.
left. exact H0.
right.
left.
rewrite Rminus_0_r.
rewrite Rminus_0_l.
rewrite Rabs_R0.
apply Rabs_pos_lt.
auto with real.
intros b.
case b ; simpl ; intros.
split.
right.
exists true.
refl_exists.
apply Zle_bool_imp_le.
exact H.
split.
apply identity_is_around.
case mode ; try apply Rle_refl.
intros.
case (Req_dec (FtoR radix true p z)%R g) ; intros.
left. exact H1.
right.
left.
unfold Rminus.
rewrite Rplus_opp_r.
rewrite Rabs_R0.
apply Rabs_pos_lt.
auto with real.
split.
right.
exists false.
refl_exists.
apply Zle_bool_imp_le.
exact H.
split.
apply identity_is_around.
case mode ; try apply Rle_refl.
intros.
case (Req_dec (FtoR radix false p z) g) ; intros.
left. exact H1.
right.
left.
unfold Rminus.
rewrite Rplus_opp_r.
rewrite Rabs_R0.
apply Rabs_pos_lt.
auto with real.
Qed.

Lemma zero_is_correctly_rounded :
  forall radix mode prec,
  is_correctly_rounded radix mode prec (FtoX (Fzero radix)) (Xreal R0).
intros.
change (Xreal R0) with (FtoX (Fzero radix)).
apply bounded_is_correctly_rounded.
apply refl_equal.
Qed.

Lemma correctly_rounded_uniq :
  forall radix mode prec a b x,
  is_correctly_rounded radix mode prec a x ->
  is_correctly_rounded radix mode prec b x ->
  a = b.
intros radix mode prec a b x Ha Hb.
Admitted.

Definition locate (radix : positive) (prec : positive) (x : R) : positive * Z * position.
Admitted.

Lemma locate_correct :
  forall radix prec x, (0 < x)%R ->
  match locate radix prec x with
  | (m, e, pos) =>
    count_digits radix m = prec /\
    correctly_located (powerRZ (IZR (Zpos radix)) e) x (Zpos m) pos
  end.
Admitted.

Definition round_real radix mode prec x :=
  match Rsign x with
  | Lt =>
    match locate radix prec (-x) with
    | (m, e, pos) => FtoR radix true (adjust_mantissa mode m pos true) e
    end
  | Eq => R0
  | Gt =>
    match locate radix prec x with
    | (m, e, pos) => FtoR radix false (adjust_mantissa mode m pos false) e
    end
  end.

Definition round radix mode prec x :=
  match x with
  | Xreal v =>
    match Rsign v with
    | Lt =>
      match locate radix prec (-v) with
      | (m, e, pos) => Float radix true (adjust_mantissa mode m pos true) e
      end
    | Eq => Fzero radix
    | Gt =>
      match locate radix prec v with
      | (m, e, pos) => Float radix false (adjust_mantissa mode m pos false) e
      end
    end
  | Xnan => Fnan radix
  end.

Lemma round_correct_real :
  forall radix mode prec x,
  FtoX (round radix mode prec (Xreal x)) = Xreal (round_real radix mode prec x).
intros.
unfold round, round_real.
simpl.
case (Rsign x) ; simpl.
apply refl_equal.
destruct (locate radix prec (-x)) as ((m, e), pos).
apply refl_equal.
destruct (locate radix prec x) as ((m, e), pos).
apply refl_equal.
Qed.

Lemma round_correct_zero :
  forall radix mode prec,
  FtoX (round radix mode prec (Xreal R0)) = Xreal R0.
intros.
simpl.
unfold Rsign.
rewrite Rcompare_refl.
apply refl_equal.
Qed.

Axiom round_correctly :
  forall radix mode prec x,
  is_correctly_rounded radix mode prec (FtoX (round radix mode prec x)) x.

Axiom round_monotone :
  forall radix mode prec x y,
  match Xcmp (FtoX (round radix mode prec x)) (FtoX (round radix mode prec y)) with
  | Xeq => True
  | c => Xcmp x y = c
  end.

Definition normalize radix prec m e :=
  match (Zpos (count_digits radix m) - Zpos prec)%Z with
  | Zneg nb => ((shift radix m nb), (e + Zneg nb)%Z)
  | _ => (m, e)
  end.

Lemma normalize_identity :
  forall radix prec m e,
  (Zpos prec <= Zpos (count_digits radix m))%Z ->
  normalize radix prec m e = (m, e).
Admitted.

Lemma normalize_stable :
  forall radix prec s m1 e1,
  FtoR radix s m1 e1 = (let (m2, e2) := normalize radix prec m1 e1 in FtoR radix s m2 e2).
intros.
unfold normalize.
case_eq (Zpos (count_digits radix m1) - Zpos prec)%Z ; trivial.
intros.
pattern e1 at 1 ; replace e1 with (e1 + Zneg p + Zpos p)%Z.
apply FtoR_shift.
change (Zneg p) with (- Zpos p)%Z.
ring.
Qed.

Lemma Fround_at_prec_correct :
  forall radix mode prec s m1 e1 pos x,
  (0 < x)%R ->
  (let (m2, e2) := normalize radix prec m1 e1 in
  correctly_located (exp_factor radix e2) x (Zpos m2) pos) ->
  FtoX (Fround_at_prec mode prec (Ufloat radix s m1 e1 pos)) =
    Xreal (round_real radix mode prec (if s then Ropp x else x)).
Admitted.

(*
Lemma Fround_at_prec_correct_pos_Eq :
  forall radix mode prec s m e,
  FtoX (Fround_at_prec mode prec (Ufloat radix s m e pos_Eq)) =
  Xreal (round_real radix mode prec (FtoR radix s m e)).
intros.
unfold FtoR.
apply Fround_at_prec_correct.
apply HtoR_pos.
unfold correctly_located.
rewrite (normalize_stable radix prec).
destruct (normalize radix prec m e) as (a, b).
apply refl_equal.
Qed.
*)

Lemma Fround_at_prec_correct_pos_Eq :
  forall radix mode prec (x : ufloat radix),
  FtoX (Fround_at_prec mode prec x) =
  FtoX (round radix mode prec (UtoX x)).
Admitted.

Lemma Fadd_slow_aux1_correct :
  forall radix sx sy mx my e,
  UtoX (Fadd_slow_aux1 radix sx sy mx my e) =
  Xadd (FtoX (Float radix sx mx e)) (FtoX (Float radix sy my e)).
intros.
unfold Xadd, FtoX.
unfold Fadd_slow_aux1.
change (Zpos mx + Zneg my)%Z with (Zpos mx - Zpos my)%Z.
case sx ; case sy ; unfold eqb.
(* - - *)
simpl.
rewrite FtoR_add.
apply refl_equal.
(* - + *)
Admitted.
(*
replace (FtoR radix true mx e + FtoR radix false my e)%R
  with (- (Z2R (Zpos mx - Zpos my) * exp_factor radix e))%R.
case (Zpos mx - Zpos my)%Z ; intros.
rewrite Rmult_0_l.
rewrite Ropp_0.
apply refl_equal.
simpl.
rewrite FtoR_split.
apply refl_equal.
simpl.
apply f_equal.
rewrite FtoR_split.
simpl.
ring.
simpl.

replace (- (Z2R (Zneg p) * powerRZ (Z2R (Zpos radix)) e))%R with (FtoR radix false p e).
apply refl_equal.
unfold FtoR, HtoR.
change (Z2R (Zneg p)) with (- Z2R (Zpos p))%R.
ring.
unfold HtoR.
rewrite minus_Z2R.
ring.
(* + - *)
replace (HtoR radix mx e + - HtoR radix my e)%R
  with ((Z2R (Zpos mx - Zpos my) * powerRZ (Z2R (Zpos radix)) e))%R.
case (Zpos mx - Zpos my)%Z ; intros.
rewrite Rmult_0_l.
apply refl_equal.
apply refl_equal.
replace (Z2R (Zneg p) * powerRZ (Z2R (Zpos radix)) e)%R with (FtoR radix true p e).
apply refl_equal.
unfold FtoR, HtoR.
change (Z2R (Zneg p)) with (- Z2R (Zpos p))%R.
ring.
unfold HtoR.
rewrite minus_Z2R.
ring.
(* + + *)
replace (HtoR radix mx e + HtoR radix my e)%R with (FtoR radix false (mx + my) e)%R.
apply refl_equal.
unfold FtoR, HtoR.
fold (Zpos mx + Zpos my)%Z.
rewrite plus_Z2R.
ring.
Qed.
*)

Lemma Fadd_slow_aux2_correct :
  forall radix sx sy mx my ex ey,
  UtoX (Fadd_slow_aux2 radix sx sy mx my ex ey) =
  Xadd (FtoX (Float radix sx mx ex)) (FtoX (Float radix sy my ey)).
intros.
unfold Xadd, FtoX.
unfold Fadd_slow_aux2.
case_eq (ex - ey)%Z ; intros ; rewrite Fadd_slow_aux1_correct ;
  unfold FtoX, Xadd.
(* . *)
replace ey with ex.
apply refl_equal.
rewrite <- (Zplus_0_l ey).
rewrite <- H.
ring.
(* . *)
rewrite <- FtoR_shift.
rewrite <- H.
replace (ey + (ex - ey))%Z with ex. 2: ring.
apply refl_equal.
(* . *)
rewrite <- FtoR_shift.
replace (ex + Zpos p)%Z with ey.
apply refl_equal.
change (Zpos p) with (- Zneg p)%Z.
rewrite <- H.
ring.
Qed.

Theorem Fadd_slow_aux_correct :
  forall radix (x y : float radix),
  UtoX (Fadd_slow_aux x y) = Xadd (FtoX x) (FtoX y).
intros.
case x.
(* . *)
case y ; intros ; apply refl_equal.
(* . *)
simpl.
case y.
apply refl_equal.
unfold FtoX.
rewrite Rplus_0_l.
apply refl_equal.
intros sy my ey.
unfold FtoX.
rewrite Rplus_0_l.
apply refl_equal.
(* . *)
intros sx mx ex.
simpl.
case y.
apply refl_equal.
unfold FtoX.
rewrite Rplus_0_r.
apply refl_equal.
intros sy my ey.
rewrite Fadd_slow_aux2_correct.
apply refl_equal.
Qed.

Theorem Fadd_slow_correct :
  forall radix mode prec (x y : float radix),
  FtoX (Fadd_slow mode prec x y) = FtoX (round radix mode prec (Xadd (FtoX x) (FtoX y))).
intros.
unfold Fadd_slow.
rewrite Fround_at_prec_correct_pos_Eq.
rewrite Fadd_slow_aux_correct.
apply refl_equal.
Qed.

Definition Fadd_correct := Fadd_slow_correct.

(*
 * Fadd_exact
 *)

Theorem Fadd_exact_correct :
  forall radix (x y : float radix),
  FtoX (Fadd_exact x y) = Xadd (FtoX x) (FtoX y).
intros.
unfold Fadd_exact.
rewrite <- (Fadd_slow_aux_correct _ x y).
case (Fadd_slow_aux x y) ; simpl ; try apply refl_equal.
intros.
case p0 ; apply refl_equal.
Qed.

(*
 * Fsub
 *)

Lemma Fsub_split :
  forall radix mode prec (x y : float radix),
  FtoX (Fsub mode prec x y) = (FtoX (Fadd mode prec x (Fneg y))).
intros.
unfold Fneg, Fadd, Fsub, Fadd_slow, Fsub_slow.
case y ; trivial.
Qed.

Theorem Fsub_correct :
  forall radix mode prec (x y : float radix),
  FtoX (Fsub mode prec x y) = FtoX (round radix mode prec (Xsub (FtoX x) (FtoX y))).
intros.
rewrite Fsub_split.
rewrite Xsub_split.
rewrite <- Fneg_correct.
apply Fadd_correct.
Qed.

Theorem Fmul_aux_correct :
  forall radix (x y : float radix),
  UtoX (Fmul_aux x y) = Xmul (FtoX x) (FtoX y).
intros radix [ | | sx mx ex ] [ | | sy my ey ] ; simpl ; try apply refl_equal.
(* . *)
rewrite Rmult_0_l.
apply refl_equal.
(* . *)
rewrite Rmult_0_l.
apply refl_equal.
(* . *)
rewrite Rmult_0_r.
apply refl_equal.
(* . *)
rewrite FtoR_mul.
apply refl_equal.
Qed.

Theorem Fmul_correct :
  forall radix mode prec (x y : float radix),
  FtoX (Fmul mode prec x y) = FtoX (round radix mode prec (Xmul (FtoX x) (FtoX y))).
intros.
unfold Fmul.
rewrite Fround_at_prec_correct_pos_Eq.
rewrite Fmul_aux_correct.
apply refl_equal.
Qed.

Lemma is_zero_correct_zero :
  is_zero 0 = true.
unfold is_zero, Rsign.
rewrite Rcompare_refl.
apply refl_equal.
Qed.

Lemma is_zero_correct_float :
  forall radix s m e,
  is_zero (FtoR radix s m e) = false.
intros.
unfold is_zero, Rsign.
case s ; simpl.
rewrite Rcompare_correct_lt.
apply refl_equal.
apply FtoR_Rneg.
rewrite Rcompare_correct_gt.
apply refl_equal.
apply FtoR_Rpos.
Qed.

Lemma count_digits_correct :
  forall radix m,
  (1 < Zpos radix)%Z ->
  let c := count_digits radix m in
  (Zpower (Zpos radix) (Zpos c - 1) <= Zpos m < Zpower (Zpos radix) (Zpos c))%Z.
Admitted.

Lemma count_digits_correct_inf :
  forall radix m c,
  (1 < Zpos radix)%Z ->
  (Zpower (Zpos radix) (Zpos c - 1) <= Zpos m)%Z ->
  (Zpos c <= Zpos (count_digits radix m))%Z.
Admitted.

Lemma count_digits_correct_sup :
  forall radix m c,
  (1 < Zpos radix)%Z ->
  (Zpos m < Zpower (Zpos radix) (Zpos c))%Z ->
  (Zpos (count_digits radix m) <= Zpos c)%Z.
Admitted.

Lemma count_digits_shift :
  forall radix m k,
  (1 < Zpos radix)%Z ->
  Zpos (count_digits radix (shift radix m k)) = (Zpos (count_digits radix m) + Zpos k)%Z.
intros.
simpl.
apply Zle_antisym.
(* . *)
apply count_digits_correct_sup.
exact H.
rewrite shift_correct.
fold (Zpos (count_digits radix m) + Zpos k)%Z.
rewrite Zpower_exp.
unfold Zpower.
apply Zmult_lt_compat_r.
apply lt_IZR.
rewrite Zpower_pos_powerRZ.
apply powerRZ_lt.
apply (IZR_lt 0).
exact (refl_equal Lt).
exact (proj2 (count_digits_correct _ _ H)).
discriminate.
discriminate.
(* . *)
apply count_digits_correct_inf.
exact H.
rewrite shift_correct.
fold (Zpos (count_digits radix m) + Zpos k)%Z.
fold (Zpower (Zpos radix) (Zpos k)).
replace (Zpos (count_digits radix m) + Zpos k - 1)%Z with (Zpos (count_digits radix m) - 1 + Zpos k)%Z.
2: ring.
rewrite Zpower_exp.
apply Zmult_le_compat_r.
exact (proj1 (count_digits_correct _ _ H)).
simpl.
rewrite Zpower_pos_nat.
apply Zpower_NR0.
discriminate.
simpl.
case (count_digits radix m) ; simpl ; intros ; try apply Zle_refl ; discriminate.
discriminate.
Qed.

Lemma Fdiv_correct_aux :
  forall radix mode prec s mx my e,
  (1 < Zpos radix)%Z ->
  (Zpos (count_digits radix my) + Zpos prec <= Zpos (count_digits radix mx))%Z ->
  FtoX (Fround_at_prec mode prec
    match Zdiv_eucl (Zpos mx) (Zpos my) with
    | (Zpos q, r) => Ufloat radix s q e (adjust_pos r my pos_Eq)
    | _ => Unan radix (* dummy *)
    end) = Xreal (round_real radix mode prec (FtoR radix s mx e / Z2R (Zpos my))%R).
intros radix mode prec s mx my e Hr Hc.
generalize (Z_div_mod (Zpos mx) (Zpos my) (Zgt_pos_0 my)).
destruct (Zdiv_eucl (Zpos mx) (Zpos my)) as (q, r).
intros (He1, He2).
(* prove the quotient has enough digits *)
assert (exists p, q = Zpos p /\ Zpos prec <= Zpos (count_digits radix p))%Z.
(* . *)
assert (Zpower (Zpos radix) (Zpos prec - 1) <= q)%Z.
apply Zle_trans with (Zpower (Zpos radix) (Zpos (count_digits radix mx) - Zpos (count_digits radix my) - 1)).
(* .. *)
cut (Zpos prec - 1 <= Zpos (count_digits radix mx) - Zpos (count_digits radix my) - 1)%Z.
generalize (Zpos prec - 1)%Z (Zpos (count_digits radix mx) - Zpos (count_digits radix my) - 1)%Z.
clear. intros a b.
apply Zpower_le_exp_compat.
apply Zgt_lt.
apply Zgt_pos_0.
omega.
(* .. *)
apply Zlt_succ_le.
apply Zmult_lt_reg_r with (Zpower_pos (Zpos radix) (count_digits radix my)).
apply Zlt_0_Zpower_pos.
exact (refl_equal _).
fold (Zpower (Zpos radix) (Zpos (count_digits radix my))).
rewrite <- Zpower_exp.
apply Zle_lt_trans with (Zpos mx).
replace (Zpos (count_digits radix mx) - Zpos (count_digits radix my) - 1 + Zpos (count_digits radix my))%Z
  with (Zpos (count_digits radix mx) - 1)%Z.
2: ring.
exact (proj1 (count_digits_correct _ _ Hr)).
apply Zle_lt_trans with (Zsucc q * Zpos my)%Z.
unfold Zsucc.
rewrite He1.
rewrite Zmult_plus_distr_l.
rewrite Zmult_comm.
omega.
apply Zmult_lt_compat_l.
apply Zle_lt_succ.
apply Zmult_le_approx with (2 := Zlt_gt _ _ (proj2 He2)).
apply Zgt_pos_0.
rewrite Zmult_comm.
rewrite <- He1.
apply Zlt_le_weak.
apply Zgt_lt.
apply Zgt_pos_0.
exact (proj2 (count_digits_correct _ _ Hr)).
generalize (Zgt_pos_0 prec).
omega.
discriminate.
(* . *)
cut (0 < q)%Z.
case_eq q ; intros ; try discriminate H1 ; refl_exists.
apply count_digits_correct_inf.
exact Hr.
rewrite <- H0.
exact H.
apply Zlt_le_trans with (2 := H).
apply Zlt_0_Zpower.
split.
generalize (Zgt_pos_0 prec).
omega.
(* verify rounding *)
destruct H as (p, (Hp, Hq)).
rewrite Hp.
replace (FtoR radix s mx e / Z2R (Zpos my))%R with
  (if s then - (FtoR radix false mx e * / Z2R (Zpos my)) else FtoR radix false mx e * / Z2R (Zpos my))%R.
apply Fround_at_prec_correct.
apply Fourier_util.Rlt_mult_inv_pos.
apply FtoR_Rpos.
apply Zpos_Rpos.
rewrite normalize_identity with (1 := Hq).
replace (exp_factor radix e) with
  (Z2R (Zpos my) * (exp_factor radix e * / Z2R (Zpos my)))%R.
apply adjust_pos_correct.
apply Fourier_util.Rlt_mult_inv_pos.
apply exp_factor_Rpos.
apply Zpos_Rpos.
exact He2.
unfold correctly_located.
rewrite FtoR_split.
rewrite He1.
rewrite Hp.
rewrite Zmult_comm.
apply Rmult_assoc.
field.
apply Zpos_not_R0.
repeat rewrite FtoR_split.
unfold Rdiv.
case s ; simpl ; try rewrite Ropp_mult_distr_l_reverse ; apply refl_equal.
Qed.

Theorem Fdiv_correct :
  forall radix mode prec (x y : float radix),
  (1 < Zpos radix)%Z ->
  FtoX (Fdiv mode prec x y) = FtoX (round radix mode prec (Xdiv (FtoX x) (FtoX y))).
intros radix mode prec [ | | sx mx ex] [ | | sy my ey] Hr;
  simpl ;
  try rewrite is_zero_correct_zero ;
  try apply refl_equal ;
  rewrite is_zero_correct_float.
unfold Rdiv.
rewrite Rmult_0_l.
apply sym_eq.
apply round_correct_zero.
rewrite round_correct_real.
cutrewrite (FtoR radix sx mx ex / FtoR radix sy my ey = FtoR radix (xorb sx sy) mx (ex - ey) / Z2R (Zpos my))%R.
unfold Fdiv, Fdiv_aux.
simpl Zplus at 1 2.
generalize (xorb sx sy). intro s.
case_eq ((count_digits radix my + prec ?= count_digits radix mx)%positive Eq) ; intro ;
  try ( apply Fdiv_correct_aux with (1 := Hr) ;
        unfold Zle ; simpl ; rewrite H ;
        discriminate ).
(* deal with short mx *)
rewrite Fdiv_correct_aux with (1 := Hr).
rewrite <- FtoR_shift.
assert (forall m n, m + Zneg n + Zpos n = m)%Z.
intros.
change (Zneg n) with (- Zpos n)%Z.
ring.
rewrite H0.
apply refl_equal.
rewrite count_digits_shift with (1 := Hr).
replace (Zpos (count_digits radix my) + Zpos prec)%Z with
  (Zpos (count_digits radix mx) + (Zpos (count_digits radix my) + Zpos prec - Zpos (count_digits radix mx)))%Z.
2: ring.
apply Zplus_le_compat_l.
simpl.
rewrite H.
apply Zle_refl.
(* simplify signs *)
repeat rewrite FtoR_split.
unfold Zminus.
rewrite exp_factor_mul.
rewrite exp_factor_inv.
case sx ; case sy ; simpl ; field ;
  exact (conj (exp_factor_not_R0 _ _) (Zpos_not_R0 _)).
Qed.

Lemma Fsqrt_correct :
  forall radix mode prec (x : float radix),
  FtoX (Fsqrt mode prec x) = FtoX (round radix mode prec (Xsqrt (FtoX x))).
Admitted.

Lemma correctly_rounded_lower :
  forall radix prec f x,
  is_correctly_rounded radix rnd_DN prec (Xreal f) (Xreal x) -> Rle f x.
intros.
exact (proj2 (proj2 H)).
Qed.

Lemma correctly_rounded_upper :
  forall radix prec f x,
  is_correctly_rounded radix rnd_UP prec (Xreal f) (Xreal x) -> Rle x f.
intros.
exact (proj2 (proj2 H)).
Qed.
