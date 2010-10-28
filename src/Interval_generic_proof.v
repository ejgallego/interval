Require Import Reals.
Require Import Interval_missing.
Require Import Bool.
Require Import ZArith.
Require Import Fcore.
Require Import Fcalc_digits.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.

Lemma FtoR_split :
  forall beta s m e,
  FtoR beta s m e =
    if s then Ropp (Z2R (Zpos m) * bpow beta e)%R
    else (Z2R (Zpos m) * bpow beta e)%R.
intros.
unfold FtoR.
case s.
rewrite <- Ropp_mult_distr_l_reverse, <- Z2R_opp.
case e ; try rewrite Rmult_1_r ; try easy.
intros p.
now rewrite Z2R_mult.
case e ; try rewrite Rmult_1_r ; try easy.
intros p.
now rewrite Z2R_mult.
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

Lemma FtoR_Rpos :
  forall beta m e,
  (0 < FtoR beta false m e)%R.
intros.
rewrite FtoR_split.
simpl.
apply Rmult_lt_0_compat.
exact (Zpos_Rpos _).
apply bpow_gt_0.
Qed.

Lemma FtoR_neg :
  forall beta s m e,
  (- FtoR beta s m e = FtoR beta (negb s) m e)%R.
intros.
repeat rewrite FtoR_split.
case s ; simpl.
apply Ropp_involutive.
apply refl_equal.
Qed.

Lemma FtoR_Rneg :
  forall beta m e,
  (FtoR beta true m e < 0)%R.
intros.
change true with (negb false).
rewrite <- FtoR_neg.
apply Ropp_lt_gt_0_contravar.
unfold Rgt.
apply FtoR_Rpos.
Qed.

Lemma FtoR_abs :
  forall beta s m e,
  (Rabs (FtoR beta s m e) = FtoR beta false m e)%R.
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
  forall beta s m1 m2 e,
  (FtoR beta s m1 e + FtoR beta s m2 e)%R = FtoR beta s (m1 + m2) e.
intros.
repeat rewrite FtoR_split.
change (Zpos (m1 + m2)) with (Zpos m1 + Zpos m2)%Z.
rewrite Z2R_plus.
rewrite Rmult_plus_distr_r.
case s ; simpl ; try rewrite Ropp_plus_distr ; apply refl_equal.
Qed.

Lemma FtoR_sub :
  forall beta s m1 m2 e,
  (Zpos m2 < Zpos m1)%Z ->
  (FtoR beta s m1 e + FtoR beta (negb s) m2 e)%R = FtoR beta s (m1 - m2) e.
intros.
repeat rewrite FtoR_split.
replace (Zpos (m1 - m2)) with (Zpos m1 - Zpos m2)%Z.
rewrite Z2R_minus.
unfold Rminus.
rewrite Rmult_plus_distr_r.
case s ; simpl.
rewrite Ropp_plus_distr.
rewrite Ropp_mult_distr_l_reverse.
rewrite Ropp_involutive.
apply refl_equal.
rewrite Ropp_mult_distr_l_reverse.
apply refl_equal.
replace (Zpos m1 - Zpos m2)%Z with (-(Zpos m2 - Zpos m1))%Z by ring.
unfold Zlt in H.
simpl in *.
rewrite H.
apply refl_equal.
Qed.

Lemma FtoR_mul :
  forall beta s1 s2 m1 m2 e1 e2,
  (FtoR beta s1 m1 e1 * FtoR beta s2 m2 e2)%R =
  FtoR beta (xorb s1 s2) (m1 * m2) (e1 + e2).
intros.
repeat rewrite FtoR_split.
change (Zpos (m1 * m2)) with (Zpos m1 * Zpos m2)%Z.
rewrite Z2R_mult.
rewrite bpow_plus.
case s1 ; case s2 ; simpl ; ring.
Qed.

Lemma shift_correct :
  forall beta m e,
  Zpos (shift beta m e) = (Zpos m * Zpower_pos beta e)%Z.
Proof.
intros beta m e.
unfold shift, Zpower_pos.
set (r := match radix_val beta with Zpos r => r | _ => xH end).
rewrite 2!iter_nat_of_P.
induction (nat_of_P e).
simpl.
now rewrite Pmult_comm.
simpl iter_nat.
rewrite Zmult_assoc.
rewrite (Zmult_comm (Zpos m)).
rewrite <- Zmult_assoc.
rewrite <- IHn.
rewrite Zpos_mult_morphism.
apply (f_equal (fun v => v * _)%Z).
unfold r.
generalize (radix_val beta) (radix_prop beta).
clear.
now intros [|p|p].
Qed.

Lemma FtoR_shift :
  forall beta s m e p,
  FtoR beta s m (e + Zpos p) = FtoR beta s (shift beta m p) e.
intros.
repeat rewrite FtoR_split.
apply (f_equal (fun v => if s then Ropp v else v)).
rewrite Zplus_comm.
rewrite bpow_plus.
rewrite <- Rmult_assoc.
apply Rmult_eq_compat_r.
rewrite shift_correct.
rewrite Z2R_mult.
rewrite Z2R_Zpower_pos.
now rewrite <- bpow_powerRZ.
Qed.

(*
 * Fneg
 *)

Theorem Fneg_correct :
  forall beta (f : float beta),
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
  forall beta (f : float beta),
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
  forall beta (f : float beta) d,
  FtoX (Fscale f d) = Xmul (FtoX f) (Xreal (bpow beta d)).
intros.
case f ; simpl ; intros.
apply refl_equal.
rewrite Rmult_0_l.
apply refl_equal.
apply f_equal.
repeat rewrite FtoR_split.
rewrite bpow_plus.
case b ; simpl ; ring.
Qed.

(*
 * Fscale2
 *)

Theorem Fscale2_correct :
  forall beta (f : float beta) d,
  match radix_val beta with Zpos (xO _) => true | _ => false end = true ->
  FtoX (Fscale2 f d) = Xmul (FtoX f) (Xreal (bpow radix2 d)).
intros.
case f ; simpl ; intros.
apply refl_equal.
rewrite Rmult_0_l.
apply refl_equal.
case_eq (radix_val beta) ; intros ; rewrite H0 in H ; try discriminate H.
case_eq p0 ; intros ; rewrite H1 in H ; try discriminate H.
rewrite H1 in H0.
clear H H1 p0.
rename p1 into p0.
cut (FtoX
  match d with
  | 0%Z => Float beta b p z
  | Zpos nb =>
      Float beta b
        (iter_pos nb positive (fun x : positive => xO x) p) z
  | Zneg nb =>
      Float beta b
        (iter_pos nb positive
           (fun x : positive => Pmult p0 x) p) (z + d)
  end = Xreal (FtoR beta b p z * bpow radix2 d)).
intro H.
case_eq p0 ; intros ; rewrite H1 in H ; try exact H.
Admitted.

(*
 * Fcmp
 *)

Lemma Fcmp_aux2_correct :
  forall beta m1 m2 e1 e2,
  Fcmp_aux2 beta m1 e1 m2 e2 =
  Xcmp (Xreal (FtoR beta false m1 e1)) (Xreal (FtoR beta false m2 e2)).
intros.
Admitted.

Theorem Fcmp_correct :
  forall beta (x y : float beta),
  Fcmp x y = Xcmp (FtoX x) (FtoX y).
intros.
case x ; intros ; simpl ; try apply refl_equal ;
  case y ; intros ; simpl ; try apply refl_equal ; clear.
now rewrite Rcompare_Eq.
case b.
rewrite Rcompare_Gt.
apply refl_equal.
apply FtoR_Rneg.
rewrite Rcompare_Lt.
apply refl_equal.
apply FtoR_Rpos.
case b ; apply refl_equal.
case b.
rewrite Rcompare_Lt.
apply refl_equal.
apply FtoR_Rneg.
rewrite Rcompare_Gt.
apply refl_equal.
apply FtoR_Rpos.
case b ; case b0.
rewrite Fcmp_aux2_correct.
simpl.
change true with (negb false).
repeat rewrite <- FtoR_neg.
generalize (FtoR beta false p0 z0).
generalize (FtoR beta false p z).
intros.
destruct (Rcompare_spec r0 r).
rewrite Rcompare_Lt.
apply refl_equal.
now apply Ropp_lt_contravar.
rewrite H.
now rewrite Rcompare_Eq.
rewrite Rcompare_Gt.
apply refl_equal.
apply Ropp_lt_contravar.
exact H.
rewrite Rcompare_Lt.
apply refl_equal.
apply Rlt_trans with R0.
apply FtoR_Rneg.
apply FtoR_Rpos.
rewrite Rcompare_Gt.
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
  forall beta (x y : float beta),
  FtoX (Fmin x y) = Xmin (FtoX x) (FtoX y).
intros.
unfold Fmin, Xmin, Rmin.
rewrite (Fcmp_correct beta x y).
case_eq (FtoX x) ; [ split | intros xr Hx ].
case_eq (FtoX y) ; [ split | intros yr Hy ].
simpl.
destruct (Rle_dec xr yr) as [[H|H]|H].
rewrite Rcompare_Lt.
exact Hx.
exact H.
now rewrite Rcompare_Eq.
rewrite Rcompare_Gt.
exact Hy.
apply Rnot_le_lt with (1 := H).
Qed.

(*
 * Fmax
 *)

Theorem Fmax_correct :
  forall beta (x y : float beta),
  FtoX (Fmax x y) = Xmax (FtoX x) (FtoX y).
intros.
unfold Fmax, Xmax, Rmax.
rewrite (Fcmp_correct beta x y).
case_eq (FtoX x) ; [ split | intros xr Hx ].
case_eq (FtoX y) ; [ split | intros yr Hy ].
simpl.
destruct (Rle_dec xr yr) as [[H|H]|H].
rewrite Rcompare_Lt.
exact Hy.
exact H.
now rewrite Rcompare_Eq.
rewrite Rcompare_Gt.
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

Definition is_bounded beta prec (f : float beta) :=
  match f with
  | Fzero => true
  | Fnan => false
  | Float _ m _ => Zle_bool (Zpos (count_digits beta m)) (Zpos prec)
  end.

Implicit Arguments is_bounded.

Ltac refl_exists :=
  repeat eapply ex_intro
  (*match goal with
  | |- ex ?P => eapply ex_intro
  end*) ;
  repeat split.

Definition locate (beta : radix) (prec : positive) (x : R) : positive * Z * position.
Admitted.

Definition round_real beta mode prec x :=
  match Rsign x with
  | Lt =>
    match locate beta prec (-x) with
    | (m, e, pos) => FtoR beta true (adjust_mantissa mode m pos true) e
    end
  | Eq => R0
  | Gt =>
    match locate beta prec x with
    | (m, e, pos) => FtoR beta false (adjust_mantissa mode m pos false) e
    end
  end.

Definition round beta mode prec x :=
  match x with
  | Xreal v =>
    match Rsign v with
    | Lt =>
      match locate beta prec (-v) with
      | (m, e, pos) => Float beta true (adjust_mantissa mode m pos true) e
      end
    | Eq => Fzero beta
    | Gt =>
      match locate beta prec v with
      | (m, e, pos) => Float beta false (adjust_mantissa mode m pos false) e
      end
    end
  | Xnan => Fnan beta
  end.

Lemma round_correct_real :
  forall beta mode prec x,
  FtoX (round beta mode prec (Xreal x)) = Xreal (round_real beta mode prec x).
intros.
unfold round, round_real.
simpl.
case (Rsign x) ; simpl.
apply refl_equal.
destruct (locate beta prec (-x)) as ((m, e), pos).
apply refl_equal.
destruct (locate beta prec x) as ((m, e), pos).
apply refl_equal.
Qed.

Lemma round_correct_zero :
  forall beta mode prec,
  FtoX (round beta mode prec (Xreal R0)) = Xreal R0.
intros.
simpl.
unfold Rsign.
now rewrite Rcompare_Eq.
Qed.

Definition rnd_of_mode mode :=
  match mode with
  | rnd_UP => rndUP
  | rnd_DN => rndDN
  | rnd_ZR => rndZR
  | rnd_NE => rndNE
  end.

Definition is_correctly_rounded beta mode prec f' x' :=
  match x', f' with
  | Xnan, Xnan => True
  | Xreal x, Xreal f => f = Fcore_generic_fmt.round beta (FLX_exp (Zpos prec)) (rnd_of_mode mode) x
  | _, _ => False
  end.

Axiom round_correctly :
  forall beta mode prec x,
  is_correctly_rounded beta mode prec (FtoX (round beta mode prec x)) x.

Axiom round_monotone :
  forall beta mode prec x y,
  match Xcmp (FtoX (round beta mode prec x)) (FtoX (round beta mode prec y)) with
  | Xeq => True
  | c => Xcmp x y = c
  end.

Definition normalize beta prec m e :=
  match (Zpos (count_digits beta m) - Zpos prec)%Z with
  | Zneg nb => ((shift beta m nb), (e + Zneg nb)%Z)
  | _ => (m, e)
  end.

Lemma normalize_identity :
  forall beta prec m e,
  (Zpos prec <= Zpos (count_digits beta m))%Z ->
  normalize beta prec m e = (m, e).
Proof.
intros beta prec m e.
unfold Zle, normalize.
rewrite <- (Zcompare_plus_compat _ _ (- Zpos prec)).
rewrite Zplus_opp_l, Zplus_comm.
unfold Zminus.
case Zplus ; try easy.
intros p H.
now elim H.
Qed.

Lemma Fround_at_prec_correct :
  forall beta mode prec s m1 e1 pos x,
  (0 < x)%R ->
  (let (m2, e2) := normalize beta prec m1 e1 in
  correctly_located (bpow beta e2) x (Zpos m2) pos) ->
  FtoX (Fround_at_prec mode prec (Ufloat beta s m1 e1 pos)) =
    Xreal (round_real beta mode prec (if s then Ropp x else x)).
Admitted.

Lemma Fround_at_prec_correct_pos_Eq :
  forall beta mode prec (x : ufloat beta),
  FtoX (Fround_at_prec mode prec x) =
  FtoX (round beta mode prec (UtoX x)).
Admitted.

Lemma Fadd_slow_aux1_correct :
  forall beta sx sy mx my e,
  UtoX (Fadd_slow_aux1 beta sx sy mx my e) =
  Xadd (FtoX (Float beta sx mx e)) (FtoX (Float beta sy my e)).
intros.
unfold Xadd, FtoX.
unfold Fadd_slow_aux1.
change (Zpos mx + Zneg my)%Z with (Zpos mx - Zpos my)%Z.
case_eq (eqb sx sy) ; intro H.
(* == *)
rewrite (eqb_prop _ _ H).
rewrite FtoR_add.
apply refl_equal.
(* != *)
replace sy with (negb sx).
clear H.
case_eq (Zpos mx - Zpos my)%Z.
intro H.
rewrite <- (FtoR_neg beta sx).
unfold FtoR.
change (Zneg mx) with (- Zpos mx)%Z.
rewrite (Zminus_eq _ _ H).
rewrite Rplus_opp_r.
apply refl_equal.
intro p.
unfold Zminus, Zplus.
simpl.
case_eq ((mx ?= my)%positive Eq) ; intros ; try discriminate H0.
rewrite (FtoR_sub beta sx).
now inversion H0.
apply Zgt_lt.
exact H.
intro p.
unfold Zminus, Zplus.
simpl.
case_eq ((mx ?= my)%positive Eq) ; intros ; try discriminate H0.
pattern sx at 2 ; rewrite <- (negb_involutive sx).
rewrite Rplus_comm.
rewrite (FtoR_sub beta (negb sx)).
now inversion H0.
exact H.
generalize H. clear.
now case sx ; case sy.
Qed.

Lemma Fadd_slow_aux2_correct :
  forall beta sx sy mx my ex ey,
  UtoX (Fadd_slow_aux2 beta sx sy mx my ex ey) =
  Xadd (FtoX (Float beta sx mx ex)) (FtoX (Float beta sy my ey)).
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
  forall beta (x y : float beta),
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
  forall beta mode prec (x y : float beta),
  FtoX (Fadd_slow mode prec x y) = FtoX (round beta mode prec (Xadd (FtoX x) (FtoX y))).
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
  forall beta (x y : float beta),
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
  forall beta mode prec (x y : float beta),
  FtoX (Fsub mode prec x y) = (FtoX (Fadd mode prec x (Fneg y))).
intros.
unfold Fneg, Fadd, Fsub, Fadd_slow, Fsub_slow.
case y ; trivial.
Qed.

Theorem Fsub_correct :
  forall beta mode prec (x y : float beta),
  FtoX (Fsub mode prec x y) = FtoX (round beta mode prec (Xsub (FtoX x) (FtoX y))).
intros.
rewrite Fsub_split.
rewrite Xsub_split.
rewrite <- Fneg_correct.
apply Fadd_correct.
Qed.

Theorem Fmul_aux_correct :
  forall beta (x y : float beta),
  UtoX (Fmul_aux x y) = Xmul (FtoX x) (FtoX y).
intros beta [ | | sx mx ex ] [ | | sy my ey ] ; simpl ; try apply refl_equal.
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
  forall beta mode prec (x y : float beta),
  FtoX (Fmul mode prec x y) = FtoX (round beta mode prec (Xmul (FtoX x) (FtoX y))).
intros.
unfold Fmul.
rewrite Fround_at_prec_correct_pos_Eq.
rewrite Fmul_aux_correct.
apply refl_equal.
Qed.

Lemma is_zero_correct_zero :
  is_zero 0 = true.
destruct (is_zero_spec 0).
apply refl_equal.
now elim H.
Qed.

Lemma is_zero_correct_float :
  forall beta s m e,
  is_zero (FtoR beta s m e) = false.
intros beta s m e.
destruct (is_zero_spec (FtoR beta s m e)).
destruct s.
refine (False_ind _ (Rlt_not_eq _ _ _ H)).
apply FtoR_Rneg.
refine (False_ind _ (Rgt_not_eq _ _ _ H)).
apply FtoR_Rpos.
apply refl_equal.
Qed.

Lemma FtoR_conversion_pos :
  forall beta m e,
  Fcore_defs.F2R (Fcore_defs.Float beta (Zpos m) e) = FtoR beta false m e.
Proof.
intros beta m e.
unfold FtoR.
destruct e.
apply Rmult_1_r.
now rewrite Z2R_mult.
easy.
Qed.

Lemma convert_location_correct :
  forall beta m e x l,
  Fcalc_bracket.inbetween_float beta m e x l ->
  correctly_located (bpow beta e) x m (convert_location l).
Proof.
intros beta m e x l H.
inversion_clear H ; simpl.
exact H0.
destruct l0 ; simpl.
Admitted.

Lemma digits_conversion :
  forall beta p,
  digits beta (Zpos p) = Zpos (count_digits beta p).
Proof.
intros beta p.
unfold digits, count_digits.
generalize xH, (radix_val beta), p at 1 3.
induction p ; simpl ; intros.
case (Zlt_bool (Zpos p1) z).
apply refl_equal.
rewrite <- IHp.
now rewrite Pplus_one_succ_r.
case (Zlt_bool (Zpos p1) z).
apply refl_equal.
rewrite <- IHp.
now rewrite Pplus_one_succ_r.
now case (Zlt_bool (Zpos p0) z).
Qed.

Theorem Fdiv_correct :
  forall beta mode prec (x y : float beta),
  FtoX (Fdiv mode prec x y) = FtoX (round beta mode prec (Xdiv (FtoX x) (FtoX y))).
Proof.
intros beta mode prec [ | | sx mx ex] [ | | sy my ey] ;
  simpl ;
  try rewrite is_zero_correct_zero ;
  try apply refl_equal ;
  rewrite is_zero_correct_float.
unfold Rdiv.
rewrite Rmult_0_l.
apply sym_eq.
apply round_correct_zero.
rewrite round_correct_real.
unfold Fdiv, Fdiv_aux.
generalize (Fcalc_div.Fdiv_core_correct beta (Zpos prec) (Zpos mx) ex (Zpos my) ey (refl_equal Lt)).
destruct (Fcalc_div.Fdiv_core beta (Zpos prec) (Zpos mx) ex (Zpos my) ey) as ((m', e'), l).
intros (H3, H4) ; try easy.
destruct m' as [|p|p].
now elim H3.
replace (FtoR beta sx mx ex / FtoR beta sy my ey)%R with
  (if xorb sx sy then - (FtoR beta false mx ex / FtoR beta false my ey) else (FtoR beta false mx ex / FtoR beta false my ey))%R.
apply (Fround_at_prec_correct beta mode prec _ p e').
apply Rmult_lt_0_compat.
apply FtoR_Rpos.
apply Rinv_0_lt_compat.
apply FtoR_Rpos.
rewrite normalize_identity.
apply convert_location_correct.
now rewrite 2!FtoR_conversion_pos in H4.
now rewrite <- digits_conversion.
rewrite 4!FtoR_split.
assert (bpow beta ey <> 0 /\ P2R my <> 0)%R.
split.
apply Rgt_not_eq.
apply bpow_gt_0.
apply Zpos_not_R0.
now case sx ; case sy ; simpl ; field.
destruct (Fcalc_bracket.inbetween_float_bounds _ _ _ _ _ H4) as (_, H5).
elim (Rlt_not_le _ _ H5).
apply Rle_trans with R0.
apply Fcore_float_prop.F2R_le_0_compat.
unfold Fcore_defs.Fnum.
now apply (Zlt_le_succ (Zneg p)).
apply Rlt_le.
apply Rmult_lt_0_compat.
now apply Fcore_float_prop.F2R_gt_0_compat.
apply Rinv_0_lt_compat.
now apply Fcore_float_prop.F2R_gt_0_compat.
Qed.

Lemma Fsqrt_correct :
  forall beta mode prec (x : float beta),
  FtoX (Fsqrt mode prec x) = FtoX (round beta mode prec (Xsqrt (FtoX x))).
Proof.
intros beta mode prec [ | | sx mx ex] ; simpl ; try easy.
(* *)
case is_negative_spec.
intros H.
elim (Rlt_irrefl _ H).
intros _.
rewrite sqrt_0.
now rewrite round_correct_zero.
(* *)
unfold Fsqrt, Fsqrt_aux.
case is_negative_spec.
case sx ; simpl.
easy.
intros H.
elim (Rlt_not_le _ _ H).
apply Rlt_le.
apply FtoR_Rpos.
case sx.
intros H.
elim (Rle_not_lt _ _ H).
apply FtoR_Rneg.
intros _.
rewrite round_correct_real.
generalize (Fcalc_sqrt.Fsqrt_core_correct beta (Zpos prec) (Zpos mx) ex (refl_equal Lt)).
destruct (Fcalc_sqrt.Fsqrt_core beta (Zpos prec) (Zpos mx)) as ((m', e'), l).
intros (H3, H4).
destruct m' as [|p|p].
now elim H3.
apply (Fround_at_prec_correct beta mode prec false p e').
apply sqrt_lt_R0.
apply FtoR_Rpos.
rewrite normalize_identity.
apply convert_location_correct.
now rewrite FtoR_conversion_pos in H4.
now rewrite <- digits_conversion.
destruct (Fcalc_bracket.inbetween_float_bounds _ _ _ _ _ H4) as (_, H5).
elim (Rlt_not_le _ _ H5).
apply Rle_trans with R0.
apply Fcore_float_prop.F2R_le_0_compat.
unfold Fcore_defs.Fnum.
now apply (Zlt_le_succ (Zneg p)).
apply Fcore_Raux.sqrt_ge_0.
Qed.

Lemma correctly_rounded_lower :
  forall beta prec f x,
  is_correctly_rounded beta rnd_DN prec (Xreal f) (Xreal x) -> Rle f x.
Proof.
intros.
rewrite H.
eapply round_DN_pt.
now apply FLX_exp_correct.
Qed.

Lemma correctly_rounded_upper :
  forall beta prec f x,
  is_correctly_rounded beta rnd_UP prec (Xreal f) (Xreal x) -> Rle x f.
Proof.
intros.
rewrite H.
eapply round_UP_pt.
now apply FLX_exp_correct.
Qed.
