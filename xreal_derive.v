Require Import Reals.
Require Import missing.
Require Import xreal.

Definition proj_fun v f x :=
  match f (Xreal x) with Xreal y => y | Xnan => v end.

Theorem derivable_imp_defined :
  forall f r d u v,
  f (Xreal r) = Xreal u -> u <> v ->
  derivable_pt_lim (proj_fun v f) r d ->
  locally_true r (fun a => exists w, f (Xreal a) = Xreal w).
intros.
(* by continuity ... *)
assert (continuity_pt (proj_fun v f) r).
apply derivable_continuous_pt.
exists d.
exact H1.
clear H1.
(* ... the projected result cannot be the default value ... *)
replace u with (proj_fun v f r) in H0.
destruct (continuity_pt_ne _ _ _ H0 H2) as (delta, (Hdelta, H3)).
exists delta.
split.
exact Hdelta.
intros.
generalize (H3 _ H1).
unfold proj_fun.
(* ... so the result is not NaN *)
case (f (Xreal (r + h))).
intro H4.
elim H4.
apply refl_equal.
intros.
exists r0.
apply refl_equal.
unfold proj_fun.
rewrite H.
apply refl_equal.
Qed.

Theorem derivable_imp_nan :
  forall f r d,
  f (Xreal r) = Xnan ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  locally_true r (fun a => f (Xreal a) = Xnan).
intros.
(* by continuity ... *)
assert (forall v, continuity_pt (proj_fun v f) r).
intros.
apply derivable_continuous_pt.
exists d.
apply H0.
clear H0.
(* ... there are points close to r with image 0 and 2 ... *)
assert (H8 : (proj_fun 0 f r < 1)%R).
unfold proj_fun.
rewrite H.
exact Rlt_0_1.
assert (H9 : (1 < proj_fun 2 f r)%R).
unfold proj_fun.
rewrite H.
apply Rlt_plus_1.
generalize (continuity_pt_lt _ _ _ H8 (H1 _)).
generalize (continuity_pt_gt _ _ _ H9 (H1 _)).
clear H8 H9. intros H8 H9.
generalize (locally_true_and _ _ _ H8 H9).
clear H8 H9.
(* ... so they are NaN *)
intros (delta, (Hd, H0)).
exists delta.
split.
exact Hd.
intros h Hh.
destruct (H0 h Hh).
generalize (Rlt_trans _ _ _ H3 H2).
unfold proj_fun.
case (f (Xreal (r + h))).
intros _.
apply refl_equal.
intros y Hy.
elim (Rlt_irrefl _ Hy).
Qed.

Theorem derivable_imp_nan_zero :
  forall f r d,
  f (Xreal r) = Xnan ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  d = R0.
intros.
assert (derivable_pt_lim (fct_cte R0) r d).
eapply derivable_pt_lim_eq_locally with (2 := H0 R0).
apply locally_true_imp with (2 := derivable_imp_nan _ _ _ H H0).
intros.
unfold proj_fun, fct_cte.
now rewrite H1.
apply uniqueness_limite with (1 := H1).
apply derivable_pt_lim_const.
Qed.

Theorem derivable_imp_defined_any :
  forall f r d u,
  f (Xreal r) = Xreal u ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  locally_true r (fun a => exists w, f (Xreal a) = Xreal w).
intros.
eapply derivable_imp_defined.
apply H.
apply Rlt_not_eq.
apply Rlt_plus_1.
apply H0.
Qed.

Theorem derivable_imp_defined_any_2 :
  forall f1 f2 r d1 d2 u1 u2,
  f1 (Xreal r) = Xreal u1 ->
  f2 (Xreal r) = Xreal u2 ->
 (forall v, derivable_pt_lim (proj_fun v f1) r d1) ->
 (forall v, derivable_pt_lim (proj_fun v f2) r d2) ->
  locally_true r (fun a =>
    (exists w1, f1 (Xreal a) = Xreal w1) /\
    (exists w2, f2 (Xreal a) = Xreal w2)).
intros.
apply locally_true_and.
apply (derivable_imp_defined_any _ _ _ _ H H1).
apply (derivable_imp_defined_any _ _ _ _ H0 H2).
Qed.

Theorem derivable_imp_defined_gt :
  forall f r d u t,
  f (Xreal r) = Xreal u -> (t < u)%R ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  locally_true r (fun a => exists w, (t < w)%R /\ f (Xreal a) = Xreal w).
intros.
apply locally_true_imp with
  (fun a => (exists w, f (Xreal a) = Xreal w) /\ (t < proj_fun R0 f a)%R).
intros x ((w, H2), H3).
exists w.
split.
replace (proj_fun 0 f x) with w in H3.
exact H3.
unfold proj_fun.
rewrite H2.
apply refl_equal.
exact H2.
apply locally_true_and.
eapply derivable_imp_defined_any ; eassumption.
apply continuity_pt_gt.
replace (proj_fun 0 f r) with u.
exact H0.
unfold proj_fun.
rewrite H.
apply refl_equal.
apply derivable_continuous_pt.
exists d.
apply H1.
Qed.

Theorem derivable_imp_defined_ne :
  forall f r d u t,
  f (Xreal r) = Xreal u -> (u <> t)%R ->
 (forall v, derivable_pt_lim (proj_fun v f) r d) ->
  locally_true r (fun a => exists w, (w <> t)%R /\ f (Xreal a) = Xreal w).
intros.
apply locally_true_imp with
  (fun a => (exists w, f (Xreal a) = Xreal w) /\ (proj_fun R0 f a <> t)%R).
intros x ((w, H2), H3).
exists w.
split.
replace (proj_fun 0 f x) with w in H3.
exact H3.
unfold proj_fun.
rewrite H2.
apply refl_equal.
exact H2.
apply locally_true_and.
eapply derivable_imp_defined_any ; eassumption.
apply continuity_pt_ne.
replace (proj_fun 0 f r) with u.
exact H0.
unfold proj_fun.
rewrite H.
apply refl_equal.
apply derivable_continuous_pt.
exists d.
apply H1.
Qed.

(*
Lemma proj_indep :
  forall f r d u v,
  f (Xreal r) = Xreal u -> u <> v ->
  derivable_pt_lim (proj_fun v f) r d ->
  forall w, derivable_pt_lim (proj_fun w f) r d.
intros.
(* on this neighborhood, all the projections are equal, so are their derivatives *)
intros eps Heps.
destruct (H1 eps Heps) as (delta1, H3).
destruct H2 as (delta2, H4).
clear H1.
assert (0 < Rmin delta1 delta2)%R.
apply Rmin_pos.
exact (cond_pos delta1).
exact (cond_pos delta2).
exists (mkposreal (Rmin delta1 delta2) H1).
intros.
replace (proj_fun w f r) with (proj_fun v f r).
replace (proj_fun w f (r + h)) with (proj_fun v f (r + h)).
apply H3 ; try assumption.
apply Rlt_le_trans with (1 := H5).
simpl.
apply Rmin_l.
unfold proj_fun.
generalize (H4 h H2 (Rlt_le_trans _ _ _ H5 (Rmin_r delta1 delta2))).
case (f (Xreal (r + h))).
intro.
elim H6.
apply refl_equal.
intros r0 _.
apply refl_equal.
unfold proj_fun.
rewrite H.
apply refl_equal.
Qed.
*)

Definition Xderive f f' :=
  forall x,
  match x, f' x, f x with
  | Xreal r, Xreal d, Xreal _ => forall v, derivable_pt_lim (proj_fun v f) r d
  | _, Xnan, _ => True
  | _, _, _ => False
  end.

Ltac xtotal_aux :=
  let r := fresh "r" in
  let X := fresh "X" in
  match goal with
  | H: False |- _ => elim H
  | |- True => exact I
  | H: Xreal _ = Xnan |- _ => discriminate H
  | H: Xnan = Xreal _ |- _ => discriminate H
  | H: true = false |- _ => discriminate H
  | H: false = true |- _ => discriminate H
  | H: ?v = ?v |- _ => clear H
  | H: Xreal _ = Xreal _ |- _ =>
    injection H ; clear H ; intro H
  | |- match ?v with Xnan => _ | Xreal _ => _ end =>
    case_eq v ; [ intros X | intros r X ]
  | H: match ?v with Xnan => Xnan | Xreal _ => _ end = Xreal _ |- _ =>
    case_eq v ; [ intros X ; rewrite X in H ; discriminate H |
    intros r X ; rewrite X in H ]
  | H: match ?v with Xnan => Xnan | Xreal _ => _ end = Xnan |- _ =>
    case_eq v ; [ intros X ; clear H |
    intros r X ; rewrite X in H ]
  | H: match ?v with true => Xnan | false => Xreal _ end = Xreal _ |- _ =>
    case_eq v ; intro X ; rewrite X in H ; [ discriminate H | idtac ]
  | H: match ?v with true => Xnan | false => Xreal _ end = Xnan |- _ =>
    case_eq v ; intro X ; rewrite X in H ; [ idtac | discriminate H ]
  | H: match ?v with Xnan => _ | Xreal _ => False end |- _ =>
    case_eq v ; [ intros X ; rewrite X in H |
    intros r X ; rewrite X in H ; elim H ]
  | H: match ?v with Xnan => False | Xreal _ => _ end |- _ =>
    case_eq v ; [ intros X ; rewrite X in H ; elim H |
    intros r X ; rewrite X in H ]
  | H1 : Xderive ?f1 ?f2 , H2 : context [?f2 ?v] |- _ =>
    generalize (H1 v) ; clear H1 ; intro H1
  | H: ?v = Xreal _ |- _ => rewrite H in *
  | H: ?v = Xnan |- _ => rewrite H in *
  | v: R, H: ?v = _ |- _ =>
    try rewrite H in * ; clear H v
  | v: R, H: _ = ?v |- _ =>
    try rewrite <- H in * ; clear H v
  end.

Ltac xtotal :=
  unfold Xtan, Xcos, Xsin, Xdiv, Xsqr, Xneg, Xabs, Xadd, Xsub, Xmul, Xinv, Xsqrt, Xatan, Xmask in * ;
  repeat xtotal_aux.

Theorem Xderive_compose :
  forall f f' g g',
  Xderive f f' -> Xderive g g' ->
  Xderive (fun x => g (f x)) (fun x => Xmul (f' x) (g' (f x))).
intros f f' g g' Hf Hg x.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp (proj_fun v g) (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X4 Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
rewrite (Rmult_comm r2).
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun at 2.
rewrite X4.
apply Hg.
Qed.

Theorem Xderive_add :
  forall f g f' g',
  Xderive f f' -> Xderive g g' ->
  Xderive (fun x => Xadd (f x) (g x)) (fun x => Xadd (f' x) (g' x)).
intros f g f' g' Hf Hg x.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (plus_fct (proj_fun v f) (proj_fun v g)).
apply locally_true_imp with (2 := derivable_imp_defined_any_2 _ _ _ _ _ _ _ X7 X6 Hf Hg).
intros x ((w1, Hw1), (w2, Hw2)).
unfold plus_fct, proj_fun.
now rewrite Hw1, Hw2.
now apply derivable_pt_lim_plus.
Qed.

Theorem Xderive_sub :
  forall f g f' g',
  Xderive f f' -> Xderive g g' ->
  Xderive (fun x => Xsub (f x) (g x)) (fun x => Xsub (f' x) (g' x)).
intros f g f' g' Hf Hg x.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (minus_fct (proj_fun v f) (proj_fun v g)).
apply locally_true_imp with (2 := derivable_imp_defined_any_2 _ _ _ _ _ _ _ X7 X6 Hf Hg).
intros x ((w1, Hw1), (w2, Hw2)).
unfold minus_fct, proj_fun.
now rewrite Hw1, Hw2.
now apply derivable_pt_lim_minus.
Qed.

Theorem Xderive_mul :
  forall f g f' g',
  Xderive f f' -> Xderive g g' ->
  Xderive (fun x => Xmul (f x) (g x)) (fun x => Xadd (Xmul (f' x) (g x)) (Xmul (g' x) (f x))).
intros f g f' g' Hf Hg x.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (mult_fct (proj_fun v f) (proj_fun v g)).
apply locally_true_imp with (2 := derivable_imp_defined_any_2 _ _ _ _ _ _ _ X10 X9 Hf Hg).
intros x ((w1, Hw1), (w2, Hw2)).
unfold mult_fct, proj_fun.
now rewrite Hw1, Hw2.
replace r3 with (proj_fun v g r).
replace r2 with (proj_fun v f r).
rewrite (Rmult_comm r6).
now apply derivable_pt_lim_mult.
unfold proj_fun.
now rewrite X10.
unfold proj_fun.
now rewrite X9.
Qed.

Theorem Xderive_div :
  forall f g f' g',
  Xderive f f' -> Xderive g g' ->
  Xderive (fun x => Xdiv (f x) (g x)) (fun x => Xdiv (Xsub (Xmul (f' x) (g x)) (Xmul (g' x) (f x))) (Xmul (g x) (g x))).
intros f g f' g' Hf Hg x.
xtotal.
generalize (is_zero_eq _ X14).
generalize (is_zero_ne _ X13).
intros.
elim H.
rewrite H0.
apply Rmult_0_r.
intro v.
apply derivable_pt_lim_eq_locally with (div_fct (proj_fun v f) (proj_fun v g)).
generalize (derivable_imp_defined_any _ _ _ _ X15 Hf).
generalize (derivable_imp_defined_ne _ _ _ _ _ X12 (is_zero_ne _ X14) Hg).
intros H2 H1.
apply locally_true_imp with (2 := locally_true_and _ _ _ H1 H2).
intros x ((w1, Hw1), (w2, (Hw2a, Hw2b))).
unfold div_fct, proj_fun.
rewrite Hw1, Hw2b.
now rewrite (is_zero_false _ Hw2a).
replace r3 with (proj_fun v g r).
replace r2 with (proj_fun v f r).
fold (Rsqr (proj_fun v g r)).
apply derivable_pt_lim_div.
apply Hf.
apply Hg.
unfold proj_fun.
rewrite X12.
exact (is_zero_ne _ X14).
unfold proj_fun.
now rewrite X15.
unfold proj_fun.
now rewrite X12.
Qed.

Theorem Xderive_neg :
  forall f f',
  Xderive f f' ->
  Xderive (fun x => Xneg (f x)) (fun x => Xneg (f' x)).
intros f f' Hf x.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (opp_fct (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X4 Hf).
intros x (w, Hw).
unfold opp_fct, proj_fun.
now rewrite Hw.
now apply derivable_pt_lim_opp.
Qed.

Theorem Xderive_inv :
  forall f f',
  Xderive f f' ->
  Xderive (fun x => Xinv (f x)) (fun x => Xneg (Xdiv (f' x) (Xsqr (f x)))).
intros f f' Hf x.
xtotal.
generalize (is_zero_eq _ X8).
generalize (is_zero_ne _ X7).
intros.
elim H.
rewrite H0.
apply Rmult_0_r.
intro v.
apply derivable_pt_lim_eq_locally with (inv_fct (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_ne _ _ _ _ _ X6 (is_zero_ne _ X8) Hf).
intros x (w, (Hw1, Hw2)).
unfold inv_fct, proj_fun.
rewrite Hw2.
now rewrite (is_zero_false _ Hw1).
apply derivable_pt_lim_eq with (div_fct (fct_cte 1) (proj_fun v f)).
intro x.
unfold div_fct, fct_cte, Rdiv.
apply Rmult_1_l.
replace (- (r4 / (r2 * r2)))%R with ((0 * proj_fun v f r - r4 * fct_cte 1 r) / Rsqr (proj_fun v f r))%R.
apply (derivable_pt_lim_div (fct_cte 1)).
apply derivable_pt_lim_const.
apply Hf.
unfold proj_fun.
rewrite X6.
exact (is_zero_ne _ X8).
unfold proj_fun, fct_cte, Rsqr.
rewrite X6.
field.
exact (is_zero_ne _ X8).
Qed.

Theorem Xderive_sqrt :
  forall f f',
  Xderive f f' ->
  Xderive (fun x => Xsqrt (f x)) (fun x => Xdiv (f' x) (Xadd (Xsqrt (f x)) (Xsqrt (f x)))).
intros f f' Hf x.
xtotal.
rewrite X7 in X9.
discriminate X9.
intro v.
assert (Hx: (0 < r2)%R).
destruct (total_order_T R0 r2) as [[H|H]|H].
exact H.
elim (is_zero_ne _ X8).
rewrite <- H, sqrt_0, Rplus_0_l.
apply refl_equal.
elim Rgt_not_le with (1 := H).
generalize (is_negative_correct r2).
now rewrite X9.
apply derivable_pt_lim_eq_locally with (comp sqrt (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_gt _ _ _ _ R0 X6 Hx Hf).
intros x (w, (Hw1, Hw2)).
unfold comp, proj_fun.
rewrite Hw2.
unfold is_negative, Rsign.
now rewrite (Rcompare_correct_gt _ _ Hw1).
unfold Rdiv.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X6.
replace (sqrt r2 + sqrt r2)%R with (2 * sqrt r2)%R by ring.
now apply derivable_pt_lim_sqrt.
Qed.

Theorem Xderive_sin :
  forall f f',
  Xderive f f' ->
  Xderive (fun x => Xsin (f x)) (fun x => Xmul (f' x) (Xcos (f x))).
intros f f' Hf x.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp sin (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X5 Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X5.
apply derivable_pt_lim_sin.
Qed.

Theorem Xderive_cos :
  forall f f',
  Xderive f f' ->
  Xderive (fun x => Xcos (f x)) (fun x => Xmul (f' x) (Xneg (Xsin (f x)))).
intros f f' Hf x.
xtotal.
intro v.
apply derivable_pt_lim_eq_locally with (comp cos (proj_fun v f)).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X6 Hf).
intros x (w, Hw).
unfold comp, proj_fun.
now rewrite Hw.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X6.
apply derivable_pt_lim_cos.
Qed.

Theorem Xderive_tan :
  forall f f',
  Xderive f f' ->
  Xderive (fun x => Xtan (f x)) (fun x => Xmul (f' x) (Xadd (Xreal 1) (Xsqr (Xtan (f x))))).
intros f f' Hf x.
xtotal.
rewrite X14 in X15.
discriminate X15.
intro v.
apply derivable_pt_lim_eq_locally with (comp tan (proj_fun v f)).
assert (continuity_pt (comp cos (proj_fun v f)) r).
apply derivable_continuous_pt.
exists (- sin (proj_fun v f r) * r6)%R.
unfold derivable_pt_abs.
apply derivable_pt_lim_comp.
apply Hf.
apply derivable_pt_lim_cos.
replace (cos r4) with (comp cos (proj_fun v f) r) in X14.
generalize (derivable_imp_defined_any _ _ _ _ X13 Hf).
generalize (continuity_pt_ne _ _ R0 (is_zero_ne _ X14) H).
intros H2 H1.
apply locally_true_imp with (2 := locally_true_and _ _ _ H1 H2).
unfold comp, proj_fun.
intros x ((w, Hw1), Hw2).
rewrite Hw1.
rewrite Hw1 in Hw2.
now rewrite (is_zero_false _ Hw2).
unfold comp, proj_fun.
now rewrite X13.
rewrite Rmult_comm.
apply derivable_pt_lim_comp.
apply Hf.
unfold proj_fun.
rewrite X13.
change (sin r4 / cos r4 * (sin r4 / cos r4))%R with (Rsqr (tan r4))%R.
apply derivable_pt_lim_tan.
now apply is_zero_ne.
Qed.

Theorem Xderive_partial_diff :
  forall g' f f',
 (forall x y, f' x = Xreal y -> g' x = Xreal y) ->
  Xderive f g' ->
  Xderive f f'.
intros g' f f' Heq Hf x.
generalize (Heq x).
clear Heq. intro Heq.
xtotal.
generalize (Heq _ (refl_equal _)).
intro.
discriminate H.
generalize (Heq _ (refl_equal _)).
intro.
discriminate H.
rewrite (Heq _ (refl_equal _)) in Hf.
exact Hf.
Qed.

Theorem Xderive_eq_diff :
  forall g' f f',
 (forall x, f' x = g' x) ->
  Xderive f g' ->
  Xderive f f'.
intros.
apply Xderive_partial_diff with (2 := H0).
intros.
now rewrite <- H.
Qed.

Theorem Xderive_partial_fun :
  forall g f f',
 (forall x y, g x = Xreal y -> f x = Xreal y) ->
  Xderive g f' ->
  Xderive f f'.
intros g f f' Heq Hg x.
generalize (Heq x).
intro Heqx.
xtotal.
generalize (Heqx _ (refl_equal _)).
intro.
discriminate H.
intro v.
apply derivable_pt_lim_eq_locally with (2 := Hg v).
apply locally_true_imp with (2 := derivable_imp_defined_any _ _ _ _ X2 Hg).
intros x (w, Hw).
unfold proj_fun.
rewrite Hw.
now rewrite (Heq _ _ Hw).
Qed.

Theorem Xderive_eq_fun :
  forall g f f',
 (forall x, f x = g x) ->
  Xderive g f' ->
  Xderive f f'.
intros.
apply Xderive_partial_fun with (2 := H0).
intros.
now rewrite H.
Qed.

Theorem Xderive_identity :
  Xderive (fun x => x) (fun x => Xmask (Xreal 1) x).
intros [|x].
exact I.
intro.
apply derivable_pt_lim_id.
Qed.

Theorem Xderive_constant :
  forall v,
  Xderive (fun _ => Xreal v) (fun x => Xmask (Xreal 0) x).
intros v [|x].
exact I.
unfold proj_fun.
intros _.
apply (derivable_pt_lim_const v).
Qed.

Theorem Xderive_MVT :
  forall f f',
  Xderive f f' ->
  forall dom : R -> Prop,
  connected dom ->
 (forall x, dom x -> f' (Xreal x) <> Xnan) ->
  forall m, dom m ->
  forall x, dom x ->
  exists c, dom c /\
  f (Xreal x) = Xadd (f (Xreal m)) (Xmul (f' (Xreal c)) (Xsub (Xreal x) (Xreal m))).
intros f f' Hd dom Hdom Hf'.
set (fr := proj_fun 0 f).
set (fr' := proj_fun 0 f').
(* f defined on [a,b] *)
assert (R1: forall x, dom x -> f (Xreal x) = Xreal (fr x)).
intros x Hx.
generalize (Hd (Xreal x)) (Hf' x Hx).
unfold fr, proj_fun at 2.
case (f' (Xreal x)).
intros _ H.
elim H.
apply refl_equal.
case (f (Xreal x)).
intros _ H _.
elim H.
intros r _ _ _.
apply refl_equal.
(* f' defined on [a,b] *)
assert (R2: forall x, dom x -> f' (Xreal x) = Xreal (fr' x)).
intros x Hx.
generalize (Hd (Xreal x)) (Hf' x Hx).
unfold fr', proj_fun at 2.
case (f' (Xreal x)).
intros _ H.
elim H.
apply refl_equal.
intros r _ _.
apply refl_equal.
(* for any u < v *)
assert (H9: forall u v, dom u -> dom v -> (u < v)%R ->
        exists c, dom c /\ f (Xreal v) = Xadd (f (Xreal u)) (Xmul (f' (Xreal c)) (Xsub (Xreal v) (Xreal u)))).
intros u v Hu Hv Huv.
refine (match MVT_cor3 fr fr' u v Huv _ with ex_intro c (conj P1 (conj P2 P3)) => _ end).
intros c Hc1 Hc2.
assert (Hc := Hdom _ _ Hu Hv _ (conj Hc1 Hc2)).
generalize (Hd (Xreal c)).
rewrite (R2 _ Hc), (R1 _ Hc).
intro H2.
exact (H2 R0).
exists c.
assert (Hc := Hdom _ _ Hu Hv _ (conj P1 P2)).
split.
exact Hc.
rewrite (R2 _ Hc), (R1 _ Hu), (R1 _ Hv).
simpl.
apply f_equal.
exact P3.
(* . *)
intros m Hm x Hx.
destruct (total_order_T m x) as [[H|H]|H].
now apply (H9 m x).
(* m = x *)
exists m.
split.
exact Hm.
rewrite H, (R1 _ Hx), (R2 _ Hx).
simpl.
apply f_equal.
ring.
(* m > x *)
destruct (H9 x m Hx Hm H) as (c, (Hc, H0)).
exists c.
split.
exact Hc.
rewrite H0.
rewrite (R2 _ Hc), (R1 _ Hx).
simpl.
apply f_equal.
ring.
Qed.
