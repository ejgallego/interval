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
  match x, f x, f' x with
  | Xreal r, Xreal _, Xreal d => forall v, derivable_pt_lim (proj_fun v f) r d
  | Xreal _, _, Xnan => True
  | Xnan, Xnan, Xnan => True
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
  | H1 : Xderive ?f1 ?f2 , H2 : context [?f1 ?v] |- _ =>
    generalize (H1 v) ; clear H1 ; intro H1
  | H: ?v = Xreal _ |- _ => rewrite H in *
  | H: ?v = Xnan |- _ => rewrite H in *
  | v: R, H: ?v = _ |- _ =>
    try rewrite H in * ; clear H v
  | v: R, H: _ = ?v |- _ =>
    try rewrite <- H in * ; clear H v
  end.

Ltac xtotal :=
  unfold Xneg, Xabs, Xadd, Xsub, Xmul, Xdiv, Xsqrt in * ;
  repeat xtotal_aux.

Theorem Xderive_compose :
  forall f f' g g',
  Xderive f f' -> Xderive g g' ->
  Xderive (fun x => g (f x)) (fun x => Xmul (f' x) (g' (f x))).
intros f f' g g' Hf Hg x.
xtotal.
intro v.
destruct (derivable_imp_defined_any _ _ _ _ X4 Hf) as (delta, (Hdelta, H0)).
eapply derivable_pt_lim_eq_close with (1 := Hdelta).
intros.
instantiate (1 := comp (proj_fun v g) (proj_fun v f)).
unfold comp, proj_fun.
destruct (H0 _ H).
rewrite H1.
apply refl_equal.
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
destruct (derivable_imp_defined_any_2 _ _ _ _ _ _ _ X4 X5 Hf Hg) as (delta, (Hdelta, H0)).
eapply derivable_pt_lim_eq_close with (1 := Hdelta).
intros.
instantiate (1 := plus_fct (proj_fun v f) (proj_fun v g)).
unfold plus_fct, proj_fun.
destruct (H0 h H) as ((w1, W1), (w2, W2)).
rewrite W1, W2.
apply refl_equal.
apply derivable_pt_lim_plus.
apply Hf.
apply Hg.
Qed.

Theorem Xderive_sub :
  forall f g f' g',
  Xderive f f' -> Xderive g g' ->
  Xderive (fun x => Xsub (f x) (g x)) (fun x => Xsub (f' x) (g' x)).
intros f g f' g' Hf Hg x.
xtotal.
intro v.
destruct (derivable_imp_defined_any_2 _ _ _ _ _ _ _ X4 X5 Hf Hg) as (delta, (Hdelta, H0)).
eapply derivable_pt_lim_eq_close with (1 := Hdelta).
intros.
instantiate (1 := minus_fct (proj_fun v f) (proj_fun v g)).
unfold minus_fct, proj_fun.
destruct (H0 h H) as ((w1, W1), (w2, W2)).
rewrite W1, W2.
apply refl_equal.
apply derivable_pt_lim_minus.
apply Hf.
apply Hg.
Qed.

Theorem Xderive_mul :
  forall f g f' g',
  Xderive f f' -> Xderive g g' ->
  Xderive (fun x => Xmul (f x) (g x)) (fun x => Xadd (Xmul (f' x) (g x)) (Xmul (g' x) (f x))).
intros f g f' g' Hf Hg x.
xtotal.
intro v.
destruct (derivable_imp_defined_any_2 _ _ _ _ _ _ _ X8 X9 Hf Hg) as (delta, (Hdelta, H0)).
eapply derivable_pt_lim_eq_close with (1 := Hdelta).
intros.
instantiate (1 := mult_fct (proj_fun v f) (proj_fun v g)).
unfold mult_fct, proj_fun.
destruct (H0 h H) as ((w1, W1), (w2, W2)).
rewrite W1, W2.
apply refl_equal.
replace r7 with (proj_fun v g r).
replace r5 with (proj_fun v f r).
rewrite (Rmult_comm r4).
apply derivable_pt_lim_mult.
apply Hf.
apply Hg.
unfold proj_fun.
rewrite X8.
apply refl_equal.
unfold proj_fun.
rewrite X9.
apply refl_equal.
Qed.

Lemma is_zero_eq :
  forall x, is_zero x = true -> x = R0.
intros.
generalize (is_zero_correct x).
rewrite H.
intro.
exact H0.
Qed.

Lemma is_zero_ne :
  forall x, is_zero x = false -> x <> R0.
intros.
generalize (is_zero_correct x).
rewrite H.
intro.
exact H0.
Qed.

Lemma is_zero_true :
  forall x, x = R0 -> is_zero x = true.
intros.
generalize (is_zero_correct x).
case (is_zero x).
split.
rewrite H.
intro.
elim H0.
apply refl_equal.
Qed.

Lemma is_zero_false :
  forall x, x <> R0 -> is_zero x = false.
intros.
generalize (is_zero_correct x).
case (is_zero x).
intro.
elim (H H0).
split.
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
generalize (derivable_imp_defined_any _ _ _ _ X11 Hf).
generalize (derivable_imp_defined_ne _ _ _ _ _ X12 (is_zero_ne _ X13) Hg).
intros H2 H1.
destruct (locally_true_and _ _ _ H1 H2) as (delta, (Hdelta, H0)).
eapply derivable_pt_lim_eq_close with (1 := Hdelta).
intros.
instantiate (1 := div_fct (proj_fun v f) (proj_fun v g)).
unfold div_fct, proj_fun.
destruct (H0 h H) as ((w1, W1), (w2, (W2a, W2b))).
rewrite W1, W2b.
rewrite (is_zero_false _ W2a).
apply refl_equal.
replace r4 with (proj_fun v g r).
replace r8 with (proj_fun v f r).
fold (Rsqr (proj_fun v g r)).
apply derivable_pt_lim_div.
apply Hf.
apply Hg.
unfold proj_fun.
rewrite X12.
exact (is_zero_ne _ X13).
unfold proj_fun.
rewrite X11.
apply refl_equal.
unfold proj_fun.
rewrite X12.
apply refl_equal.
Qed.

Theorem Xderive_neg :
  forall f f',
  Xderive f f' ->
  Xderive (fun x => Xneg (f x)) (fun x => Xneg (f' x)).
intros f f' Hf x.
xtotal.
intro v.
destruct (derivable_imp_defined_any _ _ _ _ X3 Hf) as (delta, (Hdelta, H0)).
eapply derivable_pt_lim_eq_close with (1 := Hdelta).
intros.
instantiate (1 := opp_fct (proj_fun v f)).
unfold opp_fct, proj_fun.
destruct (H0 h H) as (w, W).
rewrite W.
apply refl_equal.
apply derivable_pt_lim_opp.
apply Hf.
Qed.

Theorem Xderive_sqrt :
  forall f f',
  Xderive f f' ->
  Xderive (fun x => Xsqrt (f x)) (fun x => Xdiv (f' x) (Xadd (Xsqrt (f x)) (Xsqrt (f x)))).
intros f f' Hf x.
xtotal.
intro v.
destruct (derivable_imp_defined_any _ _ _ _ X3 Hf) as (delta, (Hdelta, H0)).
eapply derivable_pt_lim_eq_close with (1 := Hdelta).
intros.
Admitted.

Theorem Xderive_eq_diff :
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
