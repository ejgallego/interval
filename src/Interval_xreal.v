Require Import Reals.
Require Import Bool.
Require Import Interval_missing.

(*
 * Rcompare
 *)

Definition Rcompare (x y : R) : comparison.
intros x y.
destruct (total_order_T x y) as [[H | H0] | H].
exact Lt.
exact Eq.
exact Gt.
Defined.

Inductive Rcompare_prop (x y : R) : comparison -> Prop :=
  | Rcompare_Lt : (x < y)%R -> Rcompare_prop x y Lt
  | Rcompare_Eq : (x = y)%R -> Rcompare_prop x y Eq
  | Rcompare_Gt : (x > y)%R -> Rcompare_prop x y Gt.

Lemma Rcompare_spec :
  forall x y,
  Rcompare_prop x y (Rcompare x y).
intros x y.
unfold Rcompare.
destruct (total_order_T x y) as [[H|H]|H] ; now constructor.
Qed.

Opaque Rcompare.

(*
Lemma Rcompare_correct :
  forall x y,
  match Rcompare x y with
  | Lt => Rlt x y
  | Eq => x = y
  | Gt => Rlt y x
  end.
intros x y.
unfold Rcompare.
destruct (total_order_T x y) as [[H|H]|H] ; exact H.
Qed.

Opaque Rcompare.
*)

Lemma Rcompare_correct_lt :
  forall x y,
  Rlt x y -> Rcompare x y = Lt.
intros x y H.
destruct (Rcompare_spec x y).
apply refl_equal.
rewrite H0 in H.
elim (Rlt_irrefl _ H).
elim (Rlt_not_le _ _ H).
now left.
Qed.

Lemma Rcompare_correct_gt :
  forall x y,
  Rlt y x -> Rcompare x y = Gt.
intros x y H.
destruct (Rcompare_spec x y).
elim (Rlt_not_le _ _ H).
now left.
rewrite H0 in H.
elim (Rlt_irrefl _ H).
apply refl_equal.
Qed.

Lemma Rcompare_refl :
  forall x, Rcompare x x = Eq.
intros x.
destruct (Rcompare_spec x x).
elim (Rlt_irrefl _ H).
apply refl_equal.
elim (Rlt_irrefl _ H).
Qed.

Definition is_eq x y :=
  match Rcompare x y with Eq => true | _ => false end.
Definition is_le x y :=
  match Rcompare x y with Gt => false | _ => true end.
Definition is_lt x y :=
  match Rcompare x y with Lt => true | _ => false end.

Inductive is_eq_prop (x y : R) : bool -> Prop :=
  | is_eq_true : (x = y)%R -> is_eq_prop x y true
  | is_eq_false : (x <> y)%R -> is_eq_prop x y false.

Inductive is_le_prop (x y : R) : bool -> Prop :=
  | is_le_true : (x <= y)%R -> is_le_prop x y true
  | is_le_false : (y < x)%R -> is_le_prop x y false.

Inductive is_lt_prop (x y : R) : bool -> Prop :=
  | is_lt_true : (x < y)%R -> is_lt_prop x y true
  | is_lt_false : (y <= x)%R -> is_lt_prop x y false.

Lemma is_eq_spec :
  forall x y,
  is_eq_prop x y (is_eq x y).
intros.
unfold is_eq.
destruct (Rcompare_spec x y) ; constructor.
now apply Rlt_not_eq.
exact H.
now apply Rgt_not_eq.
Qed.

Lemma is_le_spec :
  forall x y,
  is_le_prop x y (is_le x y).
intros.
unfold is_le.
destruct (Rcompare_spec x y) ; constructor.
now left.
now right.
exact H.
Qed.

Lemma is_lt_spec :
  forall x y,
  is_lt_prop x y (is_lt x y).
intros.
unfold is_lt.
destruct (Rcompare_spec x y) ; constructor.
exact H.
now right.
now left.
Qed.

Opaque is_eq.
Opaque is_le.
Opaque is_lt.

(*
Lemma is_le_correct :
  forall x y,
  if is_le x y then Rle x y else Rlt y x.
intros x y.
unfold is_le.
generalize (Rcompare_correct x y).
case (Rcompare x y) ; intros ; [ right | left | idtac ] ; exact H.
Qed.

Lemma is_lt_correct :
  forall x y,
  if is_lt x y then Rlt x y else Rle y x.
intros x y.
unfold is_lt.
generalize (Rcompare_correct x y).
case (Rcompare x y) ; intros ; [ right | idtac | left ] ; try exact H.
apply sym_eq.
exact H.
Qed.
*)

Definition Rsign x := Rcompare x 0.

Definition is_positive x := is_lt 0 x.
Definition is_zero x := is_eq x 0.
Definition is_negative x := is_lt x 0.

Lemma is_zero_spec :
  forall x,
  is_eq_prop x 0 (is_zero x).
intros.
apply is_eq_spec.
Qed.

Lemma is_positive_spec :
  forall x,
  is_lt_prop 0 x (is_positive x).
intros.
apply is_lt_spec.
Qed.

Lemma is_negative_spec :
  forall x,
  is_lt_prop x 0 (is_negative x).
intros.
apply is_lt_spec.
Qed.

Opaque is_zero.
Opaque is_positive.
Opaque is_negative.

(*
Definition is_positive x :=
  match Rsign x with Gt => true | _ => false end.
Definition is_zero x :=
  match Rsign x with Eq => true | _ => false end.
Definition is_negative x :=
  match Rsign x with Lt => true | _ => false end.

Lemma is_positive_correct :
  forall x, if is_positive x then Rlt 0 x else Rle x 0.
intros.
unfold is_positive, Rsign.
generalize (Rcompare_correct x 0).
case (Rcompare x 0) ; intro H ; [ right | left | idtac ] ; exact H.
Qed.

Lemma is_zero_correct :
  forall x, if is_zero x then x = R0 else x <> R0.
intros.
unfold is_zero, Rsign.
generalize (Rcompare_correct x 0).
case (Rcompare x 0) ; intro H ; try exact H ;
  [ apply Rlt_not_eq | apply Rgt_not_eq ] ; exact H.
Qed.

Lemma is_negative_correct :
  forall x, if is_negative x then Rlt x 0 else Rle 0 x.
intros.
unfold is_negative, Rsign.
generalize (Rcompare_correct x 0).
case (Rcompare x 0) ; intro H ; [ right | idtac | left ] ; try exact H.
apply sym_eq.
exact H.
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
*)

(*
 * Extended reals
 *)

Inductive ExtendedR : Set :=
  | Xnan : ExtendedR
  | Xreal : R -> ExtendedR.

Inductive Xcomparison : Set :=
  Xeq | Xlt | Xgt | Xund.

Definition Xcmp x y :=
  match x, y with
  | Xreal u, Xreal v =>
    match Rcompare u v with
    | Lt => Xlt
    | Eq => Xeq
    | Gt => Xgt
    end
  | _, _ => Xund
  end.

Definition extension f fx := forall x,
  match fx x, x with
  | Xnan, _ => True
  | Xreal v, Xreal u => f u = v
  | _, _ => False
  end.

Definition extension_2 f fx := forall x y,
  match fx x y, x, y with
  | Xnan, _, _ => True
  | Xreal w, Xreal u, Xreal v => f u v = w
  | _, _, _ => False
  end.

Definition propagate f :=
  f Xnan = Xnan.

Definition propagate_2 f :=
  (forall x, f Xnan x = Xnan) /\ (forall x, f x Xnan = Xnan).

Lemma extension_propagate :
  forall f fx,
  extension f fx -> propagate fx.
intros f fx H.
generalize (H Xnan).
unfold propagate.
case (fx Xnan) ; now intros.
Qed.

Lemma extension_propagate_2 :
  forall f fx,
  extension_2 f fx -> propagate_2 fx.
intros f fx H.
split ; intros x.
generalize (H Xnan x).
case (fx Xnan x) ; now intros.
generalize (H x Xnan).
case (fx x Xnan) ; try split.
case x ; now intros.
Qed.

Definition Xneg x :=
  match x with
  | Xreal u => Xreal (-u)
  | Xnan => Xnan
  end.

Lemma Xneg_correct : extension Ropp Xneg.
now intros [|x].
Qed.

Definition Xinv x :=
  match x with
  | Xreal u => if is_zero u then Xnan else Xreal (/ u)
  | _ => Xnan
  end.

Lemma Xinv_correct : extension Rinv Xinv.
intros [|x] ; try split.
unfold Xinv.
now case (is_zero x).
Qed.

Definition Xsqrt x :=
  match x with
  | Xreal u => if is_negative u then Xnan else Xreal (sqrt u)
  | Xnan => Xnan
  end.

Lemma Xsqrt_correct : extension sqrt Xsqrt.
intros [|x] ; try split.
unfold Xsqrt.
now case (is_negative x).
Qed.

Definition Xabs x :=
  match x with
  | Xreal u => Xreal (Rabs u)
  | Xnan => Xnan
  end.

Definition Xadd x y :=
  match x, y with
  | Xreal u, Xreal v => Xreal (u + v)
  | _, _ => Xnan
  end.

Lemma Xadd_correct : extension_2 Rplus Xadd.
now intros [|x] [|y].
Qed.

Definition Xsub x y :=
  match x, y with
  | Xreal u, Xreal v => Xreal (u - v)
  | _, _ => Xnan
  end.

Lemma Xsub_correct : extension_2 Rminus Xsub.
now intros [|x] [|y].
Qed.

Definition Xmul x y :=
  match x, y with
  | Xreal u, Xreal v => Xreal (u * v)
  | _, _ => Xnan
  end.

Lemma Xmul_correct : extension_2 Rmult Xmul.
now intros [|x] [|y].
Qed.

Definition Xdiv x y :=
  match x, y with
  | Xreal u, Xreal v => if is_zero v then Xnan else Xreal (u / v)
  | _, _ => Xnan
  end.

Lemma Xdiv_correct : extension_2 Rdiv Xdiv.
intros [|x] [|y] ; try split.
unfold Xdiv.
now case (is_zero y).
Qed.

Definition Xmin x y :=
  match x, y with
  | Xreal u, Xreal v => Xreal (Rmin u v)
  | _, _ => Xnan
  end.

Definition Xmax x y :=
  match x, y with
  | Xreal u, Xreal v => Xreal (Rmax u v)
  | _, _ => Xnan
  end.

Lemma Xsub_split :
  forall x y, Xsub x y = Xadd x (Xneg y).
now intros [|x] [|y].
Qed.

Lemma Xdiv_split :
  forall x y, Xdiv x y = Xmul x (Xinv y).
intros [|x] [|y] ; try split.
simpl.
now case (is_zero y).
Qed.

Definition Xsqr x := Xmul x x.

Definition Xcos x :=
  match x with
  | Xreal u => Xreal (cos u)
  | Xnan => Xnan
  end.

Definition Xsin x :=
  match x with
  | Xreal u => Xreal (sin u)
  | Xnan => Xnan
  end.

Definition Xtan x :=
  Xdiv (Xsin x) (Xcos x).

Definition Xatan x :=
  match x with
  | Xreal u => Xreal (atan u)
  | Xnan => Xnan
  end.

Definition Xexp x :=
  match x with
  | Xreal u => Xreal (exp u)
  | Xnan => Xnan
  end.

(*
 * "Field" structure
 *)

Lemma Xadd_comm :
  forall x y,
  Xadd x y = Xadd y x.
intros [|x] [|y] ; try split.
simpl.
apply f_equal.
apply Rplus_comm.
Qed.

Lemma Xadd_assoc :
  forall x y z,
  Xadd (Xadd x y) z = Xadd x (Xadd y z).
intros [|x] [|y] [|z] ; try split.
simpl.
apply f_equal.
apply Rplus_assoc.
Qed.

Lemma Xadd_0_l :
  forall x,
  Xadd (Xreal 0) x = x.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rplus_0_l.
Qed.

Lemma Xadd_0_r :
  forall x,
  Xadd x (Xreal 0) = x.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rplus_0_r.
Qed.

Lemma Xmul_comm :
  forall x y,
  Xmul x y = Xmul y x.
intros [|x] [|y] ; try split.
simpl.
apply f_equal.
apply Rmult_comm.
Qed.

Lemma Xmul_assoc :
  forall x y z,
  Xmul (Xmul x y) z = Xmul x (Xmul y z).
intros [|x] [|y] [|z] ; try split.
simpl.
apply f_equal.
apply Rmult_assoc.
Qed.

Lemma Xmul_1_l :
  forall x,
  Xmul (Xreal 1) x = x.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rmult_1_l.
Qed.

Lemma Xmul_1_r :
  forall x,
  Xmul x (Xreal 1) = x.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rmult_1_r.
Qed.

Lemma Xmul_Xadd_distr_r :
  forall x y z,
  Xmul (Xadd x y) z = Xadd (Xmul x z) (Xmul y z).
intros [|x] [|y] [|z] ; try split.
simpl.
apply f_equal.
apply Rmult_plus_distr_r.
Qed.

Lemma Xmul_Xneg_distr_l :
  forall x y,
  Xmul (Xneg x) y = Xneg (Xmul x y).
intros [|x] [|y] ; try split.
simpl.
apply f_equal.
apply Ropp_mult_distr_l_reverse.
Qed.

Lemma Xmul_Xneg_distr_r :
  forall x y,
  Xmul x (Xneg y) = Xneg (Xmul x y).
intros [|x] [|y] ; try split.
simpl.
apply f_equal.
apply Ropp_mult_distr_r_reverse.
Qed.

Lemma Xinv_Xmul_distr :
  forall x y,
  Xinv (Xmul x y) = Xmul (Xinv x) (Xinv y).
intros [|x] [|y] ; try split ; simpl.
now destruct (is_zero_spec x).
destruct (is_zero_spec x).
destruct (is_zero_spec (x * y)).
apply refl_equal.
elim H0.
rewrite H.
apply Rmult_0_l.
destruct (is_zero_spec y).
destruct (is_zero_spec (x * y)).
apply refl_equal.
elim H1.
rewrite H0.
apply Rmult_0_r.
destruct (is_zero_spec (x * y)).
elim (prod_neq_R0 _ _ H H0 H1).
apply (f_equal Xreal).
now apply Rinv_mult_distr.
Qed.

Definition Xmask x y :=
  match y with
  | Xreal _ => x
  | Xnan => Xnan
  end.

Lemma Xmask_Xfun :
  forall f, propagate f ->
  forall x,
  Xmask (f x) x = f x.
intros f H [|x].
rewrite H.
apply refl_equal.
apply refl_equal.
Qed.

Lemma Xmask_Xfun_l :
  forall f, propagate_2 f ->
  forall x y,
  Xmask (f x y) x = f x y.
intros f H [|x] y.
rewrite (proj1 H).
apply refl_equal.
apply refl_equal.
Qed.

Lemma Xmask_Xfun_r :
  forall f, propagate_2 f ->
  forall x y,
  Xmask (f x y) y = f x y.
intros f H x [|y].
rewrite (proj2 H).
apply refl_equal.
apply refl_equal.
Qed.

Lemma Xfun_Xmask :
  forall f, propagate f ->
  forall x z,
  f (Xmask x z) = Xmask (f x) z.
now intros f H x [|z].
Qed.

Lemma Xfun_Xmask_l :
  forall f, propagate_2 f ->
  forall x y z,
  f (Xmask x z) y = Xmask (f x y) z.
intros f H x y [|z].
now rewrite (proj1 H).
apply refl_equal.
Qed.

Lemma Xfun_Xmask_r :
  forall f, propagate_2 f ->
  forall x y z,
  f x (Xmask y z) = Xmask (f x y) z.
intros f H x y [|z].
now rewrite (proj2 H).
apply refl_equal.
Qed.

Lemma Xmask_identity :
  forall x,
  Xmask x x = x.
intros [|x] ; now split.
Qed.

Lemma Xmask_idempot :
  forall x y,
  Xmask (Xmask x y) y = Xmask x y.
intros [|x] [|y] ; now split.
Qed.

Lemma Xmul_Xinv :
  forall x,
  Xmul x (Xinv x) = Xmask (Xreal 1) (Xinv x).
intros [|x] ; try split.
simpl.
destruct (is_zero_spec x).
apply refl_equal.
simpl.
apply f_equal.
now apply Rinv_r.
Qed.

Lemma Xadd_Xneg :
  forall x,
  Xadd x (Xneg x) = Xmask (Xreal 0) x.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rplus_opp_r.
Qed.

Lemma Xmul_0_l :
  forall x,
  Xmul (Xreal 0) x = Xmask (Xreal 0) x.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rmult_0_l.
Qed.

Lemma Xmul_0_r :
  forall x,
  Xmul x (Xreal 0) = Xmask (Xreal 0) x.
intros [|x] ; try split.
simpl.
apply f_equal.
apply Rmult_0_r.
Qed.

Definition Xadd_propagate := extension_propagate_2 _ _ Xadd_correct.
Definition Xsub_propagate := extension_propagate_2 _ _ Xsub_correct.
Definition Xmul_propagate := extension_propagate_2 _ _ Xmul_correct.
Definition Xdiv_propagate := extension_propagate_2 _ _ Xdiv_correct.
