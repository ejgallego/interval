Require Import Reals.
Require Import missing.

(*
 * Rcompare
 *)

Definition Rcompare (x y : R) : comparison.
intros.
destruct (total_order_T x y) as [[H | H0] | H].
exact Lt.
exact Eq.
exact Gt.
Defined.

Lemma Rcompare_correct :
  forall x y,
  match Rcompare x y with
  | Lt => Rlt x y
  | Eq => x = y
  | Gt => Rlt y x
  end.
intros.
unfold Rcompare.
destruct (total_order_T x y) as [[H|H]|H] ; exact H.
Qed.

Opaque Rcompare.

Lemma Rcompare_correct_lt :
  forall x y,
  Rlt x y -> Rcompare x y = Lt.
intros x y H.
generalize (Rcompare_correct x y).
case (Rcompare x y) ; intros.
elim Rlt_not_eq with (1 := H) (2 := H0).
apply refl_equal.
elim Rlt_asym with (1 := H) (2 := H0).
Qed.

Lemma Rcompare_correct_gt :
  forall x y,
  Rlt y x -> Rcompare x y = Gt.
intros x y H.
generalize (Rcompare_correct x y).
case (Rcompare x y) ; intros.
elim Rgt_not_eq with (1 := H) (2 := H0).
elim Rlt_asym with (1 := H) (2 := H0).
apply refl_equal.
Qed.

Lemma Rcompare_refl :
  forall x, Rcompare x x = Eq.
intros x.
generalize (Rcompare_correct x x).
case (Rcompare x x) ; intros.
apply refl_equal.
elim Rlt_irrefl with (1 := H).
elim Rlt_irrefl with (1 := H).
Qed.

Definition is_le x y :=
  match Rcompare x y with Gt => false | _ => true end.
Definition is_lt x y :=
  match Rcompare x y with Lt => true | _ => false end.

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

Definition Rsign x := Rcompare x 0.

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

Definition Xneg x :=
  match x with
  | Xreal u => Xreal (-u)
  | Xnan => Xnan
  end.

Definition Xinv x :=
  match x with
  | Xreal u => if is_zero u then Xnan else Xreal (/ u)
  | _ => Xnan
  end.

Definition Xsqrt x :=
  match x with
  | Xreal u => if is_negative u then Xnan else Xreal (sqrt u)
  | Xnan => Xnan
  end.

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

Definition Xsub x y :=
  match x, y with
  | Xreal u, Xreal v => Xreal (u - v)
  | _, _ => Xnan
  end.

Definition Xmul x y :=
  match x, y with
  | Xreal u, Xreal v => Xreal (u * v)
  | _, _ => Xnan
  end.

Definition Xdiv x y :=
  match x, y with
  | Xreal u, Xreal v => if is_zero v then Xnan else Xreal (u / v)
  | _, _ => Xnan
  end.

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
intros.
case x ; case y ; intros ; apply refl_equal.
Qed.

Lemma Xdiv_split :
  forall x y, Xdiv x y = Xmul x (Xinv y).
intros.
case x ; case y ; intros ; try apply refl_equal.
unfold Xmul, Xdiv, Xinv, Rdiv.
case (is_zero r) ; intros ; apply refl_equal.
Qed.

Definition Xsqr x := Xmul x x.

Definition Xatan x :=
  match x with
  | Xreal u => Xreal (Ratan u)
  | Xnan => Xnan
  end.
