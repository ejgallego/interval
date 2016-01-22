(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2015, Inria

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

Require Import Reals.
Require Import Bool.
Require Import Interval_missing.

Definition Rsign x := Rcompare x 0.

Definition is_zero x := Req_bool x 0.
Definition is_positive x := Rlt_bool 0 x.
Definition is_negative x := Rlt_bool x 0.

Lemma is_zero_spec :
  forall x, Req_bool_prop x 0 (is_zero x).
Proof.
intros x.
exact (Req_bool_spec x 0).
Qed.

Lemma is_positive_spec :
  forall x, Rlt_bool_prop 0 x (is_positive x).
Proof.
exact (Rlt_bool_spec 0).
Qed.

Lemma is_negative_spec :
  forall x, Rlt_bool_prop x 0 (is_negative x).
Proof.
intros x.
exact (Rlt_bool_spec x 0).
Qed.

Section is_pos_is_neg_missing.

Local Open Scope R_scope.

Lemma is_positive_positive x :
  (is_positive x = true) -> x > 0.
move => Hpos.
have H1 :=(is_positive_spec x).
rewrite Hpos in H1.
by inversion H1.
Qed.

Lemma is_positive_negative x :
  (is_positive x = false) -> x <= 0.
move => Hnpos.
have H1 :=(is_positive_spec x).
rewrite Hnpos in H1.
by inversion H1.
Qed.

Lemma is_negative_negative x :
  (is_negative x = true) -> x < 0.
move => Hneg.
have H1 :=(is_negative_spec x).
rewrite Hneg in H1.
by inversion H1.
Qed.

Lemma is_negative_positive x :
  (is_negative x = false) -> x >= 0.
move => Hneg.
have H1 :=(is_negative_spec x).
rewrite Hneg in H1.
inversion H1.
exact: Rle_ge.
Qed.

End is_pos_is_neg_missing.


(*
 * Extended reals
 *)

Inductive ExtendedR : Set :=
  | Xnan : ExtendedR
  | Xreal : R -> ExtendedR.

(* useful to discriminate over an ExtendedR *)
Definition notXnan (xR : ExtendedR) : Prop :=
  match xR with
    | Xnan => false
    | Xreal _ => true end = true.

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

Lemma Xcmp_rev x y:
  Xcmp y x = match Xcmp x y with
    | Xeq => Xeq
    | Xlt => Xgt
    | Xgt => Xlt
    | Xund => Xund end.
Proof.
case x; case y; try trivial.
intros rx ry.
unfold Xcmp.
now rewrite Rcompare_sym; case: (Rcompare ry rx).
Qed.

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

Lemma Xneg_involutive :
  forall x, Xneg (Xneg x) = x.
Proof.
intros [|x].
easy.
apply (f_equal Xreal), Ropp_involutive.
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

Definition Xln x :=
  match x with
  | Xreal u => if is_positive u then Xreal (ln u) else Xnan
  | Xnan => Xnan
  end.

Definition Xpower_int x n :=
  match x with
  | Xreal u =>
    match n with
    | 0%Z => Xreal 1%R
    | Zpos p => Xreal (pow u (nat_of_P p))
    | Zneg p => if is_zero u then Xnan else Xreal (Rinv (pow u (nat_of_P p)))
    end
  | Xnan => Xnan
  end.

Lemma Xpower_int_correct :
  forall n, extension (fun x => powerRZ x n) (fun x => Xpower_int x n).
Proof.
intros [|n|n] [|x] ; try split.
unfold Xpower_int.
now case (is_zero x).
Qed.

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

Section ExtensionOfFunctionsToXreal.
Require Import ssreflect.

Variable (f : R -> R).

Definition toXreal_fun : ExtendedR -> ExtendedR :=
  fun x => match x with Xnan => Xnan | Xreal r => Xreal (f r) end.

(* Interval_xreal.extension should be boolean *)

Lemma toXreal_fun_correct : extension f toXreal_fun.
Proof. by case. Qed.

End ExtensionOfFunctionsToXreal.
