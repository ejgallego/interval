(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: http://coq-interval.gforge.inria.fr/

Copyright (C) 2007-2019, Inria

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

From Coq Require Import Reals List.

Require Import Xreal.
Require Import Basic.
Require Import Interval.

Inductive unary_op : Set :=
  | Neg | Abs | Inv | Sqr | Sqrt
  | Cos | Sin | Tan | Atan | Exp | Ln
  | PowerInt (n : Z) | Nearbyint (m : rounding_mode).

Inductive binary_op : Set :=
  | Add | Sub | Mul | Div.

Inductive expr : Set :=
  | Evar : nat -> expr
  | Eint : Z -> expr
  | Econst_pi : expr
  | Eunary : unary_op -> expr -> expr
  | Ebinary : binary_op -> expr -> expr -> expr.

Definition unary_real (o : unary_op) : R -> R :=
  match o with
  | Neg => Ropp
  | Abs => Rabs
  | Inv => Rinv
  | Sqr => Rsqr
  | Sqrt => sqrt
  | Cos => cos
  | Sin => sin
  | Tan => tan
  | Atan => atan
  | Exp => exp
  | Ln => ln
  | PowerInt n => fun x => powerRZ x n
  | Nearbyint m => Rnearbyint m
  end.

Definition binary_real (o : binary_op) : R -> R -> R :=
  match o with
  | Add => Rplus
  | Sub => Rminus
  | Mul => Rmult
  | Div => Rdiv
  end.

Fixpoint eval (e : expr) (l : list R) :=
  match e with
  | Evar n => nth n l 0%R
  | Eint n => IZR n
  | Econst_pi => PI
  | Eunary o e1 => unary_real o (eval e1 l)
  | Ebinary o e1 e2 => binary_real o (eval e1 l) (eval e2 l)
  end.

Ltac list_add a l :=
  let rec aux a l n :=
    match l with
    | nil        => constr:((n, cons a l))
    | cons a _   => constr:((n, l))
    | cons ?x ?l =>
      match aux a l (S n) with
      | (?n, ?l) => constr:((n, cons x l))
      end
    end in
  aux a l O.

Ltac reify t l :=
  let rec aux t l :=
    let aux_u o a :=
      match aux a l with
      | (?u, ?l) => constr:((Eunary o u, l))
      end in
    let aux_b o a b :=
      match aux b l with
      | (?v, ?l) =>
        match aux a l with
        | (?u, ?l) => constr:((Ebinary o u v, l))
        end
      end in
    match t with
    | Ropp ?a => aux_u Neg a
    | Rabs ?a => aux_u Abs a
    | Rinv ?a => aux_u Inv a
    | Rsqr ?a => aux_u Sqr a
    | Rmult ?a ?a => aux_u Sqr a
    | sqrt ?a => aux_u Sqrt a
    | cos ?a => aux_u Cos a
    | sin ?a => aux_u Sin a
    | tan ?a => aux_u Tan a
    | atan ?a => aux_u Atan a
    | exp ?a => aux_u Exp a
    | ln ?a => aux_u Ln a
    | powerRZ ?a ?b => aux_u (PowerInt b) a
    | pow ?a ?b => aux_u (PowerInt (Z_of_nat b)) a
    | Rplus ?a ?b => aux_b Add a b
    | Rminus ?a ?b => aux_b Sub a b
    | Rplus ?a (Ropp ?b) => aux_b Sub a b
    | Rmult ?a ?b => aux_b Mul a b
    | Rdiv ?a ?b => aux_b Div a b
    | Rmult ?a (Rinv ?b) => aux_b Div a b
    | Rnearbyint ?a ?b => aux_u (Nearbyint a) b
    | IZR (Raux.Ztrunc ?a) => aux_u (Nearbyint rnd_ZR) a
    | IZR (Raux.Zfloor ?a) => aux_u (Nearbyint rnd_DN) a
    | IZR (Raux.Zceil ?a) => aux_u (Nearbyint rnd_UP) a
    | IZR (Round_NE.ZnearestE ?a) => aux_u (Nearbyint rnd_NE) a
    | PI => constr:((Econst_pi, l))
    | IZR ?n => constr:((Eint n, l))
    | _ =>
      match list_add t l with
      | (?n, ?l) => constr:((Evar n, l))
      end
    end in
  aux t l.

Module Bnd (I : IntervalOps).

Module J := IntervalExt I.

Definition unary_bnd prec (o : unary_op) : I.type -> I.type :=
  match o with
  | Neg => I.neg
  | Abs => I.abs
  | Inv => I.inv prec
  | Sqr => I.sqr prec
  | Sqrt => I.sqrt prec
  | Cos => I.cos prec
  | Sin => I.sin prec
  | Tan => I.tan prec
  | Atan => I.atan prec
  | Exp => I.exp prec
  | Ln => I.ln prec
  | PowerInt n => fun x => I.power_int prec x n
  | Nearbyint m => I.nearbyint m
  end.

Lemma unary_bnd_correct :
  forall prec o xi x,
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert (unary_bnd prec o xi)) (Xreal (unary_real o x)).
Proof.
intros prec o xi x.
destruct o.
apply I.neg_correct.
apply I.abs_correct.
apply J.inv_correct.
apply I.sqr_correct.
apply J.sqrt_correct.
apply I.cos_correct.
apply I.sin_correct.
apply J.tan_correct.
apply I.atan_correct.
apply I.exp_correct.
apply J.ln_correct.
apply J.power_int_correct.
apply I.nearbyint_correct.
Qed.

Definition binary_bnd prec (o : binary_op) : I.type -> I.type -> I.type :=
  match o with
  | Add => I.add prec
  | Sub => I.sub prec
  | Mul => I.mul prec
  | Div => I.div prec
  end.

Lemma binary_bnd_correct :
  forall prec o xi yi x y,
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert yi) (Xreal y) ->
  contains (I.convert (binary_bnd prec o xi yi)) (Xreal (binary_real o x y)).
Proof.
intros prec o xi yi x y.
destruct o.
apply I.add_correct.
apply I.sub_correct.
apply I.mul_correct.
apply J.div_correct.
Qed.

Fixpoint eval_bnd (prec : I.precision) (e : expr) :=
  match e with
  | Evar _ => I.nai
  | Eint n => I.fromZ n
  | Econst_pi => I.pi prec
  | Eunary o e1 => unary_bnd prec o (eval_bnd prec e1)
  | Ebinary o e1 e2 => binary_bnd prec o (eval_bnd prec e1) (eval_bnd prec e2)
  end.

Theorem eval_bnd_correct :
  forall prec e,
  contains (I.convert (eval_bnd prec e)) (Xreal (eval e nil)).
Proof.
intros prec.
induction e as [n|n| |o e1 IHe1|o e1 IHe1 e2 IHe2].
simpl.
now rewrite I.nai_correct.
apply I.fromZ_correct.
apply I.pi_correct.
now apply unary_bnd_correct.
now apply binary_bnd_correct.
Qed.

End Bnd.
