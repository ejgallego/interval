Require Import Reals.
Require Import List.
Require Import Interval_missing.
Require Import ZArith.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float_full.
Require Import Interval_bisect.

Module IntervalTactic (F : FloatOps with Definition even_radix := true).

Inductive interval_tac_parameters :=
  | i_prec : nat -> interval_tac_parameters
  | i_bisect : R -> interval_tac_parameters
  | i_bisect_diff : R -> interval_tac_parameters
  | i_bisect_taylor : R -> nat -> interval_tac_parameters
  | i_depth : nat -> interval_tac_parameters.

Module Private.

Module I := FloatIntervalFull F.
Module A := IntervalAlgos I.

Ltac get_float t :=
  let get_mantissa t :=
    let rec aux t :=
      match t with
      | 1%R => xH
      | 2%R => constr:(xO xH)
      | 3%R => constr:(xI xH)
      | (2 * ?v)%R =>
        let w := aux v in constr:(xO w)
      | (1 + 2 * ?v)%R =>
        let w := aux v in constr:(xI w)
      end in
    aux t in
  let get_float_rational s n d :=
    let rec aux t :=
      match t with
      | 2%R => xH
      | (2 * ?v)%R =>
        let w := aux v in
        eval vm_compute in (Psucc w)
      end in
    let e := aux d in
    let m := get_mantissa n in
    eval vm_compute in (F.fromF (Interval_generic.Float radix2 s m (Zneg e))) in
  let get_float_integer s t :=
    let rec aux m e :=
      match m with
      | xO ?v =>
        let u := eval vm_compute in (Zsucc e) in
        aux v u
      | _ => constr:(m, e)
      end in
    let m := get_mantissa t in
    let v := aux m Z0 in
    match v with
    | (?m, ?e) => eval vm_compute in (F.fromF (Interval_generic.Float radix2 s m e))
    end in
  match t with
  | 0%R => F.zero
  | (-?n * /?d)%R => get_float_rational true n d
  | (?n * /?d)%R => get_float_rational false n d
  | (-?n / ?d)%R => get_float_rational true n d
  | (?n / ?d)%R => get_float_rational false n d
  | (-?n)%R => get_float_integer true n
  | ?n => get_float_integer false n
  | _ => false
  end.

Lemma Rabs_contains :
  forall f v,
  contains (I.convert (I.bnd (F.neg f) f)) (Xreal v) ->
  match F.toF f with
  | Interval_generic.Float false m e => (Rabs v <= FtoR F.radix false m e)%R
  | _ => True
  end.
Proof.
intros f v (H1,H2).
generalize (F.real_correct f).
case_eq (F.toF f) ; try easy.
intros [|] m e Hf _.
exact I.
unfold I.I.convert_bound in H1, H2.
rewrite F.neg_correct in H1.
rewrite Fneg_correct in H1.
rewrite Hf in H1, H2.
simpl in H1, H2.
now apply Rabs_def1_le.
Qed.

Lemma Rabs_contains_rev :
  forall f v,
  match F.toF f with
  | Interval_generic.Float false m e => (Rabs v <= FtoR F.radix false m e)%R
  | _ => False
  end ->
  contains (I.convert (I.bnd (F.neg f) f)) (Xreal v).
Proof.
intros f v.
generalize (F.real_correct f).
case_eq (F.toF f) ; try easy.
intros [|] m e Hf _ H.
easy.
destruct (Rabs_def2_le _ _ H) as (H1,H2).
split ; unfold I.I.convert_bound.
rewrite F.neg_correct.
rewrite Fneg_correct.
now rewrite Hf.
now rewrite Hf.
Qed.

Lemma xreal_to_contains :
  forall prog terms n xi,
  A.check_p (A.subset_check xi) (nth n (eval_ext prog (map Xreal terms)) Xnan) ->
  contains (I.convert xi) (Xreal (nth n (eval_real prog terms) R0)).
Proof.
intros prog terms n xi.
simpl A.check_p.
apply (xreal_to_real (fun x => contains (I.convert xi) x) (fun x => contains (I.convert xi) (Xreal x))).
now case (I.convert xi).
easy.
Qed.

Lemma xreal_to_positive :
  forall prog terms n,
  A.check_p A.positive_check (nth n (eval_ext prog (map Xreal terms)) Xnan) ->
  (0 < nth n (eval_real prog terms) R0)%R.
Proof.
intros prog terms n.
simpl A.check_p.
now apply (xreal_to_real (fun x => match x with Xnan => False | Xreal r => (0 < r)%R end) (fun x => (0 < x)%R)).
Qed.

Lemma xreal_to_nonzero :
  forall prog terms n,
  A.check_p A.nonzero_check (nth n (eval_ext prog (map Xreal terms)) Xnan) ->
  nth n (eval_real prog terms) R0 <> R0.
Proof.
intros prog terms n.
simpl A.check_p.
now apply (xreal_to_real (fun x => match x with Xnan => False | Xreal r => r <> R0 end) (fun x => x <> R0)).
Qed.

Inductive expr :=
  | Econst : nat -> expr
  | Eunary : unary_op -> expr -> expr
  | Ebinary : binary_op -> expr -> expr -> expr.

Ltac list_add a l :=
  let rec aux a l n :=
    match l with
    | nil        => constr:(n, cons a l)
    | cons a _   => constr:(n, l)
    | cons ?x ?l =>
      match aux a l (S n) with
      | (?n, ?l) => constr:(n, cons x l)
      end
    end in
  aux a l O.

Ltac remove_constants t l :=
  let rec aux t l :=
    match get_float t with
    | false =>
      let aux_u o a :=
        match aux a l with
        | (?u, ?l) => constr:(Eunary o u, l)
        end in
      let aux_b o a b :=
        match aux b l with
        | (?v, ?l) =>
          match aux a l with
          | (?u, ?l) => constr:(Ebinary o u v, l)
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
      | _ =>
        match list_add t l with
        | (?n, ?l) => constr:(Econst n, l)
        end
      end
    | _ =>
      match list_add t l with
      | (?n, ?l) => constr:(Econst n, l)
      end
    end in
  aux t l.

Ltac list_find1 a l :=
  let rec aux l n :=
    match l with
    | nil       => false
    | cons a _  => n
    | cons _ ?l => aux l (S n)
    end in
  aux l O.

Ltac get_non_constants t :=
  let rec aux t l :=
    match t with
    | Econst _ => l
    | _ =>
      match list_find1 t l with
      | false =>
        let m :=
          match t with
          | Eunary _ ?a => aux a l
          | Ebinary _ ?a ?b => aux a ltac:(aux b l)
          end in
        constr:(cons t m)
      | _ => l
      end
    end in
  aux t (@nil expr).

Ltac list_find2 a l :=
  let rec aux l n :=
    match l with
    | nil       => false
    | cons a _  => n
    | cons _ ?l => aux l (S n)
    end in
  match a with
  | Econst ?n => eval compute in (n + length l)%nat
  | _ => aux l O
  end.

Ltac generate_machine l :=
  let rec aux l q :=
    match l with
    | nil => q
    | cons ?t ?l =>
      let m :=
        match t with
        | Eunary ?o ?a =>
          let u := list_find2 a l in
          constr:(Unary o u)
        | Ebinary ?o ?a ?b =>
          let u := list_find2 a l in
          let v := list_find2 b l in
          constr:(Binary o u v)
        end in
      aux l (cons m q)
    end in
  aux l (@nil term).

Ltac extract_algorithm t l :=
  match remove_constants t l with
  | (?t, ?lc) =>
    let lm := generate_machine ltac:(get_non_constants t) in
    constr:(lm, lc)
  end.

Ltac xalgorithm_pre :=
  match goal with
  | |- Rge _ _ =>
    apply Rle_ge ;
    xalgorithm_pre
  | |- Rgt _ _ =>
    unfold Rgt ;
    xalgorithm_pre
  | |- Rle ?a ?b /\ Rle ?b ?c =>
    let v := get_float a in
    let w := get_float c in
    change (contains (I.convert (I.bnd v w)) (Xreal b))
  | |- Rle (Rabs ?a) ?b =>
    let v := get_float b in
    refine (Rabs_contains v a _)
  | |- Rle ?a ?b =>
    let v := get_float b in
    refine (proj2 (_ : contains (I.convert (I.bnd F.nan v)) (Xreal a)))
  | |- Rle ?a ?b =>
    let v := get_float a in
    refine (proj1 (_ : contains (I.convert (I.bnd v F.nan)) (Xreal b)))
  | |- Rle ?a ?b =>
    apply Rminus_le ;
    refine (proj2 (_ : contains (I.convert (I.bnd F.nan F.zero)) (Xreal (a - b))))
  | |- Rlt 0 ?b =>
    idtac
  | |- Rlt ?a ?b =>
    apply Rminus_gt ;
    unfold Rgt
  | |- (?a <> 0)%R =>
    idtac
  | |- (?a <> ?b)%R =>
    apply Rminus_not_eq
  | _ => fail 100 "Goal is not an inequality with floating-point bounds."
  end.

Ltac xalgorithm_post lx :=
  match goal with
  | |- contains (I.convert ?xi) (Xreal ?y) =>
    match extract_algorithm y lx with
    | (?a, ?b) =>
      let formula := fresh "formula" in
      pose (formula := a) ;
      refine (xreal_to_contains formula b O xi _)
    end
  | |- (0 < ?y)%R =>
    match extract_algorithm y lx with
    | (?a, ?b) =>
      let formula := fresh "formula" in
      pose (formula := a) ;
      refine (xreal_to_positive formula b O _)
    end
  | |- (?y <> 0)%R =>
    match extract_algorithm y lx with
    | (?a, ?b) =>
      let formula := fresh "formula" in
      pose (formula := a) ;
      refine (xreal_to_nonzero formula b O _)
    end
  end.

Ltac xalgorithm lx :=
  match goal with
  | |- A.check_p ?check (nth ?n (eval_ext ?formula (map Xreal ?constants)) Xnan) => idtac
  | _ => xalgorithm_pre ; xalgorithm_post lx
  end.

Ltac list_warn l :=
  let rec aux l :=
    match l with
    | nil => idtac
    | cons ?a ?l => idtac a ; aux l
    end in
  aux l.

Ltac list_warn_rev l :=
  let rec aux l :=
    match l with
    | nil => idtac
    | cons ?a ?l => aux l ; idtac a
    end in
  aux l.

Ltac warn_whole l :=
  match l with
  | nil => idtac
  | cons _ nil =>
    idtac "Warning: Silently use the whole real line for the following term:" ;
    list_warn_rev l ; idtac "You may need to unfold this term."
  | cons _ _ =>
    idtac "Warning: Silently use the whole real line for the following terms:" ;
    list_warn_rev l ; idtac "You may need to unfold some of these terms."
  end.

Ltac get_bounds l prec :=
  let rec aux l prec lw :=
    match l with
    | nil => constr:(@nil A.bound_proof, @nil R)
    | cons ?x ?l =>
      let i :=
      match x with
      | PI => constr:(A.Bproof x (I.pi prec) (I.pi_correct prec), @None R)
      | _ =>
        let v := get_float x in
        constr:(let f := v in A.Bproof x (I.bnd f f) (conj (Rle_refl x) (Rle_refl x)), @None R)
      | _ =>
        match goal with
        | H: Rle ?a x /\ Rle x ?b |- _ =>
          let v := get_float a in
          let w := get_float b in
          constr:(A.Bproof x (I.bnd v w) H, @None R)
        | H: Rle ?a x |- _ =>
          let v := get_float a in
          constr:(A.Bproof x (I.bnd v F.nan) (conj H I), @None R)
        | H: Rle x ?b |- _ =>
          let v := get_float b in
          constr:(A.Bproof x (I.bnd F.nan v) (conj I H), @None R)
        | H: Rle (Rabs x) ?b |- _ =>
          let v := get_float b in
          constr:(A.Bproof x (I.bnd (F.neg v) v) (Rabs_contains_rev v x H), @None R)
        | _ =>
          match goal with
          | H: Rle ?a x /\ Rle x ?b |- _ => idtac
          | H: Rle ?a x |- _ => idtac
          | H: Rle x ?b |- _ => idtac
          | H: Rle (Rabs x) ?b |- _ => idtac
          end ;
          fail 100 "Atom" x "is neither a floating-point value nor bounded by floating-point values."
        | _ =>
          constr:(A.Bproof x (I.bnd F.nan F.nan) (conj I I), @Some R x)
        end
      end in
      match aux l prec lw with
      | (?m, ?lw) =>
        match i with
        | (?i, @None R) => constr:(cons i m, lw)
        | (?i, @Some R ?aw) => constr:(cons i m, cons aw lw)
        end
      end
    end in
  aux l prec (@nil R).

Lemma interval_helper_evaluate :
  forall bounds check formula prec n,
  A.check_f check (nth n (A.BndValuator.eval prec formula (map A.interval_from_bp bounds)) I.nai) = true ->
  A.check_p check (nth n (eval_ext formula (map A.xreal_from_bp bounds)) Xnan).
Proof.
intros bound (check_f, check_p, check_th). simpl.
intros.
apply check_th with (2 := H).
apply A.BndValuator.eval_correct.
Qed.

Lemma interval_helper_bisection :
  forall bounds check formula prec depth n,
  match bounds with
  | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
    let fi := fun b => nth n (A.BndValuator.eval prec formula (b :: map A.interval_from_bp tail)) I.nai in
    A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true
  | _ => False
  end ->
  A.check_p check (nth n (eval_ext formula (map A.xreal_from_bp bounds)) Xnan).
Proof.
intros [|[x [|l u] Hx] bounds] check formula prec depth n ; try easy.
pose (f := fun x => nth n (eval_ext formula (x :: map A.xreal_from_bp bounds)) Xnan).
pose (fi := fun b => nth n (A.BndValuator.eval prec formula (b :: map A.interval_from_bp bounds)) I.nai).
change (A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true -> A.check_p check (f (Xreal x))).
intros H.
apply A.bisect_1d_correct with (P := fun x => A.check_p check (f x)) (2 := H) (3 := Hx).
intros y yi Hy Hb.
destruct check as [b P HP].
apply (HP (f y) (fi yi)) with (2 := Hb).
now apply A.BndValuator.eval_correct_ext.
Qed.

Lemma interval_helper_bisection_diff :
  forall bounds check formula prec depth n,
  match bounds with
  | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
    let fi := fun b => A.DiffValuator.eval prec formula (map A.interval_from_bp tail) n b in
    A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true
  | _ => False
  end ->
  A.check_p check (nth n (eval_ext formula (map A.xreal_from_bp bounds)) Xnan).
Proof.
intros [|[x [|l u] Hx] bounds] check formula prec depth n ; try easy.
pose (f := fun x => nth n (eval_ext formula (x :: map A.xreal_from_bp bounds)) Xnan).
pose (fi := fun b => A.DiffValuator.eval prec formula (map A.interval_from_bp bounds) n b).
change (A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true -> A.check_p check (f (Xreal x))).
intros H.
apply A.bisect_1d_correct with (P := fun x => A.check_p check (f x)) (2 := H) (3 := Hx).
intros y yi Hy Hb.
destruct check as [b P HP].
apply (HP (f y) (fi yi)) with (2 := Hb).
now apply A.DiffValuator.eval_correct_ext.
Qed.

Lemma interval_helper_bisection_taylor :
  forall bounds check formula prec deg depth n,
  match bounds with
  | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
    let fi := fun b => A.TaylorValuator.TM.eval (prec, deg)
      (nth n (A.TaylorValuator.eval prec deg b formula (A.TaylorValuator.TM.var ::
        map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) tail)) A.TaylorValuator.TM.dummy) b b in
    A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true
  | _ => False
  end ->
  A.check_p check (nth n (eval_ext formula (map A.xreal_from_bp bounds)) Xnan).
Proof.
intros [|[x [|l u] Hx] bounds] check formula prec deg depth n ; try easy.
pose (f := fun x => nth n (eval_ext formula (x :: map (fun b => Xmask (A.xreal_from_bp b) x) bounds)) Xnan).
pose (fi := fun b => A.TaylorValuator.TM.eval (prec, deg)
  (nth n (A.TaylorValuator.eval prec deg b formula (A.TaylorValuator.TM.var ::
    map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) bounds)) A.TaylorValuator.TM.dummy)
  b b).
change (A.bisect_1d l u (fun b => A.check_f check (fi b)) depth = true -> A.check_p check (f (Xreal x))).
intros H.
apply A.bisect_1d_correct with (P := fun x => A.check_p check (f x)) (2 := H) (3 := Hx).
intros y yi Hy Hb.
destruct check as [b P HP].
apply (HP (f y) (fi yi)) with (2 := Hb).
now apply A.TaylorValuator.eval_correct_ext.
Qed.

(*
Lemma interval_helper_bisection_first_order :
  forall bounds output formula prec depth n,
  match bounds with
  | cons (V.Bproof _ (interval_float.Ibnd l u) _) tail =>
    V.Algos.bisect_1d (fun b => V.eval_first_order_nth prec formula (map V.interval_from_bp tail) n b) l u output depth = true
  | _ => False
  end ->
  contains (I.convert output) (nth n (V.eval_ext formula (map V.xreal_from_bp bounds)) (Xreal 0)).
intro.
case bounds.
intros.
elim H.
intro.
case b.
intros x xi.
case xi.
intros.
elim H.
intros.
clear bounds b xi.
pose (f := fun x => nth n (V.eval_ext formula (x :: map V.xreal_from_bp l0)) (Xreal 0)).
pose (fi := fun b => V.eval_first_order_nth prec formula (map V.interval_from_bp l0) n b).
change (contains (I.convert output) (f (Xreal x))).
refine (V.Algos.bisect_1d_correct depth f fi _ _ _ _ H _ c).
exact (V.eval_first_order_correct_ext _ _ _ _).
Qed.
*)

Definition prec_of_nat prec :=
  match Z_of_nat prec with Zpos p => F.PtoP p | _ => F.PtoP xH end.

Ltac do_interval vars prec depth eval_tac :=
  (abstract (
    xalgorithm vars ;
    match goal with
    | |- A.check_p ?check (nth ?n (eval_ext ?formula (map Xreal ?constants)) Xnan) =>
      let prec := eval vm_compute in (prec_of_nat prec) in
      match get_bounds constants prec with
      | (?bounds_, ?lw) =>
        warn_whole lw ;
        let bounds := fresh "bounds" in
        pose (bounds := bounds_) ;
        change (map Xreal constants) with (map A.xreal_from_bp bounds) ;
        eval_tac bounds check formula prec depth n ;
        vm_cast_no_check (refl_equal true)
      end
    end)) ||
  fail 100 "Numerical evaluation failed to conclude. You may want to adjust some parameters.".

Ltac do_interval_eval bounds output formula prec depth n :=
  refine (interval_helper_evaluate bounds output formula prec n _).

Ltac do_interval_bisect bounds output formula prec depth n :=
  refine (interval_helper_bisection bounds output formula prec depth n _).

Ltac do_interval_bisect_diff bounds output formula prec depth n :=
  refine (interval_helper_bisection_diff bounds output formula prec depth n _).

Ltac do_interval_bisect_taylor deg bounds output formula prec depth n :=
  refine (interval_helper_bisection_taylor bounds output formula prec deg depth n _).

Ltac tuple_to_list params l :=
  match params with
  | pair ?a ?b => tuple_to_list a (b :: l)
  | ?b => constr:(b :: l)
  | ?z => fail 100 "Unknown tactic parameter" z "."
  end.

Ltac do_interval_parse params :=
  let rec aux vars prec depth eval_tac params :=
    match params with
    | nil => do_interval vars prec depth eval_tac
    | cons (i_prec ?p) ?t => aux vars p depth eval_tac t
    | cons (i_bisect ?x) ?t => aux (cons x nil) prec depth do_interval_bisect t
    | cons (i_bisect_diff ?x) ?t => aux (cons x nil) prec depth do_interval_bisect_diff t
    | cons (i_bisect_taylor ?x ?d) ?t => aux (cons x nil) prec depth ltac:(do_interval_bisect_taylor d) t
    | cons (i_depth ?d) ?t => aux vars prec d eval_tac t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h "."
    end in
  aux (@nil R) 30%nat 15%nat do_interval_eval params.

Ltac do_interval_generalize t b :=
  match eval vm_compute in (I.convert b) with
  | Inan => fail 100 "Nothing known about" t
  | Ibnd ?l ?u =>
    match goal with
    | |- ?P =>
      match l with
      | Xnan =>
        match u with
        | Xnan => fail 100 "Nothing known about" t
        | Xreal ?u => refine ((_ : (t <= u)%R -> P) _)
        end
      | Xreal ?l =>
        match u with
        | Xnan => refine ((_ : (l <= t)%R -> P) _)
        | Xreal ?u => refine ((_ : (l <= t <= u)%R -> P) _)
        end
      end
    end
  end.

Ltac do_interval_intro_eval extend bounds formula prec depth :=
  eval vm_compute in (extend (nth 0 (A.BndValuator.eval prec formula (map A.interval_from_bp bounds)) I.nai)).

Ltac do_interval_intro_bisect extend bounds formula prec depth :=
  eval vm_compute in
   (match bounds with
    | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
      A.lookup_1d (fun b => nth 0 (A.BndValuator.eval prec formula (b :: map A.interval_from_bp tail)) I.nai) l u extend depth
    | _ => I.nai
    end).

Ltac do_interval_intro_bisect_diff extend bounds formula prec depth :=
  eval vm_compute in
   (match bounds with
    | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
      A.lookup_1d (fun b => A.DiffValuator.eval prec formula (map A.interval_from_bp tail) 0 b) l u extend depth
    | _ => I.nai
    end).

Ltac do_interval_intro_bisect_taylor deg extend bounds formula prec depth :=
  eval vm_compute in
   (match bounds with
    | cons (A.Bproof _ (Interval_interval_float.Ibnd l u) _) tail =>
      A.lookup_1d (fun b => A.TaylorValuator.TM.eval (prec, deg) (nth 0 (A.TaylorValuator.eval prec deg b formula (A.TaylorValuator.TM.var :: map (fun b => A.TaylorValuator.TM.const (A.interval_from_bp b)) tail)) A.TaylorValuator.TM.dummy) b b) l u extend depth
    | _ => I.nai
    end).

Ltac do_interval_intro t extend params vars prec depth eval_tac :=
  let prec := eval vm_compute in (prec_of_nat prec) in
  match extract_algorithm t vars with
  | (?formula, ?constants) =>
    match get_bounds constants prec with
    | (?bounds, ?lw) =>
      warn_whole lw ;
      let v := eval_tac extend bounds formula prec depth in
      do_interval_generalize t v ;
      [ | do_interval_parse params ]
    end
  end.

Ltac do_interval_intro_parse t_ extend params_ :=
  let rec aux vars prec depth eval_tac params :=
    match params with
    | nil => do_interval_intro t_ extend params_ vars prec depth eval_tac
    | cons (i_prec ?p) ?t => aux vars p depth eval_tac t
    | cons (i_bisect ?x) ?t => aux (cons x nil) prec depth do_interval_intro_bisect t
    | cons (i_bisect_diff ?x) ?t => aux (cons x nil) prec depth do_interval_intro_bisect_diff t
    | cons (i_bisect_taylor ?x ?d) ?t => aux (cons x nil) prec depth ltac:(do_interval_intro_bisect_taylor d) t
    | cons (i_depth ?d) ?t => aux vars prec d eval_tac t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h "."
    end in
  aux (@nil R) 30%nat 5%nat do_interval_intro_eval params_.

End Private.

Import Private.

Tactic Notation "interval" :=
  do_interval_parse (@nil interval_tac_parameters).

Tactic Notation "interval" "with" constr(params) :=
  do_interval_parse ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "interval_intro" constr(t) :=
  do_interval_intro_parse t (fun v : I.type => v) (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" :=
  do_interval_intro_parse t I.upper_extent (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "upper"  :=
  do_interval_intro_parse t I.lower_extent (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "with" constr(params) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "as" simple_intropattern(H) :=
  do_interval_intro_parse t (fun v : I.type => v) (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.upper_extent (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "as" simple_intropattern(H)  :=
  do_interval_intro_parse t I.lower_extent (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

End IntervalTactic.

(*Require Import Interval_stdz_carrier.*)
Require Import Interval_bigint_carrier.
Require Import Interval_specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.
Module ITSFBI2 := IntervalTactic SFBI2.
Export ITSFBI2.

(*
Require Import Interval_generic_ops.
Module GFSZ2 := GenericFloat Radix2.
Module ITGFSZ2 := IntervalTactic GFSZ2.
Export ITGFSZ2.
*)

(*
Lemma blo1 :
  forall x, (Rabs x <= 5)%R ->
  (-4 <= x + 1)%R.
intros.
interval.
Qed.
*)

(*
Lemma blo2 :
  (2/3 <= 5/7)%R.
intros.
interval_intro (5/7)%R lower with (i_prec 4%nat).
apply Rle_trans with (2 := H).
interval.
Qed.

Print blo2.
*)

(*
Lemma blo3 :
  forall x, (x <= 0)%R ->
  (0 <= x - x <= 0)%R.
intros.
Time interval with (i_bisect_diff x).
Qed.
*)

(*
Lemma blo4 :
  forall x, (3/2 <= x <= 2)%R ->
  forall y, (1 <= y <= 33/32)%R ->
  (Rabs (sqrt(1 + x/sqrt(x+y)) - 144/1000*x - 118/100) <= 71/32768)%R.
intros.
interval with (i_bisect x).
Qed.
*)

(*
Lemma blo5 :
  forall x, (-1 <= x <= 1)%R ->
  (0 <= exp x - (1 + x) <= 3/4)%R.
Proof.
intros.
interval_intro (1 + x)%R with (i_bisect_taylor x 2).
interval with (i_bisect_taylor x 2).
Qed.
*)

(*
Lemma pi10 : (31415926535/10000000000 < PI < 31415926536/10000000000)%R.
Proof.
split; interval with (i_prec 40).
Qed.
*)
