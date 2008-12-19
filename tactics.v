Require Import Reals.
Require Import List.
Require Import missing.
Require Import ZArith.
Require Import BigN.
Require Import BigZ.
Require Import xreal.
Require Import definitions.
Require Import generic.
Require Import generic_proof.
(*Require Import stdz_carrier.*)
Require Import bigint_carrier.
Require Import specific_ops.
Require Import interval.
Require Import interval_float_full.
Require Import bisect.

(*Module C := StdZRadix2.*)
Module C := BigIntRadix2.
Module F := SpecificFloat C.
Module I := FloatIntervalFull F.
Module V := Valuator I.

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
    eval vm_compute in (F.fromF (generic.Float 2 s m (Zneg e))) in
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
    | (?m, ?e) => eval vm_compute in (F.fromF (generic.Float 2 s m e))
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
  | generic.Float false m e => (Rabs v <= FtoR F.radix false m e)%R
  | _ => True
  end.
intros [|m e] v (H1, H2).
exact I.
case_eq (F.toF (Float m e)) ; trivial.
intro b. case b ; trivial.
clear b.
intros.
apply Rabs_def1_le.
unfold I.I.convert_bound in H2.
rewrite H in H2.
exact H2.
unfold I.I.convert_bound in H1.
rewrite F.neg_correct in H1.
rewrite Fneg_correct in H1.
rewrite H in H1.
exact H1.
Qed.

Lemma Rabs_contains_rev :
  forall f v,
  match F.toF f with
  | generic.Float false m e => (Rabs v <= FtoR F.radix false m e)%R
  | _ => False
  end ->
  contains (I.convert (I.bnd (F.neg f) f)) (Xreal v).
intros [|m e] v.
do 2 split.
case_eq (F.toF (Float m e)) ; try (intros ; elim H0).
intros b p z.
case b ; intros.
elim H0.
generalize (Rabs_def2_le _ _ H0).
clear H0. intros (H1, H2).
split ; unfold I.I.convert_bound.
rewrite F.neg_correct.
rewrite Fneg_correct.
rewrite H.
exact H1.
rewrite H.
exact H2.
Qed.

Inductive expr :=
  | Econst : nat -> expr
  | Eunary : V.unary_op -> expr -> expr
  | Ebinary : V.binary_op -> expr -> expr -> expr.

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
      | Ropp ?a => aux_u V.Neg a
      | Rabs ?a => aux_u V.Abs a
      | Rinv ?a => aux_u V.Inv a
      | Rsqr ?a => aux_u V.Sqr a
      | Rmult ?a ?a => aux_u V.Sqr a
      | sqrt ?a => aux_u V.Sqrt a
      | cos ?a => aux_u V.Cos a
      | sin ?a => aux_u V.Sin a
      | tan ?a => aux_u V.Tan a
      | atan ?a => aux_u V.Atan a
      | exp ?a => aux_u V.Exp a
      | Rplus ?a ?b => aux_b V.Add a b
      | Rminus ?a ?b => aux_b V.Sub a b
      | Rplus ?a (Ropp ?b) => aux_b V.Sub a b
      | Rmult ?a ?b => aux_b V.Mul a b
      | Rdiv ?a ?b => aux_b V.Div a b
      | Rmult ?a (Rinv ?b) => aux_b V.Div a b
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
          constr:(V.Unary o u)
        | Ebinary ?o ?a ?b =>
          let u := list_find2 a l in
          let v := list_find2 b l in
          constr:(V.Binary o u v)
        end in
      aux l (cons m q)
    end in
  aux l (@nil V.term).

Ltac extract_algorithm t l :=
  match remove_constants t l with
  | (?t, ?lc) =>
    let lm := generate_machine ltac:(get_non_constants t) in
    constr:(lm, lc)
  end.

Ltac xalgorithm lx :=
  match goal with
  | |- Rle ?a ?b /\ Rle ?b ?c =>
    let v := get_float a in
    let w := get_float c in
    change (contains (I.convert (I.bnd v w)) (Xreal b))
  | |- Rle (Rabs ?a) ?b =>
    let v := get_float b in
    match v with
    | Float ?m ?e => refine (Rabs_contains v a _)
    end
  | |- Rle ?a ?b =>
    let v := get_float b in
    refine (proj2 (_ : contains (I.convert (I.bnd F.nan v)) (Xreal a)))
  | |- Rle ?a ?b =>
    let v := get_float a in
    refine (proj1 (_ : contains (I.convert (I.bnd v F.nan)) (Xreal b)))
  | _ => fail 100 "Goal is not an inequality with floating-point bounds."
  end ;
  match goal with
  | |- contains ?xi (Xreal ?y) =>
    match extract_algorithm y lx with
    | (?a, ?b) =>
      let formula := fresh "formula" in
      pose (formula := a) ;
      refine (V.xreal_to_real formula b O xi _)
    end
  end.

Ltac get_bounds l :=
  let rec aux l :=
    match l with
    | nil => constr:(@nil V.bound_proof)
    | cons ?x ?l =>
      let i :=
        match goal with
        | H: Rle ?a x /\ Rle x ?b |- _ =>
          let v := get_float a in
          let w := get_float b in
          constr:(V.Bproof x (I.bnd v w) H)
        | H: Rle ?a x |- _ =>
          let v := get_float a in
          constr:(V.Bproof x (I.bnd v F.nan) (conj H I))
        | H: Rle x ?b |- _ =>
          let v := get_float b in
          constr:(V.Bproof x (I.bnd F.nan v) (conj I H))
        | H: Rle (Rabs x) ?b |- _ =>
          let v := get_float b in
          match v with
          | Float ?m ?e =>
            constr:(V.Bproof x (I.bnd (F.neg v) v) (Rabs_contains_rev v x H))
          end
        | _ =>
          let v := get_float x in
          constr:(let f := v in V.Bproof x (I.bnd f f) (conj (Rle_refl x) (Rle_refl x)))
        | _ => fail 100 "Atom" x "is neither a floating-point value nor bounded by floating-point values."
        end in
      let m := aux l in
      constr:(cons i m)
    end in
  aux l.

Lemma interval_helper_evaluate :
  forall bounds output formula prec n,
  I.subset (nth n (V.eval_bnd prec formula (map V.interval_from_bp bounds)) I.nai) output = true ->
  contains (I.convert output) (nth n (V.eval_ext formula (map V.xreal_from_bp bounds)) (Xreal 0)).
intros.
eapply subset_contains.
apply I.subset_correct.
apply H.
apply V.eval_bnd_correct.
Qed.

Lemma interval_helper_bisection :
  forall bounds output formula prec depth n,
  match bounds with
  | cons (V.Bproof _ (interval_float.Ibnd l u) _) tail =>
    V.Algos.bisect_1d (fun b => nth n (V.eval_bnd prec formula (b :: map V.interval_from_bp tail)) I.nai) l u output depth = true
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
pose (fi := fun b => nth n (V.eval_bnd prec formula (b :: map V.interval_from_bp l0)) I.nai).
change (contains (I.convert output) (f (Xreal x))).
refine (V.Algos.bisect_1d_correct depth f fi _ _ _ _ H _ c).
exact (V.eval_bnd_correct_ext _ _ _ _).
Qed.

Lemma interval_helper_bisection_diff :
  forall bounds output formula prec depth n,
  match bounds with
  | cons (V.Bproof _ (interval_float.Ibnd l u) _) tail =>
    V.Algos.bisect_1d (fun b => V.eval_diff prec formula (map V.interval_from_bp tail) n b) l u output depth = true
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
pose (fi := fun b => V.eval_diff prec formula (map V.interval_from_bp l0) n b).
change (contains (I.convert output) (f (Xreal x))).
refine (V.Algos.bisect_1d_correct depth f fi _ _ _ _ H _ c).
exact (V.eval_diff_correct_ext _ _ _ _).
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

Ltac do_interval vars prec depth eval_tac check_tac :=
  match goal with
  | |- contains (I.convert _) (nth _ (V.eval_ext _ (map Xreal _)) (Xreal 0)) => idtac
  | _ => xalgorithm vars
  end ;
  match goal with
  | |- contains (I.convert ?output) (nth ?n
      (V.eval_ext ?formula (map Xreal ?constants)) (Xreal 0)) =>
    let bounds_ := get_bounds constants in
    let bounds := fresh "bounds" in
    pose (bounds := bounds_) ;
    let prec := eval vm_compute in (C.ZtoE (Z_of_nat prec)) in
    change (map Xreal constants) with (map V.xreal_from_bp bounds) ;
    eval_tac bounds output formula prec depth n ;
    check_tac
  end.

Ltac do_interval_check :=
  vm_compute ;
  try exact (refl_equal true) ;
  fail 100 "Numerical evaluation failed to conclude. You may want to adjust some parameters.".

Ltac do_interval_nocheck :=
  vm_cast_no_check (refl_equal true).

Ltac do_interval_eval bounds output formula prec depth n :=
  refine (interval_helper_evaluate bounds output formula prec n _).

Ltac do_interval_bisect bounds output formula prec depth n :=
  refine (interval_helper_bisection bounds output formula prec depth n _).

Ltac do_interval_bisect_diff bounds output formula prec depth n :=
  refine (interval_helper_bisection_diff bounds output formula prec depth n _).

Inductive interval_tac_parameters :=
  | i_prec : nat -> interval_tac_parameters
  | i_nocheck : interval_tac_parameters
  | i_bisect : R -> interval_tac_parameters
  | i_bisect_diff : R -> interval_tac_parameters
  | i_depth : nat -> interval_tac_parameters.

Ltac tuple_to_list params l :=
  match params with
  | pair ?a ?b => tuple_to_list a (b :: l)
  | ?b => constr:(b :: l)
  end.

Ltac do_interval_parse params :=
  let rec aux vars prec depth eval_tac check_tac params :=
    match params with
    | nil => do_interval vars prec depth eval_tac check_tac
    | cons (i_prec ?p) ?t => aux vars p depth eval_tac check_tac t
    | cons i_nocheck ?t => aux vars prec depth eval_tac do_interval_nocheck t
    | cons (i_bisect ?x) ?t => aux (cons x nil) prec depth do_interval_bisect check_tac t
    | cons (i_bisect_diff ?x) ?t => aux (cons x nil) prec depth do_interval_bisect_diff check_tac t
    | cons (i_depth ?d) ?t => aux vars prec d eval_tac check_tac t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h "."
    end in
  aux (@nil R) 30%nat 15%nat do_interval_eval do_interval_check params.

Tactic Notation "interval" :=
  do_interval_parse (@nil interval_tac_parameters).

Tactic Notation "interval" "with" constr(params) :=
  do_interval_parse ltac:(tuple_to_list params (@nil interval_tac_parameters)).

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
  eval vm_compute in (extend (nth 0 (V.eval_bnd prec formula (map V.interval_from_bp bounds)) I.nai)).

Ltac do_interval_intro_bisect extend bounds formula prec depth :=
  eval vm_compute in
   (match bounds with
    | cons (V.Bproof _ (interval_float.Ibnd l u) _) tail =>
      V.Algos.lookup_1d (fun b => nth 0 (V.eval_bnd prec formula (b :: map V.interval_from_bp tail)) I.nai) l u extend depth
    | _ => I.nai
    end).

Ltac do_interval_intro_bisect_diff extend bounds formula prec depth :=
  eval vm_compute in
   (match bounds with
    | cons (V.Bproof _ (interval_float.Ibnd l u) _) tail =>
      V.Algos.lookup_1d (fun b => V.eval_diff prec formula (map V.interval_from_bp tail) 0 b) l u extend depth
    | _ => I.nai
    end).

Ltac do_interval_intro t extend params vars prec depth eval_tac :=
  let prec := eval vm_compute in (C.ZtoE (Z_of_nat prec)) in
  match extract_algorithm t vars with
  | (?formula, ?constants) =>
    let bounds := get_bounds constants in
    let v := eval_tac extend bounds formula prec depth in
    do_interval_generalize t v ;
    [ intro | do_interval_parse params ]
  end.

Ltac do_interval_intro_parse t_ extend params_ :=
  let rec aux vars prec depth eval_tac params :=
    match params with
    | nil => do_interval_intro t_ extend params_ vars prec depth eval_tac
    | cons (i_prec ?p) ?t => aux vars p depth eval_tac t
    | cons i_nocheck ?t => aux vars prec depth eval_tac t
    | cons (i_bisect ?x) ?t => aux (cons x nil) prec depth do_interval_intro_bisect t
    | cons (i_bisect_diff ?x) ?t => aux (cons x nil) prec depth do_interval_intro_bisect_diff t
    | cons (i_depth ?d) ?t => aux vars prec d eval_tac t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h "."
    end in
  aux (@nil R) 30%nat 5%nat do_interval_intro_eval params_.

Tactic Notation "interval_intro" constr(t) :=
  do_interval_intro_parse t (fun v : I.type => v) (cons i_nocheck nil).

Tactic Notation "interval_intro" constr(t) "lower" :=
  do_interval_intro_parse t I.upper_extent (cons i_nocheck nil).

Tactic Notation "interval_intro" constr(t) "upper"  :=
  do_interval_intro_parse t I.lower_extent (cons i_nocheck nil).

Tactic Notation "interval_intro" constr(t) "with" constr(params) :=
  do_interval_intro_parse t (fun v : I.type => v) ltac:(tuple_to_list params (cons i_nocheck nil)).

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) :=
  do_interval_intro_parse t I.upper_extent ltac:(tuple_to_list params (cons i_nocheck nil)).

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) :=
  do_interval_intro_parse t I.lower_extent ltac:(tuple_to_list params (cons i_nocheck nil)).

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
