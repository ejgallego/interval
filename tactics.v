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
Require Import stdz_carrier.
Require Import bigint_carrier.
Require Import specific_ops.
Require Import interval.
Require Import interval_float.
Require Import bisect.

(*Module C := StdZRadix2.*)
Module C := BigIntRadix2.
Module F := SpecificFloat C.
Module I := FloatInterval F.
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
    eval vm_compute in (F.fromF (Float 2 s m (Zneg e))) in
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
    | (?m, ?e) => eval vm_compute in (F.fromF (Float 2 s m e))
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
  forall m e v,
  contains (I.convert (I.bnd (F.Float true m e) (F.Float false m e))) (Xreal v) ->
  match F.toF (F.Float false m e) with
  | generic.Float false m e => (Rabs v <= FtoR F.radix false m e)%R
  | _ => True
  end.
intros m e v (H1, H2).
case_eq (F.toF (F.Float false m e)) ; trivial.
intro b. case b ; trivial.
clear b.
intros.
apply Rabs_def1_le.
unfold I.convert_bound in H2.
rewrite H in H2.
exact H2.
unfold I.convert_bound in H1.
change (F.Float true m e) with (F.neg (F.Float false m e)) in H1.
rewrite F.neg_correct in H1.
rewrite Fneg_correct in H1.
rewrite H in H1.
exact H1.
Qed.

Lemma Rabs_contains_rev :
  forall m e v,
  match F.toF (F.Float false m e) with
  | generic.Float false m e => (Rabs v <= FtoR F.radix false m e)%R
  | _ => False
  end ->
  contains (I.convert (I.bnd (F.Float true m e) (F.Float false m e))) (Xreal v).
intros m e v.
case_eq (F.toF (F.Float false m e)) ; try (intros ; elim H0).
intros b p z.
case b ; intros.
elim H0.
generalize (Rabs_def2_le _ _ H0).
clear H0. intros (H1, H2).
split ; unfold I.convert_bound.
change (F.Float true m e) with (F.neg (F.Float false m e)).
rewrite F.neg_correct.
rewrite Fneg_correct.
rewrite H.
exact H1.
rewrite H.
exact H2.
Qed.

Ltac list_add a l :=
  match l with
  | nil        => constr:(cons a l)
  | cons a _   => l
  | cons ?x ?l => let m := list_add a l in constr:(cons x m)
  end.

Ltac list_find a l :=
  let rec aux n l :=
    match l with
    | nil       => false
    | cons (Rinv R0) ?l => aux n l (* /0 is used as a marker *)
    | cons a _  => n
    | cons _ ?l => aux (S n) l
    end in
  aux O l.

Ltac get_algorithm t l :=
  let get_constants t l :=
    let rec aux t l :=
      match get_float t with
      | false =>
        match t with
        | Ropp ?a => aux a l
        | Rabs ?a => aux a l
        | sqrt ?a => aux a l
        | Rplus ?a ?b => aux a ltac:(aux b l)
        | Rminus ?a ?b => aux a ltac:(aux b l)
        | Rmult ?a ?b => aux a ltac:(aux b l)
        | Rdiv ?a ?b => aux a ltac:(aux b l)
        | Rmult ?a (Rinv ?b) => aux a ltac:(aux b l)
        | _ => list_add t l
        end
      | _ => list_add t l
      end in
    aux t l in
  let get_terms t l :=
    let rec aux t l :=
      match list_find t l with
      | false =>
        let m :=
          match t with
          | Ropp ?a => aux a l
          | Rabs ?a => aux a l
          | sqrt ?a => aux a l
          | Rplus ?a ?b => aux a ltac:(aux b l)
          | Rminus ?a ?b => aux a ltac:(aux b l)
          | Rmult ?a ?b => aux a ltac:(aux b l)
          | Rdiv ?a ?b => aux a ltac:(aux b l)
          | Rmult ?a (Rinv ?b) => aux a ltac:(aux b l)
          end in
        constr:(cons t m)
      | _ => l
      end in
    let m := constr:(cons (Rinv R0) l) in
    aux t m in
  let rec generate l q :=
    match l with
    | cons (Rinv R0) ?l => constr:(q, l)
    | cons ?t ?l =>
      let m :=
        match t with
        | Ropp ?a =>
          let u := list_find a l in constr:(V.Unary V.Neg u)
        | Rabs ?a =>
          let u := list_find a l in constr:(V.Unary V.Abs u)
        | sqrt ?a =>
          let u := list_find a l in constr:(V.Unary V.Sqrt u)
        | Rplus ?a ?b =>
          let u := list_find a l in
          let v := list_find b l in constr:(V.Binary V.Add u v)
        | Rminus ?a ?b =>
          let u := list_find a l in
          let v := list_find b l in constr:(V.Binary V.Sub u v)
        | Rmult ?a ?b =>
          let u := list_find a l in
          let v := list_find b l in constr:(V.Binary V.Mul u v)
        | Rdiv ?a ?b =>
          let u := list_find a l in
          let v := list_find b l in constr:(V.Binary V.Div u v)
        | Rmult ?a (Rinv ?b) =>
          let u := list_find a l in
          let v := list_find b l in constr:(V.Binary V.Div u v)
        end in
      generate l (cons m q)
    end in
  generate ltac:(get_terms t ltac:(get_constants t l)) (@nil V.term).

Ltac xalgorithm lx :=
  match goal with
  | |- Rle ?a ?b /\ Rle ?b ?c =>
    let v := get_float a in
    let w := get_float c in
    change (contains (I.convert (I.bnd v w)) (Xreal b))
  | |- Rle (Rabs ?a) ?b =>
    let v := get_float b in
    match v with
    | F.Float false ?m ?e => refine (Rabs_contains m e a _)
    end
  | |- Rle ?a ?b =>
    let v := get_float b in
    refine ((fun (p : contains (I.convert (I.bnd F.nan v)) (Xreal a)) => match p with conj _ q => q end) _)
  | |- Rle ?a ?b =>
    let v := get_float a in
    refine ((fun (p : contains (I.convert (I.bnd v F.nan)) (Xreal b)) => match p with conj q _ => q end) _)
  | _ => fail 100 "Goal is not an inequality with floating-point bounds."
  end ;
  match goal with
  | |- contains ?xi (Xreal ?y) =>
    match get_algorithm y lx with
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
          constr:(V.Bproof (Xreal x) (I.bnd v w) H)
        | H: Rle ?a x |- _ =>
          let v := get_float a in
          constr:(V.Bproof (Xreal x) (I.bnd v F.nan) (conj H I))
        | H: Rle x ?b |- _ =>
          let v := get_float b in
          constr:(V.Bproof (Xreal x) (I.bnd F.nan v) (conj I H))
        | H: Rle (Rabs x) ?b |- _ =>
          let v := get_float b in
          match v with
          | F.Float false ?m ?e =>
            constr:(V.Bproof (Xreal x) (I.bnd (F.Float true m e) v) (Rabs_contains_rev m e x H))
          end
        | _ =>
          let v := get_float x in
          constr:(let f := v in V.Bproof (Xreal x) (I.bnd f f) (conj (Rle_refl x) (Rle_refl x)))
        | _ => fail 100 "Atom" x "is neither a floating-point value nor bounded by floating-point values."
        end in
      let m := aux l in
      constr:(cons i m)
    end in
  aux l.

Lemma interval_helper_evaluate :
  forall bounds output formula prec n,
  I.subset (nth n (V.eval_bnd prec formula (map V.interval_from_bp bounds)) I.Inan) output = true ->
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
  | cons (V.Bproof _ (I.Ibnd l u) _) tail =>
    V.Algos.bisect_1d (fun b => nth n (V.eval_bnd prec formula (b :: map V.interval_from_bp tail)) I.Inan) l u output depth = true
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
pose (fi := fun b => nth n (V.eval_bnd prec formula (b :: map V.interval_from_bp l0)) I.Inan).
change (contains (I.convert output) (f x)).
refine (V.Algos.bisect_1d_correct depth f fi _ _ _ _ H _ c).
exact (V.eval_bnd_correct_ext _ _ _ _).
Qed.

Lemma interval_helper_bisection_diff :
  forall bounds output formula prec depth n,
  match bounds with
  | cons (V.Bproof _ (I.Ibnd l u) _) tail =>
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
change (contains (I.convert output) (f x)).
refine (V.Algos.bisect_1d_correct depth f fi _ _ _ _ H _ c).
exact (V.eval_diff_correct_ext _ _ _ _).
Qed.

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
  let rec aux params l :=
    match params with
    | pair ?a ?b => aux a (b :: l)
    | ?b => constr:(b :: l)
    end in
  do_interval_parse ltac:(aux params (@nil interval_tac_parameters)).

Ltac generalize_interval t b :=
  match b with
  | I.Inan => fail 100 "Nothing known about" t
  | I.Ibnd ?l ?u =>
    let l := eval vm_compute in (FtoX (F.toF l)) in
    let u := eval vm_compute in (FtoX (F.toF u)) in
    match l with
    | Xnan =>
      match u with
      | Xnan => fail 100 "Nothing known about" t
      | Xreal ?u => refine ((_ : (t <= u)%R -> _) (proj2 _))
      end
    | Xreal ?l =>
      match u with
      | Xnan => refine ((_ : (l <= t)%R -> _) (proj1 _))
      | Xreal ?u => refine ((_ : (l <= t <= u)%R -> _) _)
      end
    | _ => idtac l
    end
  end.

Ltac interval_intro t :=
  let prec := eval vm_compute in (C.ZtoE (Z_of_nat 30%nat)) in
  match get_algorithm t (@nil R) with
  | (?formula, ?constants) =>
    let bounds := get_bounds constants in
    let v := eval vm_compute in (nth 0 (V.eval_bnd prec formula (map V.interval_from_bp bounds)) I.Inan) in
    generalize_interval t v ;
    [ intro | do_interval (@nil R) 30%nat 15%nat do_interval_eval do_interval_nocheck
      (*let formula_ := fresh "algo" in
      pose (formula_ := formula) ;
      let bounds_ := fresh "bounds" in
      pose (bounds_ := bounds) ;
      refine (V.xreal_to_real formula_ constants 0 (I.convert v)
        (interval_helper_evaluate bounds_ v formula_ prec 0 _)) ;
      vm_cast_no_check (refl_equal true)*) ]
  end.

(*
Lemma blo :
  forall x, (Rabs x <= 5)%R ->
  (-4 <= x + 1)%R.
intros.
interval.
Qed.
*)

(*
Lemma blo :
  forall x, (0 <= x)%R ->
  (2/3 <= 5/7)%R.
intros.
interval_intro (2/3)%R.
apply Rle_trans with (1 := proj2 H0).
interval.
Qed.
*)

(*
Lemma blo :
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
bisect x.
Qed.
Print blo4.
*)
