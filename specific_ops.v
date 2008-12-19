Require Import ZArith.
Require Import Bool.
Require Import missing.
Require Import xreal.
Require Import definitions.
Require Import generic.
Require Import generic_proof.
Require Import float_sig.
Require Import specific_sig.

Inductive s_float (smantissa_type exponent_type : Type) : Type :=
  | Fnan : s_float smantissa_type exponent_type
  | Float : smantissa_type -> exponent_type -> s_float smantissa_type exponent_type.

Implicit Arguments Fnan [smantissa_type exponent_type].
Implicit Arguments Float [smantissa_type exponent_type].

Module SpecificFloat (Carrier : FloatCarrier) <: FloatOps.

Import Carrier.

Definition radix := radix.
Definition even_radix := match radix with xO _ => true | _ => false end.
Definition radix_correct := radix_correct.
Definition even_radix_correct := refl_equal even_radix.

Definition type := s_float smantissa_type exponent_type.

Definition toF (x : type) :=
  match x with
  | Fnan => generic.Fnan radix
  | Float m e =>
    match mantissa_sign m with
    | Mzero => generic.Fzero radix
    | Mnumber s p => generic.Float radix s (MtoP p) (EtoZ e)
    end
  end.

Definition fromF (f : generic.float radix) :=
  match f with
  | generic.Fnan => Fnan
  | generic.Fzero => Float mantissa_zero exponent_zero
  | generic.Float false m e => Float (ZtoM (Zpos m)) (ZtoE e)
  | generic.Float true m e => Float (ZtoM (Zneg m)) (ZtoE e)
  end.

Definition precision := exponent_type.
Definition sfactor := exponent_type.
Definition prec p := match EtoZ p with Zpos q => q | _ => xH end.
Definition ZtoS := ZtoE.
Definition StoZ := EtoZ.
Definition PtoP n := ZtoE (Zpos n).
Definition incr_prec x y := exponent_add x (ZtoE (Zpos y)).

Definition zero := Float mantissa_zero exponent_zero.
Definition nan := @Fnan smantissa_type exponent_type.
Definition nan_correct := refl_equal (generic.Fnan radix).

Lemma zero_correct :
  toF zero = generic.Fzero radix.
generalize (mantissa_sign_correct mantissa_zero).
simpl.
case (mantissa_sign mantissa_zero).
trivial.
rewrite mantissa_zero_correct.
intros s p.
case s ; intros (H, _) ; discriminate H.
Qed.

Definition mag (x : type) :=
  match x with
  | Fnan => exponent_zero
  | Float m e =>
    match mantissa_sign m with
    | Mzero => e
    | Mnumber _ m => exponent_add e (mantissa_digits m)
    end
  end.

Definition real (f : type) := match f with Fnan => false | _ => true end.
Lemma real_correct :
  forall f, match toF f with generic.Fnan => real f = false | _ => real f = true end.
intros.
case f ; simpl.
apply refl_equal.
intros m e.
now case (mantissa_sign m).
Qed.

Definition fromZ n := Float (ZtoM n) exponent_zero.

Lemma fromZ_correct :
  forall n, FtoX (toF (fromZ n)) = Xreal (Z2R n).
intros.
simpl.
generalize (mantissa_sign_correct (ZtoM n)).
case_eq (mantissa_sign (ZtoM n)) ; intros ; rewrite ZtoM_correct in *.
rewrite H0.
apply refl_equal.
rewrite exponent_zero_correct.
rewrite (proj1 H0).
now case s.
Qed.

Lemma match_helper_1 :
  forall A B y2, forall f : A -> B,
  forall x y1,
  f (match mantissa_sign x with Mzero => y1 | Mnumber s p => y2 s p end) =
  match mantissa_sign x with Mzero => f y1 | Mnumber s p => f (y2 s p) end.
intros.
now case (mantissa_sign x).
Qed.

(*
Lemma mantissa_sign_correct_zero :
  mantissa_sign mantissa_zero = Mzero.
generalize (mantissa_sign_correct mantissa_zero).
rewrite mantissa_zero_correct.
case (mantissa_sign mantissa_zero).
trivial.
intros s m.
case s ; intros (H1, _) ; try discriminate H1.
Qed.

Lemma mantissa_sign_correct_pos :
  forall p, valid_mantissa p ->
  exists q,
  valid_mantissa q /\ MtoP p = MtoP q /\
  mantissa_sign (mantissa_pos p) = Mnumber false q.
intros.
generalize (mantissa_sign_correct (mantissa_pos p)).
rewrite mantissa_pos_correct ; [idtac | exact H].
case (mantissa_sign (mantissa_pos p)).
intro H0. discriminate H0.
intros s m.
case s ; intros (H1, H2) ; try discriminate H1.
exists m.
split.
exact H2.
split.
inversion H1.
apply refl_equal.
apply refl_equal.
Qed.
*)

Definition float_aux s m e : type :=
  Float ((if s : bool then mantissa_neg else mantissa_pos) m) e.

Lemma toF_float :
  forall s p e, valid_mantissa p ->
  toF (float_aux s p e) = generic.Float radix s (MtoP p) (EtoZ e).
intros.
simpl.
generalize (mantissa_sign_correct ((if s then mantissa_neg else mantissa_pos) p)).
case (mantissa_sign ((if s then mantissa_neg else mantissa_pos) p)).
case s.
rewrite mantissa_neg_correct.
intro H0 ; discriminate H0.
exact H.
rewrite mantissa_pos_correct.
intro H0 ; discriminate H0.
exact H.
intros t q.
case s.
rewrite mantissa_neg_correct.
case t ; intros (H1, H2).
now inversion H1.
discriminate H1.
exact H.
rewrite mantissa_pos_correct.
case t ; intros (H1, H2).
discriminate H1.
now inversion H1.
exact H.
Qed.

(*
 * neg
 *)

Definition neg (f : type) :=
  match f with
  | Float m e =>
    match mantissa_sign m with
    | Mzero => f
    | Mnumber s p => Float ((if s then mantissa_pos else mantissa_neg) p) e
    end
  | _ => f
  end.

Lemma neg_correct :
  forall x, FtoX (toF (neg x)) = FtoX (Fneg (toF x)).
intros.
destruct x as [| m e].
apply refl_equal.
simpl.
rewrite (match_helper_1 _ _ (fun (s : bool) p => Float ((if s then mantissa_pos else mantissa_neg) p) e) (fun a => FtoX (toF a))).
rewrite (match_helper_1 _ _ (fun s p => generic.Float radix s (MtoP p) (EtoZ e)) (fun a => FtoX (Fneg a))).
generalize (mantissa_sign_correct m).
case_eq (mantissa_sign m).
simpl.
intros H _.
rewrite H.
apply refl_equal.
intros s p H0 (H1, H2).
generalize (toF_float (negb s) p e H2).
case s ; simpl ;
  intro H ; rewrite H ;
  apply refl_equal.
Qed.

(*
 * abs
 *)

Definition abs (f : type) :=
  match f with
  | Float m e =>
    match mantissa_sign m with
    | Mzero => f
    | Mnumber _ p => Float (mantissa_pos  p) e
    end
  | _ => f
  end.

Lemma abs_correct :
  forall x, FtoX (toF (abs x)) = FtoX (Fabs (toF x)).
intros.
destruct x as [| m e].
apply refl_equal.
simpl.
rewrite (match_helper_1 _ _ (fun (s : bool) p => Float (mantissa_pos p) e) (fun a => FtoX (toF a))).
rewrite (match_helper_1 _ _ (fun s p => generic.Float radix s (MtoP p) (EtoZ e)) (fun a => FtoX (Fabs a))).
generalize (mantissa_sign_correct m).
case_eq (mantissa_sign m).
simpl.
intros H _.
rewrite H.
apply refl_equal.
intros s p H0 (H1, H2).
apply f_equal.
exact (toF_float false p e H2).
Qed.

(*
 * scale
 *)

Definition scale (f : type) d :=
  match f with
  | Float m e => Float m (exponent_add e d)
  | _ => f
  end.

Lemma scale_correct :
  forall x d, FtoX (toF (scale x (ZtoE d))) = FtoX (Fscale (toF x) d).
intros.
case x.
apply refl_equal.
intros m e. simpl.
case (mantissa_sign m).
apply refl_equal.
intros s p.
rewrite exponent_add_correct, ZtoE_correct.
apply refl_equal.
Qed.

(*
 * scale2
 *)

Definition scale2 (f : type) d :=
  match f with
  | Float m e =>
    match mantissa_sign m with
    | Mzero => f
    | Mnumber s p =>
      match mantissa_scale2 p d with
      | (p2, d2) => float_aux s p2 (exponent_add e d2)
      end
    end
  | _ => f
  end.

Axiom scale2_correct :
  forall x d, even_radix = true ->
  FtoX (toF (scale2 x (ZtoE d))) = FtoX (Fscale2 (toF x) d).

(*
 * cmp
 *)

Definition cmp_aux1 m1 m2 :=
  match mantissa_cmp m1 m2 with
  | Eq => Xeq
  | Lt => Xlt
  | Gt => Xgt
  end.

Definition cmp_aux2 m1 e1 m2 e2 :=
  let d1 := mantissa_digits m1 in
  let d2 := mantissa_digits m2 in
  match exponent_cmp (exponent_add e1 d1) (exponent_add e2 d2) with
  | Lt => Xlt
  | Gt => Xgt
  | Eq =>
    let nb := exponent_sub e1 e2 in
    match exponent_cmp nb exponent_zero with
    | Gt => cmp_aux1 (mantissa_shl m1 nb) m2
    | Lt => cmp_aux1 m1 (mantissa_shl m2 (exponent_neg nb))
    | Eq => cmp_aux1 m1 m2
    end
  end.

Lemma cmp_aux2_correct :
  forall m1 e1 m2 e2,
  valid_mantissa m1 -> valid_mantissa m2 ->
  cmp_aux2 m1 e1 m2 e2 = Fcmp_aux2 radix (MtoP m1) (EtoZ e1) (MtoP m2) (EtoZ e2).
intros m1 e1 m2 e2 H1 H2.
unfold cmp_aux2, Fcmp_aux2.
rewrite exponent_cmp_correct.
do 2 rewrite exponent_add_correct.
do 2 (rewrite mantissa_digits_correct ; [idtac | assumption]).
unfold radix.
case (EtoZ e1 + Zpos (count_digits Carrier.radix (MtoP m1))
   ?= EtoZ e2 + Zpos (count_digits Carrier.radix (MtoP m2)))%Z ;
  try apply refl_equal.
rewrite exponent_cmp_correct.
rewrite exponent_zero_correct.
rewrite exponent_sub_correct.
case_eq (EtoZ e1 - EtoZ e2)%Z ; intros ; simpl ;
  unfold cmp_aux1, Fcmp_aux1.
now rewrite mantissa_cmp_correct.
generalize (mantissa_shl_correct p m1 (exponent_sub e1 e2) H1).
rewrite exponent_sub_correct.
refine (fun H0 => _ (proj1 (H0 H)) (proj2 (H0 H))).
clear H0.
intros H3 H4.
rewrite mantissa_cmp_correct.
rewrite H3.
apply refl_equal.
exact H4.
exact H2.
generalize (mantissa_shl_correct p m2 (exponent_neg (exponent_sub e1 e2)) H2).
rewrite exponent_neg_correct.
rewrite exponent_sub_correct.
rewrite H.
refine (fun H0 => _ (proj1 (H0 (refl_equal _))) (proj2 (H0 (refl_equal _)))).
clear H0.
intros H3 H4.
rewrite mantissa_cmp_correct.
rewrite H3.
apply refl_equal.
exact H1.
exact H4.
Qed.

Definition cmp (f1 f2 : type) :=
  match f1, f2 with
  | Fnan, _ => Xund
  | _, Fnan => Xund
  | Float m1 e1, Float m2 e2 =>
    match mantissa_sign m1, mantissa_sign m2 with
    | Mzero, Mzero => Xeq
    | Mzero, Mnumber true _ => Xgt
    | Mzero, Mnumber false _ => Xlt
    | Mnumber true _, Mzero => Xlt
    | Mnumber false _, Mzero => Xgt
    | Mnumber true _, Mnumber false _ => Xlt
    | Mnumber false _, Mnumber true _ => Xgt
    | Mnumber true p1, Mnumber true p2 => cmp_aux2 p2 e2 p1 e1
    | Mnumber false p1, Mnumber false p2 => cmp_aux2 p1 e1 p2 e2
    end
  end.

Lemma cmp_correct :
  forall x y, cmp x y = Fcmp (toF x) (toF y).
intros.
destruct x as [| mx ex].
apply refl_equal.
destruct y as [| my ey].
simpl.
case (mantissa_sign mx) ; intros ; try case s ; apply refl_equal.
simpl.
generalize (mantissa_sign_correct mx) (mantissa_sign_correct my).
case (mantissa_sign mx) ; case (mantissa_sign my).
trivial.
intros sy py.
now case sy.
intros sx px.
now case sx.
intros sy py sx px.
intros (Hx1, Hx2) (Hy1, Hy2).
do 2 (rewrite cmp_aux2_correct ; try assumption).
apply refl_equal.
Qed.

(*
 * min
 *)

Definition min x y :=
  match cmp x y with
  | Xlt => x
  | Xeq => x
  | Xgt => y
  | Xund => nan
  end.

Lemma min_correct :
  forall x y,
  FtoX (toF (min x y)) = FtoX (Fmin (toF x) (toF y)).
intros.
unfold min, Fmin.
rewrite cmp_correct.
case (Fcmp (toF x) (toF y)) ; apply refl_equal.
Qed.

(*
 * max
 *)

Definition max x y :=
  match cmp x y with
  | Xlt => y
  | Xeq => y
  | Xgt => x
  | Xund => nan
  end.

Lemma max_correct :
  forall x y,
  FtoX (toF (max x y)) = FtoX (Fmax (toF x) (toF y)).
intros.
unfold max, Fmax.
rewrite cmp_correct.
case (Fcmp (toF x) (toF y)) ; apply refl_equal.
Qed.

(*
 * round
 *)

Definition need_change radix_ mode m pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | pos_Mi =>
      if mantissa_even m then false
      else match radix_ with xO _ => false | _ => true end
    | _ => false
    end
  end.

Definition adjust_mantissa mode m pos sign :=
  if need_change xH mode m pos sign then mantissa_add m mantissa_one else m.

Definition round_aux mode prec sign m1 e1 pos :=
  let nb := exponent_sub (mantissa_digits m1) prec in
  let e2 := exponent_add e1 nb in
  match exponent_cmp nb exponent_zero with
  | Gt =>
    let (m2, pos2) := mantissa_shr m1 nb pos in
    float_aux sign (adjust_mantissa mode m2 pos2 sign) e2
  | Eq => float_aux sign (adjust_mantissa mode m1 pos sign) e1
  | Lt =>
    if need_change radix mode m1 pos sign then
      let m2 := mantissa_add (mantissa_shl m1 nb) mantissa_one in
      float_aux sign m2 e2
    else float_aux sign m1 e1
  end.

Axiom round_aux_correct :
  forall mode p sign m1 e1 pos,
  valid_mantissa m1 ->
  FtoX (toF (round_aux mode p sign m1 e1 pos)) =
  FtoX (Fround_at_prec mode (prec p) (generic.Ufloat radix sign (MtoP m1) (EtoZ e1) pos)).

Definition round mode prec (f : type) :=
  match f with
  | Float m e =>
    match mantissa_sign m with
    | Mzero => zero
    | Mnumber s p => round_aux mode prec s p e pos_Eq
    end
  | _ => f
  end.

(*
 * mul_exact
 *)

Definition mul_exact (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, _ => x
    | _, Mzero => y
    | Mnumber sx px, Mnumber sy py =>
      float_aux (xorb sx sy) (mantissa_mul px py) (exponent_add ex ey)
    end
  end.

Lemma mul_exact_correct :
  forall x y, FtoX (toF (mul_exact x y)) = FtoX (Fmul_exact (toF x) (toF y)).
intros x y.
destruct x as [| mx ex].
apply refl_equal.
simpl.
destruct y as [| my ey].
now case (mantissa_sign mx).
generalize (mantissa_sign_correct mx) (mantissa_sign_correct my).
case_eq (mantissa_sign mx) ; simpl ; case_eq (mantissa_sign my) ; simpl.
intros _ Hx _ _.
rewrite Hx.
apply refl_equal.
intros sy py _ Hx _ _.
rewrite Hx.
apply refl_equal.
intros Hy sx px _ _ _.
rewrite Hy.
apply refl_equal.
intros sy py _ sx px _ (_, Hx2) (_, Hy2).
generalize (mantissa_mul_correct px py).
intro H.
destruct (H Hx2 Hy2).
clear H.
generalize (mantissa_sign_correct ((if xorb sx sy then mantissa_neg else mantissa_pos)
  (mantissa_mul px py))).
case (mantissa_sign ((if xorb sx sy then mantissa_neg else mantissa_pos)
  (mantissa_mul px py))).
case (xorb sx sy).
rewrite mantissa_neg_correct.
intro H. discriminate H.
exact (proj2 (mantissa_mul_correct _ _ Hx2 Hy2)).
rewrite mantissa_pos_correct.
intro H. discriminate H.
exact (proj2 (mantissa_mul_correct _ _ Hx2 Hy2)).
intros sz pz (Hz1, Hz2).
simpl.
rewrite exponent_add_correct.
rewrite <- H0.
assert (forall A B, forall b : bool, forall f1 f2 : A -> B, forall x, (if b then f1 else f2) x = if b then f1 x else f2 x).
intros.
now case b.
do 2 rewrite H in Hz1.
clear H.
assert (forall A B, forall f : A -> B, forall b : bool, forall x1 x2, f (if b then x1 else x2) = if b then f x1 else f x2).
intros.
now case b.
rewrite (H _ _ MtoZ) in Hz1.
clear H.
rewrite mantissa_neg_correct in Hz1 ; [idtac | exact H1].
rewrite mantissa_pos_correct in Hz1 ; [idtac | exact H1].
generalize Hz1. clear Hz1.
case (xorb sx sy) ; case sz ; intro H ; try discriminate H ; inversion H ; apply refl_equal.
Qed.

(*
 * mul
 *)

Definition mul mode prec (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, _ => x
    | _, Mzero => y
    | Mnumber sx mx, Mnumber sy my =>
      round_aux mode prec (xorb sx sy) (mantissa_mul mx my) (exponent_add ex ey) pos_Eq
    end
  end.

Lemma mul_correct :
  forall mode p x y,
  FtoX (toF (mul mode p x y)) = FtoX (Fmul mode (prec p) (toF x) (toF y)).
intros.
destruct x as [| mx ex].
apply refl_equal.
destruct y as [| my ey].
simpl.
now case (mantissa_sign mx).
simpl.
generalize (mantissa_sign_correct mx).
case_eq (mantissa_sign mx).
simpl.
intros.
rewrite H.
now case (mantissa_sign my).
intros sx px Hx (Hx1, Hx2).
rewrite (match_helper_1 _ _ (fun s py => round_aux mode p (Datatypes.xorb sx s) (mantissa_mul px py)
  (exponent_add ex ey) pos_Eq) (fun a => FtoX (toF a))).
rewrite (match_helper_1 _ _ (fun s p => generic.Float radix s (MtoP p) (EtoZ ey))
  (fun a => FtoX (Fmul mode (prec p) (generic.Float radix sx (MtoP px) (EtoZ ex)) a))).
simpl.
generalize (mantissa_sign_correct my).
case (mantissa_sign my).
trivial.
intros sy py (_, Hy2).
destruct (mantissa_mul_correct px py) as (H1, H2) ; try assumption.
rewrite round_aux_correct.
rewrite H1. clear H1.
rewrite exponent_add_correct.
apply refl_equal.
exact H2.
Qed.

(*
 * add_exact
 *)

Definition add_exact_aux1 sx sy mx my e :=
  if eqb sx sy then
    float_aux sx (mantissa_add mx my) e
  else
    match mantissa_cmp mx my with
    | Eq => zero
    | Gt => float_aux sx (mantissa_sub mx my) e
    | Lt => float_aux sy (mantissa_sub my mx) e
    end.

Definition add_exact_aux2 sx sy mx my ex ey :=
  let nb := exponent_sub ex ey in
  match exponent_cmp nb exponent_zero with
  | Gt => add_exact_aux1 sx sy (mantissa_shl mx nb) my ey
  | Lt => add_exact_aux1 sx sy mx (mantissa_shl my (exponent_neg nb)) ex
  | Eq => add_exact_aux1 sx sy mx my ex
  end.

Definition add_exact (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, _ => y
    | _, Mzero => x
    | Mnumber sx mx, Mnumber sy my =>
      add_exact_aux2 sx sy mx my ex ey
    end
  end.

Lemma add_exact_aux_correct :
  forall sx mx ex sy my ey,
  FtoX (toF (add_exact_aux2 sx sy mx my ex ey)) =
  FtoX (Fround_none (Fadd_slow_aux2 radix sx sy (MtoP mx) (MtoP my) (EtoZ ex) (EtoZ ey))).
intros.
unfold add_exact_aux2, Fround_none, Fadd_slow_aux2.
rewrite exponent_cmp_correct.
rewrite exponent_zero_correct.
rewrite exponent_sub_correct.
Admitted.

Lemma add_exact_correct :
  forall x y, FtoX (toF (add_exact x y)) = FtoX (Fadd_exact (toF x) (toF y)).
intros [|mx ex] y.
apply refl_equal.
destruct y as [|my ey].
simpl.
now case (mantissa_sign mx).
simpl.
generalize (mantissa_sign_correct mx).
case_eq (mantissa_sign mx).
simpl.
now case (mantissa_sign my).
intros sx px Hx (Hx1, Hx2).
generalize (mantissa_sign_correct my).
case (mantissa_sign my).
simpl.
now rewrite Hx.
intros sy py (Hy1, Hy2).
unfold Fadd_exact, Fadd_slow_aux.
apply add_exact_aux_correct.
Qed.

(*
 * add
 *)

Definition add_slow_aux1 mode prec sx sy mx my e :=
  if eqb sx sy then
    round_aux mode prec sx (mantissa_add mx my) e pos_Eq
  else
    match mantissa_cmp mx my with
    | Eq => zero
    | Gt => round_aux mode prec sx (mantissa_sub mx my) e pos_Eq
    | Lt => round_aux mode prec sy (mantissa_sub my mx) e pos_Eq
    end.

Definition add_slow_aux2 mode prec sx sy mx my ex ey :=
  let nb := exponent_sub ex ey in
  match exponent_cmp nb exponent_zero with
  | Gt => add_slow_aux1 mode prec sx sy (mantissa_shl mx nb) my ey
  | Lt => add_slow_aux1 mode prec sx sy mx (mantissa_shl my (exponent_neg nb)) ex
  | Eq => add_slow_aux1 mode prec sx sy mx my ex
  end.

Definition add_slow mode prec (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, Mzero => x
    | Mzero, Mnumber sy py => round_aux mode prec sy py ey pos_Eq
    | Mnumber sx px, Mzero => round_aux mode prec sx px ex pos_Eq
    | Mnumber sx px, Mnumber sy py =>
      add_slow_aux2 mode prec sx sy px py ex ey
    end
  end.

Definition add := add_slow.

Axiom add_correct : forall mode p x y, FtoX (toF (add mode p x y)) = FtoX (Fadd mode (prec p) (toF x) (toF y)).

(*
 * sub_exact
 *)

Definition sub_exact (x y : type) := add_exact x (neg y).

Lemma sub_exact_correct :
  forall x y, FtoX (toF (sub_exact x y)) = FtoX (Fsub_exact (toF x) (toF y)).
intros x y.
unfold sub_exact.
rewrite add_exact_correct.
rewrite Fadd_exact_correct.
rewrite neg_correct.
replace (Fsub_exact (toF x) (toF y)) with (Fadd_exact (toF x) (Fneg (toF y))).
rewrite Fadd_exact_correct.
apply refl_equal.
now case (toF y).
Qed.

(*
 * sub
 *)

Definition sub mode prec (x y : type) := add mode prec x (neg y).

Lemma sub_correct :
  forall mode p x y,
  FtoX (toF (sub mode p x y)) = FtoX (Fsub mode (prec p) (toF x) (toF y)).
intros.
rewrite Fsub_split.
unfold sub.
rewrite add_correct.
do 2 rewrite Fadd_correct.
rewrite neg_correct.
apply refl_equal.
Qed.

(*
 * div
 *)

Definition div_aux mode prec s mx my e :=
  let (q, pos) := mantissa_div mx my in
  round_aux mode prec s q e pos.

Definition div mode prec (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Float mx ex, Float my ey =>
    match mantissa_sign mx, mantissa_sign my with
    | Mzero, _ => x
    | _, Mzero => Fnan
    | Mnumber sx px, Mnumber sy py =>
      let dx := mantissa_digits px in
      let dy := mantissa_digits py in
      let e := exponent_sub ex ey in
      let nb := exponent_sub (exponent_add dy prec) dx in
      match exponent_cmp nb exponent_zero with
      | Gt =>
        div_aux mode prec (xorb sx sy) (mantissa_shl px nb) py (exponent_sub e nb)
      | _ => div_aux mode prec (xorb sx sy) px py e
      end
    end
  end.

Axiom div_correct : forall mode p x y, FtoX (toF (div mode p x y)) = FtoX (Fdiv mode (prec p) (toF x) (toF y)).

(*
 * sqrt
 *)

Definition sqrt_aux2 mode prec m e :=
  let (s, pos) := mantissa_sqrt m in
  round_aux mode prec false s e pos.

Definition sqrt mode prec (f : type) :=
  match f with
  | Fnan => f
  | Float m e =>
    match mantissa_sign m with
    | Mzero => f
    | Mnumber true _ => Fnan
    | Mnumber false p =>
      let d := mantissa_digits p in
      let c := exponent_sub (exponent_add prec prec) (exponent_add d exponent_one) in
      match exponent_cmp c exponent_zero with
      | Gt =>
        let (nb, e2) :=
          let (ee, b) := exponent_div2_floor (exponent_sub e c) in
          if b then (exponent_add c exponent_one, ee) else (c, ee) in
        sqrt_aux2 mode prec (mantissa_shl p nb) e2
      | _ =>
        let (e2, b) := exponent_div2_floor e in
        if b then sqrt_aux2 mode prec (mantissa_shl p exponent_one) e2
        else sqrt_aux2 mode prec p e2
      end
    end
  end.

Axiom sqrt_correct : forall mode p x, FtoX (toF (sqrt mode p x)) = FtoX (Fsqrt mode (prec p) (toF x)).

End SpecificFloat.
