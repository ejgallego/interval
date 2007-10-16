Require Import ZArith.
Require Import Bool.
Require Import missing.
Require Import xreal.
Require Import definitions.
Require Import generic.
Require Import generic_proof.
Require Import float_sig.
Require Import specific_sig.

Module SpecificFloat (Carrier : FloatCarrier) <: FloatOps.

Import Carrier.

Definition radix := radix.
Definition radix_correct := radix_correct.

Inductive float : Set :=
  | Fnan : float
  | Fzero : float
  | Float : bool -> mantissa_type -> exponent_type -> float.

Definition type := float.

Definition toF (x : type) :=
  match x with
  | Fnan => generic.Fnan radix
  | Fzero => generic.Fzero radix
  | Float s m e => generic.Float radix s (MtoP m) (EtoZ e)
  end.

Definition fromF (f : generic.float radix) :=
  match f with
  | generic.Float s m e => Float s (PtoM m) (ZtoE e)
  | generic.Fnan => Fnan
  | generic.Fzero => Fzero
  end.

Definition precision := exponent_type.
Definition sfactor := exponent_type.
Definition prec p := match EtoZ p with Zpos q => q | _ => xH end.
Definition ZtoS := ZtoE.

Definition zero := Fzero.
Definition nan := Fnan.

Definition zero_correct := refl_equal (generic.Fzero radix).
Definition nan_correct := refl_equal (generic.Fnan radix).

Definition real f := match f with Fnan => false | _ => true end.
Lemma real_correct :
  forall f, match toF f with generic.Fnan => real f = false | _ => real f = true end.
intros.
now case f.
Qed.

Definition fromZ n :=
  match n with
  | Zpos p => Float false (PtoM p) exponent_zero
  | Zneg p => Float true (PtoM p) exponent_zero
  | Z0 => Fzero
  end.

Lemma fromZ_correct :
  forall n, FtoX (toF (fromZ n)) = Xreal (Z2R n).
intros.
case n ; intros ; unfold fromZ, toF, FtoX ;
  try (rewrite exponent_zero_correct ; rewrite PtoM_correct ) ;
  apply refl_equal.
Qed.

(*
 * neg
 *)

Definition neg (f : type) :=
  match f with
  | Float s m e => Float (negb s) m e
  | _ => f
  end.

Lemma neg_correct :
  forall x, FtoX (toF (neg x)) = FtoX (Fneg (toF x)).
intros.
case x ; intros ; apply refl_equal.
Qed.

(*
 * abs
 *)

Definition abs (f : type) :=
  match f with
  | Float s m e => Float false m e
  | _ => f
  end.

Lemma abs_correct :
  forall x, FtoX (toF (abs x)) = FtoX (Fabs (toF x)).
intros.
case x ; intros ; apply refl_equal.
Qed.

(*
 * scale
 *)

Definition scale (f : type) d :=
  match f with
  | Float s m e => Float s m (exponent_add e d)
  | _ => f
  end.

Lemma scale_correct :
  forall x d, FtoX (toF (scale x (ZtoE d))) = FtoX (Fscale (toF x) d).
intros.
case x ; try apply refl_equal.
intros s m e.
simpl.
rewrite exponent_add_correct.
rewrite ZtoE_correct.
apply refl_equal.
Qed.

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
  cmp_aux2 m1 e1 m2 e2 = Fcmp_aux2 radix (MtoP m1) (EtoZ e1) (MtoP m2) (EtoZ e2).
intros.
unfold cmp_aux2, Fcmp_aux2.
rewrite exponent_cmp_correct.
do 2 rewrite exponent_add_correct.
do 2 rewrite mantissa_digits_correct.
unfold radix.
case (EtoZ e1 + Zpos (count_digits Carrier.radix (MtoP m1))
   ?= EtoZ e2 + Zpos (count_digits Carrier.radix (MtoP m2)))%Z ;
  try apply refl_equal.
rewrite exponent_cmp_correct.
rewrite exponent_zero_correct.
rewrite exponent_sub_correct.
case_eq (EtoZ e1 - EtoZ e2)%Z ; intros ; simpl ;
  unfold cmp_aux1, Fcmp_aux1 ; rewrite mantissa_cmp_correct.
apply refl_equal.
rewrite (mantissa_shl_correct p).
apply refl_equal.
rewrite exponent_sub_correct.
exact H.
rewrite (mantissa_shl_correct p).
apply refl_equal.
rewrite exponent_neg_correct.
rewrite exponent_sub_correct.
rewrite H.
apply refl_equal.
Qed.

Definition cmp (f1 f2 : type) :=
  match f1, f2 with
  | Fnan, _ => Xund
  | _, Fnan => Xund
  | Fzero, Fzero => Xeq
  | Fzero, Float false _ _ => Xlt
  | Fzero, Float true _ _ => Xgt
  | Float false _ _, Fzero => Xgt
  | Float true _ _, Fzero => Xlt
  | Float false _ _, Float true _ _ => Xgt
  | Float true _ _, Float false _ _ => Xlt
  | Float false m1 e1, Float false m2 e2 => cmp_aux2 m1 e1 m2 e2
  | Float true m1 e1, Float true m2 e2 => cmp_aux2 m2 e2 m1 e1
  end.

Lemma cmp_correct :
  forall x y, cmp x y = Fcmp (toF x) (toF y).
intros.
case x.
apply refl_equal.
case y ; intros ; apply refl_equal.
intros sx mx ex.
case y ; try apply refl_equal.
intros sy my ey.
simpl.
case sx ; case sy ; try apply refl_equal ; apply cmp_aux2_correct.
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
    Float sign (adjust_mantissa mode m2 pos2 sign) e2
  | Eq => Float sign (adjust_mantissa mode m1 pos sign) e1
  | Lt =>
    if need_change radix mode m1 pos sign then
      let m2 := mantissa_add (mantissa_shl m1 nb) mantissa_one in
      Float sign m2 e2
    else Float sign m1 e1
  end.

Axiom round_aux_correct :
  forall mode p sign m1 e1 pos,
  FtoX (toF (round_aux mode p sign m1 e1 pos)) =
  FtoX (Fround_at_prec mode (prec p) (generic.Ufloat radix sign (MtoP m1) (EtoZ e1) pos)).

Definition round mode prec (f : type) :=
  match f with
  | Float s m e => round_aux mode prec s m e pos_Eq
  | _ => f
  end.

(*
 * mul_exact
 *)

Definition mul_exact (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Fzero, _ => x
  | _, Fzero => y
  | Float sx mx ex, Float sy my ey =>
    Float (xorb sx sy) (mantissa_mul mx my) (exponent_add ex ey)
  end.

Lemma mul_exact_correct :
  forall x y, FtoX (toF (mul_exact x y)) = FtoX (Fmul_exact (toF x) (toF y)).
intros x y.
case x.
apply refl_equal.
case y ; intros ; apply refl_equal.
intros sx mx ex.
case y ; try apply refl_equal.
intros sy my ey.
simpl.
apply (f_equal2 (fun a b => xreal.Xreal (FtoR radix (xorb sx sy) a b))).
apply mantissa_mul_correct.
apply exponent_add_correct.
Qed.

(*
 * mul
 *)

Definition mul mode prec (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Fzero, _ => x
  | _, Fzero => y
  | Float sx mx ex, Float sy my ey =>
    round_aux mode prec (xorb sx sy) (mantissa_mul mx my) (exponent_add ex ey) pos_Eq
  end.

Lemma mul_correct :
  forall mode p x y,
  FtoX (toF (mul mode p x y)) = FtoX (Fmul mode (prec p) (toF x) (toF y)).
intros.
case x.
apply refl_equal.
case y ; intros ; apply refl_equal.
intros sx mx ex.
case y ; try apply refl_equal.
intros sy my ey.
simpl.
rewrite round_aux_correct.
rewrite mantissa_mul_correct.
rewrite exponent_add_correct.
apply refl_equal.
Qed.

(*
 * add_exact
 *)

Definition add_exact_aux1 sx sy mx my e :=
  if eqb sx sy then
    Float sx (mantissa_add mx my) e
  else
    match mantissa_cmp mx my with
    | Eq => Fzero
    | Gt => Float sx (mantissa_sub mx my) e
    | Lt => Float sy (mantissa_sub my mx) e
    end.

Definition add_exact_aux2 sx sy mx my ex ey :=
  let nb := exponent_sub ex ey in
  match exponent_cmp nb exponent_zero with
  | Gt => add_exact_aux1 sx sy (mantissa_shl mx nb) my ey
  | Lt => add_exact_aux1 sx sy mx (mantissa_shl my (exponent_neg nb)) ex
  | Eq => add_exact_aux1 sx sy mx my ex
  end.

Lemma add_exact_aux2_correct :
  forall sx mx ex sy my ey,
  FtoX (toF (add_exact_aux2 sx sy mx my ex ey)) =
  FtoX (Fround_none (Fadd_slow_aux2 radix sx sy (MtoP mx) (MtoP my) (EtoZ ex) (EtoZ ey))).
intros.
unfold add_exact_aux2, Fround_none, Fadd_slow_aux2.
rewrite exponent_cmp_correct.
rewrite exponent_zero_correct.
Admitted.

Definition add_exact (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Fzero, Fzero => x
  | Fzero, Float sy my ey => y
  | Float sx mx ex, Fzero => x
  | Float sx mx ex, Float sy my ey =>
    add_exact_aux2 sx sy mx my ex ey
  end.

Lemma add_exact_correct :
  forall x y, FtoX (toF (add_exact x y)) = FtoX (Fadd_exact (toF x) (toF y)).
intros x y.
case x.
apply refl_equal.
case y ; intros ; apply refl_equal.
intros sx mx ex.
case y ; try apply refl_equal.
intros sy my ey.
unfold Fadd_exact, Fadd_slow_aux.
simpl.
apply add_exact_aux2_correct.
Qed.

(*
 * add
 *)

Definition add_slow_aux1 mode prec sx sy mx my e :=
  if eqb sx sy then
    round_aux mode prec sx (mantissa_add mx my) e pos_Eq
  else
    match mantissa_cmp mx my with
    | Eq => Fzero
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
  | Fzero, Fzero => x
  | Fzero, Float sy my ey => round_aux mode prec sy my ey pos_Eq
  | Float sx mx ex, Fzero => round_aux mode prec sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    add_slow_aux2 mode prec sx sy mx my ex ey
  end.

Definition add := add_slow.

Axiom add_correct : forall mode p x y, FtoX (toF (add mode p x y)) = FtoX (Fadd mode (prec p) (toF x) (toF y)).

(*
 * sub_exact
 *)

Definition sub_exact (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Fzero, Fzero => x
  | Fzero, Float sy my ey => Float (negb sy) my ey
  | Float sx mx ex, Fzero => x
  | Float sx mx ex, Float sy my ey =>
    add_exact_aux2 sx (negb sy) mx my ex ey
  end.

Lemma sub_exact_correct :
  forall x y, FtoX (toF (sub_exact x y)) = FtoX (Fsub_exact (toF x) (toF y)).
intros x y.
case x.
apply refl_equal.
case y ; intros ; apply refl_equal.
intros sx mx ex.
case y ; try apply refl_equal.
intros sy my ey.
unfold Fsub_exact, Fsub_slow_aux.
simpl.
apply add_exact_aux2_correct.
Qed.

(*
 * sub
 *)

Definition sub mode prec (x y : type) :=
  match x, y with
  | Fnan, _ => x
  | _, Fnan => y
  | Fzero, Fzero => x
  | Fzero, Float sy my ey => round_aux mode prec (negb sy) my ey pos_Eq
  | Float sx mx ex, Fzero => round_aux mode prec sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    add_slow_aux2 mode prec sx (negb sy) mx my ex ey
  end.

Lemma sub_correct :
  forall mode p x y,
  FtoX (toF (sub mode p x y)) = FtoX (Fsub mode (prec p) (toF x) (toF y)).
intros.
rewrite Fsub_split.
replace (sub mode p x y) with (add mode p x (neg y)).
rewrite add_correct.
rewrite Fadd_correct.
rewrite neg_correct.
rewrite Fadd_correct.
apply refl_equal.
case x ; case y ; intros ; apply refl_equal.
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
  | _, Fzero => Fnan
  | Fzero, _ => x
  | Float sx mx ex, Float sy my ey =>
    let dx := mantissa_digits mx in
    let dy := mantissa_digits my in
    let e := exponent_sub ex ey in
    let nb := exponent_sub (exponent_add dy prec) dx in
    match exponent_cmp nb exponent_zero with
    | Gt =>
      div_aux mode prec (xorb sx sy) (mantissa_shl mx nb) my (exponent_sub e nb)
    | _ => div_aux mode prec (xorb sx sy) mx my e
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
  | Float false m e =>
    let d := mantissa_digits m in
    let p := exponent_sub (exponent_add prec prec) (exponent_add d exponent_one) in
    match exponent_cmp p exponent_zero with
    | Gt =>
      let (nb, e2) :=
        let (ee, b) := exponent_div2_floor (exponent_sub e p) in
        if b then (exponent_add p exponent_one, ee) else (p, ee) in
      sqrt_aux2 mode prec (mantissa_shl m nb) e2
    | _ =>
      let (e2, b) := exponent_div2_floor e in
      if b then sqrt_aux2 mode prec (mantissa_shl m exponent_one) e2
      else sqrt_aux2 mode prec m e2
    end
  | Float true _ _ => Fnan
  | _ => f
  end.

Axiom sqrt_correct : forall mode p x, FtoX (toF (sqrt mode p x)) = FtoX (Fsqrt mode (prec p) (toF x)).

End SpecificFloat.
