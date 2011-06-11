Require Import Fcore_Raux.
Require Import ZArith.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.

Inductive signed_number (A : Type) :=
  | Mzero : signed_number A
  | Mnumber (s : bool) (m : A) : signed_number A.

Implicit Arguments Mzero [A].
Implicit Arguments Mnumber [A].

Module Type FloatCarrier.

Parameter radix : Fcore_Raux.radix.
Parameter smantissa_type : Type.
Parameter mantissa_type : Type.
Parameter exponent_type : Type.
Parameter MtoP : mantissa_type -> positive.
Parameter PtoM : positive -> mantissa_type.
Parameter MtoZ : smantissa_type -> Z.
Parameter ZtoM : Z -> smantissa_type.
Parameter EtoZ : exponent_type -> Z.
Parameter ZtoE : Z -> exponent_type.

Parameter valid_mantissa : mantissa_type -> Prop.

Parameter exponent_zero : exponent_type.
Parameter exponent_one : exponent_type.
Parameter mantissa_zero : smantissa_type.
Parameter mantissa_one : mantissa_type.
Parameter mantissa_pos : mantissa_type -> smantissa_type.
Parameter mantissa_neg : mantissa_type -> smantissa_type.

Parameter exponent_neg : exponent_type -> exponent_type.
Parameter exponent_add : exponent_type -> exponent_type -> exponent_type.
Parameter exponent_sub : exponent_type -> exponent_type -> exponent_type.
Parameter exponent_cmp : exponent_type -> exponent_type -> comparison.
Parameter exponent_div2_floor : exponent_type -> exponent_type * bool.

Parameter mantissa_sign : smantissa_type -> signed_number mantissa_type.

Parameter mantissa_add : mantissa_type -> mantissa_type -> mantissa_type.
Parameter mantissa_sub : mantissa_type -> mantissa_type -> mantissa_type.
Parameter mantissa_mul : mantissa_type -> mantissa_type -> mantissa_type.
Parameter mantissa_cmp : mantissa_type -> mantissa_type -> comparison.
Parameter mantissa_digits : mantissa_type -> exponent_type.
Parameter mantissa_even : mantissa_type -> bool.
Parameter mantissa_scale2 : mantissa_type -> exponent_type -> mantissa_type * exponent_type.
Parameter mantissa_shl : mantissa_type -> exponent_type -> mantissa_type.
Parameter mantissa_shr : mantissa_type -> exponent_type -> position -> mantissa_type * position.
Parameter mantissa_div : mantissa_type -> mantissa_type -> mantissa_type * position.
Parameter mantissa_sqrt : mantissa_type -> mantissa_type * position.

Parameter PtoM_correct : forall n, MtoP (PtoM n) = n.
Parameter ZtoM_correct : forall n, MtoZ (ZtoM n) = n.
Parameter ZtoE_correct : forall n, EtoZ (ZtoE n) = n.

Parameter exponent_zero_correct : EtoZ exponent_zero = Z0.
Parameter exponent_one_correct : EtoZ exponent_one = 1%Z.

Parameter exponent_neg_correct :
  forall x, EtoZ (exponent_neg x) = (- EtoZ x)%Z.

Parameter exponent_add_correct :
  forall x y, EtoZ (exponent_add x y) = (EtoZ x + EtoZ y)%Z.

Parameter exponent_sub_correct :
  forall x y, EtoZ (exponent_sub x y) = (EtoZ x - EtoZ y)%Z.

Parameter exponent_cmp_correct :
  forall x y, exponent_cmp x y = Zcompare (EtoZ x) (EtoZ y).

Parameter mantissa_zero_correct : MtoZ mantissa_zero = Z0.

Parameter mantissa_pos_correct :
  forall x, valid_mantissa x ->
  MtoZ (mantissa_pos x) = Zpos (MtoP x).

Parameter mantissa_neg_correct :
  forall x, valid_mantissa x ->
  MtoZ (mantissa_neg x) = Zneg (MtoP x).

Parameter mantissa_sign_correct :
  forall x,
  match mantissa_sign x with
  | Mzero => MtoZ x = Z0
  | Mnumber s p => MtoZ x = (if s then Zneg else Zpos) (MtoP p) /\ valid_mantissa p
  end.

Parameter mantissa_even_correct :
  forall x, valid_mantissa x ->
  mantissa_even x = Zeven (Zpos (MtoP x)).

Parameter mantissa_one_correct :
  MtoP mantissa_one = xH /\ valid_mantissa mantissa_one.

Parameter mantissa_add_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  MtoP (mantissa_add x y) = (MtoP x + MtoP y)%positive /\
  valid_mantissa (mantissa_add x y).

Parameter mantissa_mul_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  MtoP (mantissa_mul x y) = (MtoP x * MtoP y)%positive /\
  valid_mantissa (mantissa_mul x y).

Parameter mantissa_cmp_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  mantissa_cmp x y = Zcompare (Zpos (MtoP x)) (Zpos (MtoP y)).

Parameter mantissa_digits_correct :
  forall x, valid_mantissa x ->
  EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).

Parameter mantissa_shl_correct :
  forall x y z, valid_mantissa y -> EtoZ z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x /\
  valid_mantissa (mantissa_shl y z).

Parameter mantissa_shr_correct :
  forall x y z k, valid_mantissa y -> EtoZ z = Zpos x ->
  (Zpos (shift radix 1 x) <= Zpos (MtoP y))%Z ->
  let (sq,l) := mantissa_shr y z k in
  let (q,r) := Zdiv_eucl (Zpos (MtoP y)) (Zpos (shift radix 1 x)) in
  Zpos (MtoP sq) = q /\
  l = adjust_pos r (shift radix 1 x) k /\
  valid_mantissa sq.

Parameter mantissa_div_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  (Zpos (MtoP y) <= Zpos (MtoP x))%Z ->
  let (q,l) := mantissa_div x y in
  Zpos (MtoP q) = (Zpos (MtoP x) / Zpos (MtoP y))%Z /\
  Fcalc_bracket.inbetween_int (Zpos (MtoP q)) (Z2R (Zpos (MtoP x)) / Z2R (Zpos (MtoP y)))%R (convert_location_inv l) /\
  valid_mantissa q.

End FloatCarrier.
