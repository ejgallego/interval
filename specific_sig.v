Require Import ZArith.
Require Import definitions.
Require Import generic.
Require Import generic_proof.

Module Type FloatCarrier.

Parameter radix : positive.
Parameter radix_correct : (1 < Zpos radix)%Z.
Parameter mantissa_type : Set.
Parameter exponent_type : Set.
Parameter PtoM : positive -> mantissa_type.
Parameter MtoP : mantissa_type -> positive.
Parameter EtoZ : exponent_type -> Z.
Parameter ZtoE : Z -> exponent_type.

Parameter exponent_zero : exponent_type.
Parameter exponent_one : exponent_type.
Parameter mantissa_one : mantissa_type.

Parameter exponent_neg : exponent_type -> exponent_type.
Parameter exponent_add : exponent_type -> exponent_type -> exponent_type.
Parameter exponent_sub : exponent_type -> exponent_type -> exponent_type.
Parameter exponent_cmp : exponent_type -> exponent_type -> comparison.
Parameter exponent_div2_floor : exponent_type -> exponent_type * bool.

Parameter mantissa_add : mantissa_type -> mantissa_type -> mantissa_type.
Parameter mantissa_sub : mantissa_type -> mantissa_type -> mantissa_type.
Parameter mantissa_mul : mantissa_type -> mantissa_type -> mantissa_type.
Parameter mantissa_cmp : mantissa_type -> mantissa_type -> comparison.
Parameter mantissa_digits : mantissa_type -> exponent_type.
Parameter mantissa_even : mantissa_type -> bool.
Parameter mantissa_shl : mantissa_type -> exponent_type -> mantissa_type.
Parameter mantissa_shr : mantissa_type -> exponent_type -> position -> mantissa_type * position.
Parameter mantissa_div : mantissa_type -> mantissa_type -> mantissa_type * position.
Parameter mantissa_sqrt : mantissa_type -> mantissa_type * position.

Parameter PtoM_correct :
  forall n, MtoP (PtoM n) = n.

Parameter ZtoE_correct :
  forall n, EtoZ (ZtoE n) = n.

Parameter exponent_zero_correct : EtoZ exponent_zero = Z0.

Parameter exponent_neg_correct :
  forall x, EtoZ (exponent_neg x) = (- EtoZ x)%Z.

Parameter exponent_add_correct :
  forall x y, EtoZ (exponent_add x y) = (EtoZ x + EtoZ y)%Z.

Parameter exponent_sub_correct :
  forall x y, EtoZ (exponent_sub x y) = (EtoZ x - EtoZ y)%Z.

Parameter exponent_cmp_correct :
  forall x y, exponent_cmp x y = Zcompare (EtoZ x) (EtoZ y).

Parameter mantissa_mul_correct :
  forall x y, MtoP (mantissa_mul x y) = (MtoP x * MtoP y)%positive.

Parameter mantissa_cmp_correct :
  forall x y, mantissa_cmp x y = Zcompare (Zpos (MtoP x)) (Zpos (MtoP y)).

Parameter mantissa_digits_correct :
  forall x, EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).

Parameter mantissa_shl_correct :
  forall x y z, EtoZ z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x.

End FloatCarrier.
