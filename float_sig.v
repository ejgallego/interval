Require Import ZArith.
Require Import missing.
Require Import xreal.
Require Import definitions.
Require Import generic.
Require Import generic_proof.

Module Type FloatOps.

Parameter radix : positive.
Parameter even_radix : bool.
Parameter radix_correct : (1 < Zpos radix)%Z.
Parameter even_radix_correct : match radix with xO _ => true | _ => false end = even_radix.
Parameter type : Set.
Parameter toF : type -> float radix.

Parameter precision : Set.
Parameter sfactor : Set.
Parameter prec : precision -> positive.
Parameter ZtoS : Z -> sfactor.
Parameter PtoP : positive -> precision.

Parameter zero : type.
Parameter nan : type.
Parameter fromZ : Z -> type.
Parameter fromF : float radix -> type.
Parameter real : type -> bool.

Parameter cmp : type -> type -> Xcomparison.
Parameter min : type -> type -> type.
Parameter max : type -> type -> type.
Parameter round : rounding_mode -> precision -> type -> type.
Parameter neg : type -> type.
Parameter abs : type -> type.
Parameter scale : type -> sfactor -> type.
Parameter scale2 : type -> sfactor -> type.
Parameter add_exact : type -> type -> type.
Parameter sub_exact : type -> type -> type.
Parameter mul_exact : type -> type -> type.
Parameter add : rounding_mode -> precision -> type -> type -> type.
Parameter sub : rounding_mode -> precision -> type -> type -> type.
Parameter mul : rounding_mode -> precision -> type -> type -> type.
Parameter div : rounding_mode -> precision -> type -> type -> type.
Parameter sqrt : rounding_mode -> precision -> type -> type.

Parameter zero_correct : toF zero = Fzero radix.
Parameter nan_correct : toF nan = Fnan radix.
Parameter fromZ_correct :
  forall n, FtoX (toF (fromZ n)) = Xreal (Z2R n).

Parameter real_correct :
  forall f,
  match toF f with Fnan => real f = false | _ => real f = true end.

Parameter cmp_correct :
  forall x y, cmp x y = Fcmp (toF x) (toF y).

Parameter min_correct :
  forall x y, FtoX (toF (min x y)) = FtoX (Fmin (toF x) (toF y)).

Parameter max_correct :
  forall x y, FtoX (toF (max x y)) = FtoX (Fmax (toF x) (toF y)).

Parameter neg_correct :
  forall x, FtoX (toF (neg x)) = FtoX (Fneg (toF x)).

Parameter abs_correct :
  forall x, FtoX (toF (abs x)) = FtoX (Fabs (toF x)).

Parameter scale_correct :
  forall x d, FtoX (toF (scale x (ZtoS d))) = FtoX (Fscale (toF x) d).

Parameter scale2_correct :
  forall x d, even_radix = true ->
  FtoX (toF (scale2 x (ZtoS d))) = FtoX (Fscale2 (toF x) d).

Parameter add_exact_correct :
  forall x y, FtoX (toF (add_exact x y)) = FtoX (Fadd_exact (toF x) (toF y)).

Parameter sub_exact_correct :
  forall x y, FtoX (toF (sub_exact x y)) = FtoX (Fsub_exact (toF x) (toF y)).

Parameter mul_exact_correct :
  forall x y, FtoX (toF (mul_exact x y)) = FtoX (Fmul_exact (toF x) (toF y)).

Parameter add_correct :
  forall mode p x y,
  FtoX (toF (add mode p x y)) = FtoX (Fadd mode (prec p) (toF x) (toF y)).

Parameter sub_correct :
  forall mode p x y,
  FtoX (toF (sub mode p x y)) = FtoX (Fsub mode (prec p) (toF x) (toF y)).

Parameter mul_correct :
  forall mode p x y,
  FtoX (toF (mul mode p x y)) = FtoX (Fmul mode (prec p) (toF x) (toF y)).

Parameter div_correct :
  forall mode p x y,
  FtoX (toF (div mode p x y)) = FtoX (Fdiv mode (prec p) (toF x) (toF y)).

Parameter sqrt_correct :
  forall mode p x,
  FtoX (toF (sqrt mode p x)) = FtoX (Fsqrt mode (prec p) (toF x)).

End FloatOps.
