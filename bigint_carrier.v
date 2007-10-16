Require Import BigN.
Require Import BigZ.
Require Import Bool.
Require Import definitions.
Require Import generic.
Require Import specific_sig.

Module BigIntRadix2 <: FloatCarrier.

Definition radix := 2%positive.
Definition radix_correct := refl_equal Lt.
Definition mantissa_type := BigN.t.
Definition exponent_type := BigZ.t.

Definition MtoP m :=
  match BigN.to_Z m with
  | Zpos p => p
  | _ => xH
  end.

Definition PtoM := BigN.of_pos.
Definition EtoZ := BigZ.to_Z.
Definition ZtoE := BigZ.of_Z.

Definition exponent_zero := 0%bigZ.
Definition exponent_one := 1%bigZ.
Definition exponent_neg := BigZ.opp.
Definition exponent_add := BigZ.add.
Definition exponent_sub := BigZ.sub.
Definition exponent_cmp := BigZ.compare.
Definition mantissa_one := 1%bigN.
Definition mantissa_add := BigN.add.
Definition mantissa_sub := BigN.sub.
Definition mantissa_mul := BigN.mul.
Definition mantissa_cmp := BigN.compare.

Definition mantissa_shl m d :=
  match d with
  | BigZ.Pos k => BigN.safe_shiftl k m
  | BigZ.Neg _ => m
  end.

Definition mantissa_digits m :=
  (BigZ.Pos (BigN.Ndigits m) - BigZ.Pos (BigN.head0 m))%bigZ.

Definition mantissa_even m := BigN.is_even m.

Definition mantissa_split_div m d pos :=
  let (q, r) := BigN.div_eucl m d in (q,
  if BigN.eq_bool r 0%bigN then
    match pos with pos_Eq => pos_Eq | _ => pos_Lo end
  else
    match BigN.compare (BigN.safe_shiftl 1%bigN r) d with
    | Lt => pos_Lo
    | Eq => match pos with pos_Eq => pos_Mi | _ => pos_Up end
    | Gt => pos_Up
    end).

Definition mantissa_div := fun m d => mantissa_split_div m d pos_Eq.

(*
Definition mantissa_shr m d pos :=
  mantissa_split_div m (mantissa_shl 1%bigN d) pos.
*)

Definition mantissa_shr m d pos :=
  let dd := BigZ.to_N d in
  (BigN.shiftr dd m,
  let d1 := BigN.pred dd in
  match BigN.compare (BigN.tail0 m) d1 with
  | Gt => match pos with pos_Eq => pos_Eq | _ => pos_Lo end
  | Eq => match pos with pos_Eq => pos_Mi | _ => pos_Up end
  | Lt =>
    if BigN.is_even (BigN.shiftr d1 m) then pos_Lo
    else pos_Up
  end).

(*
Definition mantissa_shr m d pos :=
  let dd := BigZ.to_N d in
  let d1 := BigN.pred dd in
  (BigN.shiftr dd m,
  let p1 := BigN.is_even (BigN.shiftr d1 m) in
  let p2 := BigN.is_even (BigN.shiftr d1 (BigN.pred m)) in
  if p1 then
    if p2 then (* 00 *)
      pos_Lo
    else       (* 01 *)
      match pos with pos_Eq => pos_Eq | _ => pos_Lo end
  else
    if p2 then (* 10 *)
      match pos with pos_Eq => pos_Mi | _ => pos_Up end
    else       (* 11 *)
      pos_Up).
*)

Definition exponent_div2_floor e :=
  match e with
  | BigZ.Pos p =>
    (BigZ.Pos (BigN.safe_shiftr 1%bigN p), negb (BigN.is_even p))
  | BigZ.Neg p =>
    let q := BigN.safe_shiftr 1%bigN p in
    if BigN.is_even p then (BigZ.Neg q, false)
    else (BigZ.Neg (BigN.succ q), true)
  end.

Definition mantissa_sqrt m :=
  let s := BigN.sqrt m in
  let r := BigN.sub m (BigN.square s) in
  (s, if BigN.eq_bool r 0%bigN then pos_Eq
      else match BigN.compare r s with Gt => pos_Up | _ => pos_Lo end).

Definition exponent_zero_correct := refl_equal Z0.

Axiom PtoM_correct :
  forall n, MtoP (PtoM n) = n.

Axiom ZtoE_correct :
  forall n, EtoZ (ZtoE n) = n.

Axiom exponent_neg_correct :
  forall x, EtoZ (exponent_neg x) = (- EtoZ x)%Z.

Axiom exponent_add_correct :
  forall x y, EtoZ (exponent_add x y) = (EtoZ x + EtoZ y)%Z.

Axiom exponent_sub_correct :
  forall x y, EtoZ (exponent_sub x y) = (EtoZ x - EtoZ y)%Z.

Axiom exponent_cmp_correct :
  forall x y, exponent_cmp x y = Zcompare (EtoZ x) (EtoZ y).

Axiom mantissa_mul_correct :
  forall x y, MtoP (mantissa_mul x y) = (MtoP x * MtoP y)%positive.

Axiom mantissa_cmp_correct :
  forall x y, mantissa_cmp x y = Zcompare (Zpos (MtoP x)) (Zpos (MtoP y)).

Axiom mantissa_digits_correct :
  forall x, EtoZ (mantissa_digits x) = Zpos (definitions.count_digits radix (MtoP x)).

Axiom mantissa_shl_correct :
  forall x y z, EtoZ z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x.

End BigIntRadix2.
