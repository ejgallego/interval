Require Import BigN.
Require Import BigZ.
Require Import Bool.
Require Import definitions.
Require Import generic.
Require Import specific_sig.

Module BigIntRadix2 <: FloatCarrier.

Definition radix := 2%positive.
Definition radix_correct := refl_equal Lt.
Definition smantissa_type := BigZ.t.
Definition mantissa_type := BigN.t.
Definition exponent_type := BigZ.t.

Definition MtoZ := BigZ.to_Z.
Definition ZtoM := BigZ.of_Z.
Definition MtoP v := match BigN.to_Z v with Zpos w => w | _ => xH end.
Definition PtoM := BigN.of_pos.
Definition EtoZ := BigZ.to_Z.
Definition ZtoE := BigZ.of_Z.

Definition valid_mantissa v := exists p, BigN.to_Z v = Zpos p.

Definition exponent_zero := 0%bigZ.
Definition exponent_one := 1%bigZ.
Definition exponent_neg := BigZ.opp.
Definition exponent_add := BigZ.add.
Definition exponent_sub := BigZ.sub.
Definition exponent_cmp := BigZ.compare.
Definition mantissa_zero := 0%bigZ.
Definition mantissa_one := 1%bigN.
Definition mantissa_add := BigN.add.
Definition mantissa_sub := BigN.sub.
Definition mantissa_mul := BigN.mul.
Definition mantissa_cmp := BigN.compare.
Definition mantissa_pos := BigZ.Pos.
Definition mantissa_neg := BigZ.Neg.

Definition mantissa_sign m :=
  if BigZ.eq_bool m 0%bigZ then Mzero
  else
    match m with
    | BigZ.Pos p => Mnumber false p
    | BigZ.Neg p => Mnumber true p
    end.

Definition mantissa_shl m d :=
  BigN.safe_shiftl (BigZ.to_N d) m.

Definition mantissa_scale2 (m : mantissa_type) (d : exponent_type) := (m, d).

Definition mantissa_digits m :=
  BigZ.Pos (BigN.Ndigits m - BigN.head0 m)%bigN.

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

Definition mantissa_div :=
  fun m d => mantissa_split_div m d pos_Eq.

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
  let r := BigN.sub m (BigN.square s) in (s,
  if BigN.eq_bool r 0%bigN then pos_Eq
  else match BigN.compare r s with Gt => pos_Up | _ => pos_Lo end).

Definition exponent_zero_correct := refl_equal Z0.
Definition mantissa_zero_correct := refl_equal Z0.

Definition ZtoM_correct := BigZ.spec_of_Z.
Definition ZtoE_correct := BigZ.spec_of_Z.
Definition exponent_neg_correct := BigZ.spec_opp.
Definition exponent_abs_correct := BigZ.spec_abs.
Definition exponent_add_correct := BigZ.spec_add.
Definition exponent_sub_correct := BigZ.spec_sub.

Lemma PtoM_correct :
  forall n, MtoP (PtoM n) = n.
intros.
unfold MtoP, PtoM.
rewrite BigN.spec_of_pos.
apply refl_equal.
Qed.

Lemma mantissa_pos_correct :
  forall x, valid_mantissa x ->
  MtoZ (mantissa_pos x) = Zpos (MtoP x).
intros x (p, H).
unfold MtoZ, MtoP.
simpl.
rewrite H.
apply refl_equal.
Qed.

Lemma mantissa_neg_correct :
  forall x, valid_mantissa x ->
  MtoZ (mantissa_neg x) = Zneg (MtoP x).
intros x (p, H).
unfold MtoZ, MtoP.
simpl.
rewrite H.
apply refl_equal.
Qed.

Lemma mantissa_mul_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  MtoP (mantissa_mul x y) = (MtoP x * MtoP y)%positive /\
  valid_mantissa (mantissa_mul x y).
intros x y (px, Hx) (py, Hy).
unfold mantissa_mul, valid_mantissa, MtoP.
rewrite BigN.spec_mul.
rewrite Hx, Hy.
simpl.
split.
apply refl_equal.
exists (px * py)%positive.
apply refl_equal.
Qed.

Lemma mantissa_cmp_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  mantissa_cmp x y = Zcompare (Zpos (MtoP x)) (Zpos (MtoP y)).
intros x y (px, Hx) (py, Hy).
unfold mantissa_cmp, MtoP.
generalize (BigN.spec_compare x y).
case (x ?= y)%bigN ; intros ; apply sym_eq.
apply <- Zcompare_Eq_iff_eq.
rewrite Hx, Hy, <- Hx, <- Hy.
exact H.
rewrite <- H.
rewrite Hx, Hy.
apply refl_equal.
rewrite <- H.
rewrite Hx, Hy.
apply refl_equal.
Qed.

Lemma exponent_cmp_correct :
  forall x y, exponent_cmp x y = Zcompare (MtoZ x) (MtoZ y).
intros.
unfold exponent_cmp, MtoZ.
apply sym_eq.
generalize (BigZ.spec_compare x y).
unfold Zlt, Zgt.
case (x ?= y)%bigZ ; intro H ; rewrite H ;
 first [ apply Zcompare_refl | apply refl_equal ].
Qed.

Axiom mantissa_digits_correct :
  forall x, valid_mantissa x ->
  EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).

Axiom mantissa_shl_correct :
  forall x y z, valid_mantissa y ->
  EtoZ z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x /\ valid_mantissa (mantissa_shl y z).

Lemma mantissa_sign_correct :
  forall x,
  match mantissa_sign x with
  | Mzero => MtoZ x = Z0
  | Mnumber s p => MtoZ x = (if s then Zneg else Zpos) (MtoP p) /\ valid_mantissa p
  end.
intros.
unfold mantissa_sign.
generalize (BigZ.spec_eq_bool x 0%bigZ).
case (BigZ.eq_bool x 0%bigZ).
trivial.
change 0%bigZ with BigZ.zero.
rewrite BigZ.spec_0.
case x ; unfold valid_mantissa ; simpl ; intros.
(* + *)
assert (BigN.to_Z t = Zpos (MtoP t)).
generalize H. clear.
unfold MtoP.
generalize (BigN.spec_pos t).
case (BigN.to_Z t) ; intros.
elim H0.
apply refl_equal.
apply refl_equal.
elim H.
apply refl_equal.
split.
exact H0.
exists (MtoP t).
exact H0.
(* - *)
assert (- BigN.to_Z t = Zneg (MtoP t))%Z.
generalize H. clear.
unfold MtoP.
generalize (BigN.spec_pos t).
case (BigN.to_Z t) ; intros.
elim H0.
apply refl_equal.
apply refl_equal.
elim H.
apply refl_equal.
split.
exact H0.
exists (MtoP t).
exact (BinInt.Zopp_inj _ (Zpos _) H0).
Qed.

End BigIntRadix2.
