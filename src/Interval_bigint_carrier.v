Require Import Fcore_Raux.
Require Import BigN.
Require Import BigZ.
Require Import Bool.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_specific_sig.

Module BigIntRadix2 <: FloatCarrier.

Definition radix := radix2.
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
  BigN.shiftl (BigZ.to_N d) m. (* safe_shiftl for 8.2 *)

Definition mantissa_scale2 (m : mantissa_type) (d : exponent_type) := (m, d).

Definition mantissa_digits m :=
  BigZ.Pos (BigN.Ndigits m - BigN.head0 m)%bigN.

Definition mantissa_even m := BigN.is_even m.

Definition mantissa_split_div m d pos :=
  let (q, r) := BigN.div_eucl m d in (q,
  if BigN.eq_bool r 0%bigN then
    match pos with pos_Eq => pos_Eq | _ => pos_Lo end
  else
    match BigN.compare (BigN.shiftl 1%bigN r) d with
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
    (BigZ.Pos (BigN.shiftr 1%bigN p), negb (BigN.is_even p))
  | BigZ.Neg p =>
    let q := BigN.shiftr 1%bigN p in
    if BigN.is_even p then (BigZ.Neg q, false)
    else (BigZ.Neg (BigN.succ q), true)
  end.

Definition mantissa_sqrt m :=
  let s := BigN.sqrt m in
  let r := BigN.sub m (BigN.square s) in (s,
  if BigN.eq_bool r 0%bigN then pos_Eq
  else match BigN.compare r s with Gt => pos_Up | _ => pos_Lo end).

Definition exponent_zero_correct := refl_equal Z0.
Definition exponent_one_correct := refl_equal 1%Z.
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

Lemma mantissa_even_correct :
  forall x, valid_mantissa x ->
  mantissa_even x = Zeven (Zpos (MtoP x)).
Proof.
intros x (px, Hx).
unfold mantissa_even, Zeven, MtoP.
generalize (BigN.spec_is_even x).
rewrite Hx.
case (BigN.is_even x) ;
  destruct px as [px|px|] ; try easy.
rewrite Zpos_xI.
now rewrite Zplus_comm, Zmult_comm, Z_mod_plus_full.
rewrite Zpos_xO.
now rewrite Zmult_comm, Z_mod_mult.
Qed.

Lemma mantissa_one_correct :
  MtoP mantissa_one = xH /\ valid_mantissa mantissa_one.
Proof.
repeat split.
now exists xH.
Qed.

Lemma mantissa_add_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  MtoP (mantissa_add x y) = (MtoP x + MtoP y)%positive /\
  valid_mantissa (mantissa_add x y).
Proof.
intros x y (px, Hx) (py, Hy).
unfold mantissa_add, valid_mantissa, MtoP.
rewrite BigN.spec_add.
rewrite Hx, Hy.
repeat split.
now exists (px + py)%positive.
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
rewrite Hx, Hy, <- Hx, <- Hy.
apply BigN.spec_compare.
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

Lemma mantissa_digits_correct :
  forall x, valid_mantissa x ->
  EtoZ (mantissa_digits x) = Zpos (count_digits radix (MtoP x)).
Proof.
intros x (px, Vx).
unfold mantissa_digits, EtoZ.
simpl.
rewrite BigN.spec_sub_pos.
rewrite BigN.spec_Ndigits.
rewrite <- digits_conversion.
rewrite <- Zplus_0_r.
rewrite <- (Zplus_opp_r [BigN.head0 x]%bigN)%Z.
rewrite Zplus_assoc.
apply (f_equal (fun v => v + _)%Z).
rewrite <- Fcalc_digits.digits_shift.
2: now apply Zgt_not_eq.
2: apply BigN.spec_pos.
refine (_ (BigN.spec_head0 x _)).
2: now rewrite Vx.
intros (H1,H2).
unfold MtoP.
rewrite Vx.
set (d := Fcalc_digits.digits radix (Zpos px * radix ^ [BigN.head0 x]%bigN)).
cut (d <= Zpos (BigN.digits x) /\ Zpos (BigN.digits x) - 1 < d)%Z. omega.
unfold d ; clear d.
split.
apply Fcalc_digits.digits_le_Zpower.
rewrite Zabs_Zmult, Zmult_comm.
rewrite Zabs_eq.
simpl Zabs.
now rewrite <- Vx.
apply Zpower_ge_0.
apply Fcalc_digits.digits_gt_Zpower.
rewrite Zabs_Zmult, Zmult_comm.
rewrite Zabs_eq.
simpl Zabs.
now rewrite <- Vx.
apply Zpower_ge_0.
admit.
Qed.

Lemma mantissa_shl_correct :
  forall x y z, valid_mantissa y ->
  EtoZ z = Zpos x ->
  MtoP (mantissa_shl y z) = shift radix (MtoP y) x /\ valid_mantissa (mantissa_shl y z).
Proof.
intros x y z (py, Vy) Hz.
unfold mantissa_shl, MtoP, valid_mantissa.
rewrite BigN.spec_shiftl, Vy.
cut (Zpos py * 2 ^ [BigZ.to_N z]%bigN = Zpos (shift radix py x))%Z.
intro H.
rewrite H.
repeat split.
refl_exists.
rewrite shift_correct.
unfold EtoZ in Hz.
now rewrite spec_to_Z, Hz.
Qed.

Lemma mantissa_sign_correct :
  forall x,
  match mantissa_sign x with
  | Mzero => MtoZ x = Z0
  | Mnumber s p => MtoZ x = (if s then Zneg else Zpos) (MtoP p) /\ valid_mantissa p
  end.
intros.
unfold mantissa_sign.
rewrite BigZ.spec_eq_bool.
case Zeq_bool_spec.
easy.
change (BigZ.to_Z 0%bigZ) with Z0.
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

Axiom mantissa_shr_correct :
  forall x y z k, valid_mantissa y -> EtoZ z = Zpos x ->
  (Zpos (shift radix 1 x) <= Zpos (MtoP y))%Z ->
  let (sq,l) := mantissa_shr y z k in
  let (q,r) := Zdiv_eucl (Zpos (MtoP y)) (Zpos (shift radix 1 x)) in
  Zpos (MtoP sq) = q /\
  l = adjust_pos r (shift radix 1 x) k /\
  valid_mantissa sq.

Axiom mantissa_div_correct :
  forall x y, valid_mantissa x -> valid_mantissa y ->
  (Zpos (MtoP y) <= Zpos (MtoP x))%Z ->
  let (q,l) := mantissa_div x y in
  Zpos (MtoP q) = (Zpos (MtoP x) / Zpos (MtoP y))%Z /\
  Fcalc_bracket.inbetween_int (Zpos (MtoP q)) (Z2R (Zpos (MtoP x)) / Z2R (Zpos (MtoP y)))%R (convert_location_inv l) /\
  valid_mantissa q.

End BigIntRadix2.
