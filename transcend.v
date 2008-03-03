Require Import Reals.
Require Import xreal.
Require Import definitions.
Require Import float_sig.
Require Import generic.
Require Import generic_proof.
Require Import interval_float.

Module TranscendentalFloatFast (F : FloatOps with Definition even_radix := true).

Module I := FloatInterval F.

CoInductive constant : Set :=
  | Consts: I.type -> constant -> constant.

Fixpoint constant_getter_aux n cst :=
  match cst, n with
  | Consts xi _, O => xi
  | Consts _ c, S p => constant_getter_aux p c
  end.

Definition constant_getter cst prec :=
  let nb := Zabs_nat (Zpred (fst (Zdiv.Zdiv_eucl_POS (F.prec prec + 30)%positive 31%Z))) in
  constant_getter_aux nb cst.

CoFixpoint constant_generator_aux gen n :=
  Consts (gen (F.PtoP (n * 31)%positive)) (constant_generator_aux gen (Psucc n)).

Definition constant_generator gen :=
  constant_generator_aux gen 1.

(* 0 <= inputs *)
Fixpoint atan_fast0_aux prec thre powl powu sqrl sqru two div (nb : nat) { struct nb } :=
  let npwu := F.mul rnd_UP prec powu sqru in
  let valu := F.div rnd_UP prec npwu div in
  match F.cmp valu thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero valu
  | _, S n =>
    let npwl := F.mul rnd_DN prec powl sqrl in
    let vall := F.div rnd_DN prec npwl div in
    I.sub prec (I.bnd vall valu)
      (atan_fast0_aux prec thre npwl npwu sqrl sqru two (F.add_exact div two) n)
  end.

(*
Definition atan_fast0_aux prec thre powl powu sqrl sqru two div nb :=
  let fix aux powl powu div (nb : nat) { struct nb } :=
    let npwu := F.mul rnd_UP prec powu sqru in
    let valu := F.div rnd_UP prec npwu div in
    match F.cmp valu thre, nb with
    | Xlt, _ => I.bnd (F.neg valu) valu
    | _, O => I.bnd (F.neg valu) valu
    | _, S n =>
      let npwl := F.mul rnd_DN prec powl sqrl in
      let vall := F.div rnd_DN prec npwl div in
      I.sub prec (I.bnd vall valu)
        (aux npwl npwu (F.add_exact div two) n)
    end in
  aux powl powu div nb.
*)

(* -1/2 <= input <= 1/2 *)
Definition atan_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := atan_fast0_aux prec thre c1 c1 x2l x2u (F.fromZ 2) (F.fromZ 3) (nat_of_P p) in
  I.mul_mixed prec (I.sub prec (I.bnd c1 c1) rem) x.

(* -1/2 <= input <= 1/2 *)
Definition atan_fast0i prec xi :=
  let x2 := I.sqr prec xi in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := atan_fast0_aux prec thre c1 c1 (I.lower x2) (I.upper x2) (F.fromZ 2) (F.fromZ 3) (nat_of_P p) in
  I.mul prec (I.sub prec (I.bnd c1 c1) rem) xi.

Definition pi4_gen prec :=
  let s2 := F.ZtoS 2 in
  I.sub prec
   (I.scale2 (atan_fast0i prec (I.inv prec (I.fromZ 5))) s2)
   (atan_fast0i prec (I.inv prec (I.fromZ 239))).

Definition pi4_seq := constant_generator pi4_gen.
Definition pi4 := constant_getter pi4_seq.

Definition atan_fastP prec x :=
  let c1 := F.fromZ 1 in
  match F.cmp x (F.scale2 c1 (F.ZtoS (-1)%Z)) with
  | Xgt =>
    let pi4i := pi4 prec in
    let s1 := F.ZtoS 1%Z in
    match F.cmp x (F.scale2 c1 s1) with
    | Xgt =>
      I.sub prec
       (I.scale2 pi4i s1)
       (atan_fast0i prec (I.bnd (F.div rnd_DN prec c1 x) (F.div rnd_UP prec c1 x)))
    | _ =>
      let xm1 := F.sub_exact x c1 in
      let xp1 := F.add_exact x c1 in
      I.add prec pi4i
       (atan_fast0i prec (I.bnd (F.div rnd_DN prec xm1 xp1) (F.div rnd_UP prec xm1 xp1)))
    end
  | _ => atan_fast0 prec x
  end.

Definition atan_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (atan_fastP prec (F.neg x))
  | Xgt => atan_fastP prec x
  | Xund => I.nai
  end.

(* 0 <= inputs *)
Fixpoint cos_fast0_aux prec thre powl powu sqrl sqru fact div (nb : nat) { struct nb } :=
  let npwu := F.mul rnd_UP prec powu sqru in
  let valu := F.div rnd_UP prec npwu div in
  match F.cmp valu thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero valu
  | _, S n =>
    let npwl := F.mul rnd_DN prec powl sqrl in
    let vall := F.div rnd_DN prec npwl div in
    let one := F.fromZ 1 in
    let nfact := F.add_exact fact (F.add_exact one one) in
    let ndiv := F.mul_exact div (F.mul_exact fact (F.add_exact fact one)) in
    I.sub prec (I.bnd vall valu)
      (cos_fast0_aux prec thre npwl npwu sqrl sqru nfact ndiv n)
  end.

(* -1/2 <= input <= 1/2 *)
Definition cos_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := cos_fast0_aux prec thre c1 c1 x2l x2u (F.fromZ 3) (F.fromZ 2) (nat_of_P p) in
  I.sub prec (I.bnd c1 c1) rem.

(* 0 <= input *)
Definition sin_cos_reduce prec x :=
  let c1 := F.fromZ 1 in
  let sp1 := F.ZtoS 1%Z in
  let sm1 := F.ZtoS (-1)%Z in
  let i1 := I.bnd c1 c1 in
  let th := F.scale2 c1 sm1 in
  let fix reduce x (nb : nat) {struct nb} :=
    match F.cmp x th, nb with
    | Xlt, _ => (Xgt, cos_fast0 prec x)
    | _, O => (Xeq, I.bnd (F.neg c1) c1)
    | _, S n =>
      match reduce (F.scale2 x sm1) n with
      | (s, c) =>
       (match s, I.sign_large c with
        | Xlt, Xgt => Xlt
        | Xlt, Xlt => Xgt
        | Xgt, Xlt => Xlt
        | Xgt, Xgt => Xgt
        | _, _ => s
        end,
        I.sub prec (I.scale2 (I.sqr prec c) sp1) i1)
      end
    end in
  reduce x.

(*
Definition cos_fastP prec x :=
  let c1 := F.fromZ 1 in
  let c2 := F.fromZ 2 in
  let sm1 := F.ZtoS (-1)%Z in
  let i1 := I.bnd c1 c1 in
  let ir := I.bnd (F.neg c1) c1 in
  let th := F.scale2 c1 sm1 in
  let fix reduce x (nb : nat) {struct nb} :=
    match F.cmp x th, nb with
    | Xlt, _ => cos_fast0 prec x
    | _, O => ir
    | _, S n =>
      let c := reduce (F.scale2 x sm1) n in
      I.meet ir (I.sub prec (I.mul_mixed prec (I.sqr prec c) c2) i1)
    end in
  reduce x 20.
*)

(* 0 <= input *)
Definition cos_fastP prec x :=
  snd (sin_cos_reduce prec x 20).

Definition cos_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.fromZ 1
  | Xlt => cos_fastP prec (F.neg x)
  | Xgt => cos_fastP prec x
  | Xund => I.nai
  end.

(* 0 <= inputs *)
Fixpoint sin_fast0_aux prec thre powl powu sqrl sqru fact div (nb : nat) { struct nb } :=
  let npwu := F.mul rnd_UP prec powu sqru in
  let valu := F.div rnd_UP prec npwu div in
  match F.cmp valu thre, nb with
  | Xlt, _
  | _, O => I.bnd F.zero valu
  | _, S n =>
    let npwl := F.mul rnd_DN prec powl sqrl in
    let vall := F.div rnd_DN prec npwl div in
    let one := F.fromZ 1 in
    let nfact := F.add_exact fact (F.add_exact one one) in
    let ndiv := F.mul_exact div (F.mul_exact fact (F.add_exact fact one)) in
    I.sub prec (I.bnd vall valu)
      (cos_fast0_aux prec thre npwl npwu sqrl sqru nfact ndiv n)
  end.

(* -1/2 <= input <= 1/2 *)
Definition sin_fast0 prec x :=
  let x2l := F.mul rnd_DN prec x x in
  let x2u := F.mul rnd_UP prec x x in
  let c1 := F.fromZ 1 in
  let p := F.prec prec in
  let thre := F.scale c1 (F.ZtoS (Zneg p)) in
  let rem := sin_fast0_aux prec thre c1 c1 x2l x2u (F.fromZ 4) (F.fromZ 6) (nat_of_P p) in
  I.mul_mixed prec (I.sub prec (I.bnd c1 c1) rem) x.

(*
(* 0 <= input *)
Definition sin_fastP prec x :=
  let c1 := F.fromZ 1 in
  let c2 := F.fromZ 2 in
  let sm1 := F.ZtoS (-1)%Z in
  let i1 := I.bnd c1 c1 in
  let ir := I.bnd (F.neg c1) c1 in
  let th := F.scale2 c1 sm1 in
  match F.cmp x th with
  | Xlt => sin_fast0 prec x
  | _ => (* parallel evaluation of sign(sin) / cos *)
    let fix reduce x (nb : nat) {struct nb} :=
      match F.cmp x th, nb with
      | Xlt, _ => (Xgt, cos_fast0 prec x)
      | _, O => (Xeq, ir)
      | _, S n =>
        match reduce (F.scale2 x sm1) n with
        | (s, c) =>
          let s2 :=
            match s, I.sign_large c with
            | Xlt, Xgt => Xlt
            | Xlt, Xlt => Xgt
            | Xgt, Xlt => Xlt
            | Xgt, Xgt => Xgt
            | _, _ => s
            end in
         (s2,
          I.meet ir (I.sub prec (I.mul_mixed prec (I.sqr prec c) c2) i1))
        end
      end in
    match reduce x 20 with
    | (s, c) =>
      let v := I.sqrt prec (I.sub prec i1 (I.sqr prec c)) in
      match s with
      | Xlt => I.neg v
      | Xgt => v
      | _ => ir
      end
    end
  end.
*)

(* 0 <= input *)
Definition sin_fastP prec x :=
  let c1 := F.fromZ 1 in
  let sm1 := F.ZtoS (-1)%Z in
  let th := F.scale2 c1 sm1 in
  match F.cmp x th with
  | Xlt => sin_fast0 prec x
  | _ =>
    match sin_cos_reduce prec x 20 with
    | (s, c) =>
      let v := I.sqrt prec (I.sub prec (I.bnd c1 c1) (I.sqr prec c)) in
      match s with
      | Xlt => I.neg v
      | Xgt => v
      | _ => I.bnd (F.neg c1) c1
      end
    end
  end.

Definition sin_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (sin_fastP prec (F.neg x))
  | Xgt => sin_fastP prec x
  | Xund => I.nai
  end.

(*
(* 0 <= input *)
Definition tan_fastP prec x :=
  let c1 := F.fromZ 1 in
  let c2 := F.fromZ 2 in
  let sm1 := F.ZtoS (-1)%Z in
  let i1 := I.bnd c1 c1 in
  let ir := I.bnd (F.neg c1) c1 in
  let th := F.scale2 c1 sm1 in
  match F.cmp x th with
  | Xlt =>
    let s := sin_fast0 prec x in
    I.div prec s (I.sqrt prec (I.sub prec i1 (I.sqr prec s)))
  | _ => (* parallel evaluation of sign(sin) / cos *)
    let fix reduce x (nb : nat) {struct nb} :=
      match F.cmp x th, nb with
      | Xlt, _ => (Xgt, cos_fast0 prec x)
      | _, O => (Xeq, ir)
      | _, S n =>
        match reduce (F.scale2 x sm1) n with
        | (s, c) =>
          let s2 :=
            match s, I.sign_large c with
            | Xlt, Xgt => Xlt
            | Xlt, Xlt => Xgt
            | Xgt, Xlt => Xlt
            | Xgt, Xgt => Xgt
            | _, _ => s
            end in
         (s2,
          I.meet ir (I.sub prec (I.mul_mixed prec (I.sqr prec c) c2) i1))
        end
      end in
    match reduce x 20 with
    | (s, c) =>
      let v := I.sqrt prec (I.sub prec (I.div prec i1 (I.sqr prec c)) i1) in
      match s, I.sign_large c with
      | Xlt, Xgt => I.neg v
      | Xgt, Xlt => I.neg v
      | Xlt, Xlt => v
      | Xgt, Xgt => v
      | _, _ => I.nai
      end
    end
  end.
*)

(* 0 <= input *)
Definition tan_fastP prec x :=
  let c1 := F.fromZ 1 in
  let i1 := I.bnd c1 c1 in
  let sm1 := F.ZtoS (-1)%Z in
  let th := F.scale2 c1 sm1 in
  match F.cmp x th with
  | Xlt =>
    let s := sin_fast0 prec x in
    I.div prec s (I.sqrt prec (I.sub prec i1 (I.sqr prec s)))
  | _ =>
    match sin_cos_reduce prec x 20 with
    | (s, c) =>
      let v := I.sqrt prec (I.sub prec (I.div prec i1 (I.sqr prec c)) i1) in
      match s, I.sign_large c with
      | Xlt, Xgt => I.neg v
      | Xgt, Xlt => I.neg v
      | Xlt, Xlt => v
      | Xgt, Xgt => v
      | _, _ => I.nai
      end
    end
  end.

Definition tan_fast prec x :=
  match F.cmp x F.zero with
  | Xeq => I.bnd F.zero F.zero
  | Xlt => I.neg (tan_fastP prec (F.neg x))
  | Xgt => tan_fastP prec x
  | Xund => I.nai
  end.

End TranscendentalFloatFast.

(*
Require Import specific_ops.
Require Import stdz_carrier.
Module F := SpecificFloat StdZRadix2.
Module A := TranscendentalFloatFast F.
Time Eval vm_compute in (A.atan_fast 50%Z (Float 201%Z (-8)%Z)).
Time Eval vm_compute in (A.cos_fast 50%Z (Float 201%Z (-8)%Z)).
Time Eval vm_compute in (A.tan_fast 50%Z (Float 3619%Z (-8)%Z)).
Time Eval vm_compute in (A.sin_fast 50%Z (Float 201%Z (-8)%Z)).
*)

(*
Module Transcendental (F : FloatOps).

Definition try_round mode prec x e :=
  let l := F.sub mode prec x e in
  let u := F.add mode prec x e in
  match F.cmp l u with
  | Xeq => Some l
  | _ => None
  end.

Lemma try_round_correct :
  forall mode prec x e r,
  Xcmp (Xabs (Xsub (FtoX (F.toF x)) r)) (FtoX (F.toF e)) = Xlt ->
  match try_round mode prec x e with
  | Some f => FtoX (F.toF f) = FtoX (round F.radix mode (F.prec prec) r)
  | None => True
  end.
intros mode prec x e r H.
unfold try_round.
case_eq (F.cmp (F.sub mode prec x e) (F.add mode prec x e)) ; trivial.
rewrite F.cmp_correct.
rewrite Fcmp_correct.
rewrite F.sub_correct.
rewrite Fsub_correct.
rewrite F.add_correct.
rewrite Fadd_correct.
generalize H. clear H.
case r ; case (FtoX (F.toF x)) ; case (FtoX (F.toF e)) ;
  try (intros ; discriminate).
clear.
intros e x r.
unfold Xsub, Xadd, Xabs.
repeat rewrite round_correct_real.
unfold Xcmp.
generalize (Rcompare_correct (Rabs (x - r)) e).
case (Rcompare (Rabs (x - r)) e) ; intros He H ;
  try discriminate H ; clear H.
set (l := round_real F.radix mode (F.prec prec) (x - e)).
set (u := round_real F.radix mode (F.prec prec) (x + e)).
generalize (Rcompare_correct l u).
case (Rcompare l u) ; intros Hlu H ;
  try discriminate H ; clear H.
apply f_equal.
set (s := round_real F.radix mode (F.prec prec) r).
destruct (Rtotal_order l s) as [H|[H|H]].
2: trivial.
(* l < round r *)
assert (Xcmp (FtoX (round F.radix mode (F.prec prec) (Xreal (x + e))))
             (FtoX (round F.radix mode (F.prec prec) (Xreal r))) = Xlt).
repeat rewrite round_correct_real.
simpl.
fold u s.
rewrite <- Hlu.
rewrite Rcompare_correct_lt with (1 := H).
apply refl_equal.
generalize (round_monotone F.radix mode (F.prec prec) (Xreal (x + e)) (Xreal r)).
rewrite H0. clear H H0.
simpl.
rewrite Rcompare_correct_gt.
intro. discriminate.
destruct (Rabs_def2 _ _ He) as (_, H).
apply Rplus_lt_reg_r with (-e - r)%R.
replace (-e - r + r)%R with (-e)%R. 2: ring.
replace (-e - r + (x + e))%R with (x - r)%R. 2: ring.
exact H.
(* l > round r *)
assert (Xcmp (FtoX (round F.radix mode (F.prec prec) (Xreal (x - e))))
             (FtoX (round F.radix mode (F.prec prec) (Xreal r))) = Xgt).
repeat rewrite round_correct_real.
simpl.
fold l s.
rewrite Rcompare_correct_gt with (1 := H).
apply refl_equal.
generalize (round_monotone F.radix mode (F.prec prec) (Xreal (x - e)) (Xreal r)).
rewrite H0. clear H H0.
simpl.
rewrite Rcompare_correct_lt.
intro. discriminate.
destruct (Rabs_def2 _ _ He) as (H, _).
apply Rplus_lt_reg_r with (e - r)%R.
replace (e - r + (x - e))%R with (x - r)%R. 2: ring.
replace (e - r + r)%R with e. 2: ring.
exact H.
Qed.

End Transcendental.
*)