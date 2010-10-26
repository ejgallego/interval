Require Import Reals.
Require Import Bool.
Require Import ZArith.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Fcalc_sqrt.

Inductive float (radix : positive) : Set :=
  | Fnan : float radix
  | Fzero : float radix
  | Float : bool -> positive -> Z -> float radix.

Definition FtoX radix (f : float radix) :=
  match f with
  | Fzero => Xreal R0
  | Fnan => Xnan
  | Float s m e => Xreal (FtoR radix s m e)
  end.

Implicit Arguments FtoX.

(*
 * Fneg
 *)

Definition Fneg radix (f : float radix) :=
  match f with
  | Float s m e => Float radix (negb s) m e
  | _ => f
  end.

Implicit Arguments Fneg.

(*
 * Fabs
 *)

Definition Fabs radix (f : float radix) :=
  match f with
  | Float s m e => Float radix false m e
  | _ => f
  end.

Implicit Arguments Fabs.

(*
 * Fscale
 *)

Definition Fscale radix (f : float radix) d :=
  match f with
  | Float s m e => Float radix s m (e + d)
  | _ => f
  end.

Implicit Arguments Fscale.

(*
 * Fscale2
 *)

Definition Fscale2 radix (f : float radix) d :=
  match f with
  | Float s m e =>
    match radix, d with
    | xO xH, _ => Float radix s m (e + d)
    | _, Z0 => f
    | _, Zpos nb =>
      Float radix s (iter_pos nb _ (fun x => xO x) m) e
    | xO r, Zneg nb =>
      Float radix s (iter_pos nb _ (fun x => Pmult r x) m) (e + d)
    | _, _ => Fnan radix
    end
  | _ => f
  end.

Implicit Arguments Fscale2.

(*
 * Fcmp
 *
 * 1. Compare signs.
 * 2. Compare position of most significant digits.
 * 3. Compare shifted mantissas.
 *)

Definition shift radix m nb :=
  iter_pos nb _ (fun x => Pmult radix x) m.

Definition Fcmp_aux1 m1 m2 :=
  match Zcompare (Zpos m1) (Zpos m2) with
  | Eq => Xeq
  | Lt => Xlt
  | Gt => Xgt
  end.

Definition Fcmp_aux2 radix m1 e1 m2 e2 :=
  let d1 := count_digits radix m1 in
  let d2 := count_digits radix m2 in
  match Zcompare (e1 + Zpos d1)%Z (e2 + Zpos d2)%Z with
  | Lt => Xlt
  | Gt => Xgt
  | Eq =>
    match Zminus e1 e2 with
    | Zpos nb => Fcmp_aux1 (shift radix m1 nb) m2
    | Zneg nb => Fcmp_aux1 m1 (shift radix m2 nb)
    | Z0 => Fcmp_aux1 m1 m2
    end
  end.

Definition Fcmp radix (f1 f2 : float radix) :=
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
  | Float false m1 e1, Float false m2 e2 => Fcmp_aux2 radix m1 e1 m2 e2
  | Float true m1 e1, Float true m2 e2 => Fcmp_aux2 radix m2 e2 m1 e1
  end.

Implicit Arguments Fcmp.

(*
 * Fmin
 *)

Definition Fmin radix (f1 f2 : float radix) :=
  match Fcmp f1 f2 with
  | Xlt => f1
  | Xeq => f1
  | Xgt => f2
  | Xund => Fnan radix
  end.

Implicit Arguments Fmin.

(*
 * Fmax
 *)

Definition Fmax radix (f1 f2 : float radix) :=
  match Fcmp f1 f2 with
  | Xlt => f2
  | Xeq => f2
  | Xgt => f1
  | Xund => Fnan radix
  end.

Implicit Arguments Fmax.

(*
 * position
 *)

Inductive position : Set :=
  pos_Eq | pos_Lo | pos_Mi | pos_Up.

Inductive ufloat (radix : positive) : Set :=
  | Unan : ufloat radix
  | Uzero : ufloat radix
  | Ufloat : bool -> positive -> Z -> position -> ufloat radix.

Definition UtoX radix (f : ufloat radix) :=
  match f with
  | Uzero => Xreal R0
  | Ufloat s m e pos_Eq => Xreal (FtoR radix s m e)
  | _ => Xnan
  end.

Implicit Arguments UtoX.

Definition float_to_ufloat radix (x : float radix) :=
  match x with
  | Fnan => Unan radix
  | Fzero => Uzero radix
  | Float s m e => Ufloat radix s m e pos_Eq
  end.

Implicit Arguments float_to_ufloat.

Definition adjust_pos r d pos :=
  match r with
  | Z0 =>
    match pos with
    | pos_Eq => pos_Eq
    | _ => match d with xH => pos | _ => pos_Lo end
    end
  | Zneg _ => pos_Eq (* dummy *)
  | Zpos _ =>
    let (hd, mid) :=
      match d with
      | xO p => (p, match pos with pos_Eq => pos_Mi | _ => pos_Up end)
      | xI p => (p, match pos with pos_Eq => pos_Lo | _ => pos end)
      | xH => (xH, pos_Eq) (* dummy *)
      end in
    match Zcompare r (Zpos hd) with
    | Lt => pos_Lo
    | Eq => mid
    | Gt => pos_Up
    end
  end.

(*
 * Fround_none
 *)

Definition Fround_none radix (uf : ufloat radix) :=
  match uf with
  | Uzero => Fzero radix
  | Ufloat s m e pos_Eq => Float radix s m e
  | _ => Fnan radix
  end.

Implicit Arguments Fround_none.

(*
 * Fround_at_prec
 *
 * Assume the position is scaled at exponent ex + min(0, px - p).
 *)

Definition need_change mode m pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | pos_Mi =>
      match m with
      | xO _ => false
      | _ => true
      end
    | _ => false
    end
  end.

Definition need_change_radix radix mode m pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | pos_Mi =>
      match m with
      | xO _ => false
      | _ => match radix with xO _ => false | _ => true end
      end
    | _ => false
    end
  end.

Definition adjust_mantissa mode m pos sign :=
  if need_change mode m pos sign then Psucc m else m.

Definition Fround_at_prec radix mode prec (uf : ufloat radix) :=
  match uf with
  | Unan => Fnan radix
  | Uzero => Fzero radix
  | Ufloat sign m1 e1 pos =>
    match (Zpos (count_digits radix m1) - Zpos prec)%Z with
    | Zpos nb =>
      let d := shift radix xH nb in
      match Zdiv_eucl (Zpos m1) (Zpos d) with
      | (Zpos m2, r) =>
        let pos2 := adjust_pos r d pos in
        let e2 := (e1 + Zpos nb)%Z in
        Float radix sign (adjust_mantissa mode m2 pos2 sign) e2
      | _ => Fnan radix (* dummy *)
      end
    | Z0 => Float radix sign (adjust_mantissa mode m1 pos sign) e1
    | Zneg nb =>
      if need_change_radix radix mode m1 pos sign then
        Float radix sign (Psucc (shift radix m1 nb)) (e1 + Zneg nb)
      else Float radix sign m1 e1
    end
  end.

Implicit Arguments Fround_at_prec.

(*
 * Fround_at_exp
 *
 * Assume the position is scaled at exponent min(ex, e).
 *)

Definition need_change_zero mode pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | _ => false
    end
  end.

Definition Fround_at_exp radix mode e2 (uf : ufloat radix) :=
  match uf with
  | Unan => Fnan radix
  | Uzero => Fzero radix
  | Ufloat sign m1 e1 pos =>
    match (e2 - e1)%Z with
    | Zpos nb =>
      match Zcompare (Zpos (count_digits radix m1)) (Zpos nb) with
      | Gt =>
        let d := shift radix xH nb in
        match Zdiv_eucl (Zpos m1) (Zpos d) with
        | (Zpos m2, r) =>
          let pos2 := adjust_pos r d pos in
          Float radix sign (adjust_mantissa mode m2 pos2 sign) e2
        | _ => Fnan radix (* dummy *)
        end
      | Eq =>
        let d := shift radix xH nb in
        let pos2 := adjust_pos (Zpos m1) d pos in
        if need_change_zero mode pos2 sign then
          Float radix sign xH e2
        else Fzero radix
      | Lt =>
        let pos2 := match pos with pos_Eq => pos_Eq | _ => pos_Lo end in
        if need_change_zero mode pos2 sign then
          Float radix sign xH e2
        else Fzero radix
      end
    | Z0 => Float radix sign (adjust_mantissa mode m1 pos sign) e1
    | Zneg nb =>
      if need_change_radix radix mode m1 pos sign then
        Float radix sign (Psucc (shift radix m1 nb)) e2
      else Float radix sign m1 e1
    end
  end.

Implicit Arguments Fround_at_exp.

(*
 * Fround
 *)

Definition Fround radix mode prec (x : float radix) :=
  Fround_at_prec mode prec (float_to_ufloat x).

Implicit Arguments Fround.

(*
 * Fint_exact
 *)

Definition Fint_exact radix mode (x : float radix) :=
  Fround_at_exp mode 0 (float_to_ufloat x).

Implicit Arguments Fint_exact.

(*
 * Fint
 *)

Definition Fint radix mode prec x :=
  match x with
  | Float sx mx ex =>
    match Zcompare (Zpos (count_digits radix mx) + ex) (Zpos prec) with
    | Gt => Fround_at_prec mode prec
    | _ => Fround_at_exp mode 0
    end (Ufloat radix sx mx ex pos_Eq)
  | _ => x
  end.

Implicit Arguments Fint.

(*
 * Fmul, Fmul_exact
 *)

Definition Fmul_aux radix (x y : float radix) :=
  match x, y with
  | Fnan, _ => Unan radix
  | _, Fnan => Unan radix
  | Fzero, _ => Uzero radix
  | _, Fzero => Uzero radix
  | Float sx mx ex, Float sy my ey =>
    Ufloat radix (xorb sx sy) (Pmult mx my) (ex + ey) pos_Eq
  end.

Implicit Arguments Fmul_aux.

Definition Fmul radix mode prec (x y : float radix) :=
  Fround_at_prec mode prec (Fmul_aux x y).

Implicit Arguments Fmul.

Definition Fmul_exact radix (x y : float radix) :=
  Fround_none (Fmul_aux x y).

Implicit Arguments Fmul_exact.

(*
 * Fadd_slow, Fadd_exact
 *
 * 1. Shift the mantissa with the highest exponent to match the other one.
 * 2. Perform the addition/subtraction.
 * 3. Round to p digits.
 *
 * Complexity is fine as long as px <= p and py <= p and exponents are close.
 *)

Definition Fadd_slow_aux1 radix sx sy mx my e :=
  if eqb sx sy then
    Ufloat radix sx (Pplus mx my) e pos_Eq
  else
    match (Zpos mx + Zneg my)%Z with
    | Z0 => Uzero radix
    | Zpos p => Ufloat radix sx p e pos_Eq
    | Zneg p => Ufloat radix sy p e pos_Eq
    end.

Definition Fadd_slow_aux2 radix sx sy mx my ex ey :=
  match Zminus ex ey with
  | Zpos nb => Fadd_slow_aux1 radix sx sy (shift radix mx nb) my ey
  | Zneg nb => Fadd_slow_aux1 radix sx sy mx (shift radix my nb) ex
  | Z0 => Fadd_slow_aux1 radix sx sy mx my ex
  end.

Definition Fadd_slow_aux radix (x y : float radix) :=
  match x, y with
  | Fnan, _ => Unan radix
  | _, Fnan => Unan radix
  | Fzero, Fzero => Uzero radix
  | Fzero, Float sy my ey =>
    Ufloat radix sy my ey pos_Eq
  | Float sx mx ex, Fzero =>
    Ufloat radix sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_slow_aux2 radix sx sy mx my ex ey
  end.

Implicit Arguments Fadd_slow_aux.

Definition Fadd_slow radix mode prec (x y : float radix) :=
  Fround_at_prec mode prec (Fadd_slow_aux x y).

Implicit Arguments Fadd_slow.

Definition Fadd_exact radix (x y : float radix) :=
  Fround_none (Fadd_slow_aux x y).

Implicit Arguments Fadd_exact.

(*
 * Fadd_fast
 *
 * 1. Guess a lower bound on the exponent of the result.
 * 2. Truncate the mantissa (at most one) that extends farther.
 * 3. Adjust the mantissa so that the propagated truncation error is inward.
 * 4. Shift the (usually other) mantissa to match it.
 * 5. Perform the addition/subtraction.
 * 6. Round to p digits wrt the position given by the truncation.
 *
 * Complexity is fine as long as, either
 *  . px <= p and py <= p, or
 *  . pv <= p and v has same magnitude than the result.
 *
 * Details:
 *
 *  . Same sign:
 *    Exponent of the result is at least max(u1, u2) - p.
 *    Target exponent e is min(max(e1, e2), max(u1, u2) - p).
 *    1. if either e1 < e or e2 < e (assume e2 < e), then e1 >= e
 *       if u2 <= e, then f2 < b^u2 <= b^e
 *         return rounded f1 at p digits with pos(f2)
 *       otherwise e2 < e < u2
 *       truncate m2 at e, shift m1 at e
 *    2. if e1 >= e and e2 >= e
 *       shift m1 or m2 at min(e1, e2)
 *    Perform addition.
 *
 *  . Opposite signs: (assume u1 > u2 + 1, otherwise full subtraction)
 *    Exponent of the result is at least u1 - p - 1.
 *    Target exponent e is min(max(e1, e2), u1 - p - 1).
 *    1. if u2 < e, then f2 < b^u2 <= b^e / b
 *       return f1 - b^(e - 2)
 *    2. if u2 = e, then change e to e - 1 and continue
 *    3. if e2 < e < u2, then e1 >= e
 *       truncate m2 outward at e, shift m1 at e
 *    4. if e1 < e < u2, then e2 >= e and e < u2 < u1
 *       truncate m1 at e, shift m2 at e
 *    5. if e1 >= e and e2 >= e
 *       shift m1 or m2 at min(e1, e2)
 *    Perform subtraction.
 *)

Definition truncate radix m1 nb :=
  let d := iter_pos nb _ (fun x => Pmult radix x) xH in
  match Zdiv_eucl (Zpos m1) (Zpos d) with
  | (Zpos m2, r) => (m2, adjust_pos r d pos_Eq)
  | _ => (xH, pos_Lo) (* dummy *)
  end.

Definition Fadd_fast_aux1 radix s m1 m2 e d2 u2 e1 e2 :=
  match Zcompare u2 e with
  | Lt => (* negligible value *)
    Ufloat radix s m1 e1 pos_Lo
  | Eq => (* almost negligible *)
    Ufloat radix s m1 e1 (adjust_pos (Zpos m2) (shift radix xH d2) pos_Eq)
  | Gt =>
    match (e - e2)%Z with
    | Zpos p =>
      let (n2, pos) := truncate radix m2 p in
      let n1 := 
        match (e1 - e)%Z with
        | Zpos q => (shift radix m1 q)
        | Z0 => m1
        | _ => xH (* dummy *)
        end in
      Ufloat radix s (Pplus n1 n2) e pos
    | _ => Unan radix (* dummy *)
    end
  end.

Definition Fsub_fast_aux1 radix s m1 m2 e e1 e2 :=
  match (e - e2)%Z with
  | Zpos p =>
    let (n2, pos) :=
      match truncate radix m2 p with
      | (n, pos_Eq) => (n, pos_Eq)
      | (n, pos_Lo) => (Psucc n, pos_Up)
      | (n, pos_Mi) => (Psucc n, pos_Mi)
      | (n, pos_Up) => (Psucc n, pos_Lo)
      end in
    let n1 := 
      match (e1 - e)%Z with
      | Zpos q => (shift radix m1 q)
      | Z0 => m1
      | _ => xH (* dummy *)
      end in
    Ufloat radix s (Pminus n1 n2) e pos
  | _ => Unan radix (* dummy *)
  end.

Definition Fsub_fast_aux2 radix prec s m1 m2 u1 u2 e1 e2 :=
  let e := Zmin (Zmax e1 e2) (u1 + Zneg (prec + 1)) in
  if Zlt_bool e2 e then
    match Zcompare u2 e with
    | Lt => (* negligible value *)
      Fadd_slow_aux2 radix s (negb s) m1 xH e1 (e - 2)
    | Eq => (* almost negligible *)
      let ee := (e - 1)%Z in
      if Zeq_bool e2 ee then
        let n1 :=
          match (e1 - ee)%Z with
          | Zpos q => (shift radix m1 q)
          | Z0 => m1
          | _ => xH (* dummy *)
          end in
        Ufloat radix s (Pminus n1 m2) ee pos_Eq
      else
        Fsub_fast_aux1 radix s m1 m2 ee e1 e2
    | Gt =>
      Fsub_fast_aux1 radix s m1 m2 e e1 e2
    end
  else if Zlt_bool e1 e then
    match (e - e1)%Z with
    | Zpos p =>
      let (n1, pos) := truncate radix m1 p in
      let n2 := 
        match (e2 - e)%Z with
        | Zpos q => (shift radix m2 q)
        | Z0 => m2
        | _ => xH (* dummy *)
        end in
      Ufloat radix s (Pminus n1 n2) e pos
    | _ => Unan radix (* dummy *)
    end
  else
    Fadd_slow_aux2 radix s (negb s) m1 m2 e1 e2.

Definition Fadd_fast_aux2 radix prec s1 s2 m1 m2 e1 e2 :=
  let d1 := count_digits radix m1 in
  let d2 := count_digits radix m2 in
  let u1 := (e1 + Zpos d1)%Z in
  let u2 := (e2 + Zpos d2)%Z in
  if eqb s1 s2 then
    (* same sign *)
    let e := Zmin (Zmax e1 e2) ((Zmax u1 u2) + Zneg prec) in
    if Zlt_bool e1 e then
      Fadd_fast_aux1 radix s1 m2 m1 e d1 u1 e2 e1
    else if Zlt_bool e2 e then
      Fadd_fast_aux1 radix s1 m1 m2 e d2 u2 e1 e2
    else
      Fadd_slow_aux2 radix s1 s2 m1 m2 e1 e2
  else
    (* opposite sign *)
    if Zlt_bool (u1 + 1)%Z u2 then
      Fsub_fast_aux2 radix prec s2 m2 m1 u2 u1 e2 e1
    else if Zlt_bool (u2 + 1)%Z u1 then
      Fsub_fast_aux2 radix prec s1 m1 m2 u1 u2 e1 e2
    else
      (* massive cancellation possible *)
      Fadd_slow_aux2 radix s1 s2 m1 m2 e1 e2.

Definition Fadd_fast_aux radix prec (x y : float radix) :=
  match x, y with
  | Fnan, _ => Unan radix
  | _, Fnan => Unan radix
  | Fzero, Fzero => Uzero radix
  | Fzero, Float sy my ey =>
    Ufloat radix sy my ey pos_Eq
  | Float sx mx ex, Fzero =>
    Ufloat radix sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_fast_aux2 radix prec sx sy mx my ex ey
  end.

Implicit Arguments Fadd_fast_aux.

Definition Fadd_fast radix mode prec (x y : float radix) :=
  Fround_at_prec mode prec (Fadd_fast_aux prec x y).

Implicit Arguments Fadd_fast.

Definition Fadd := Fadd_slow.

Implicit Arguments Fadd.

(*
 * Fsub, Fsub_exact
 *)

Definition Fsub_slow_aux radix (x y : float radix) :=
  match x, y with
  | Fnan, _ => Unan radix
  | _, Fnan => Unan radix
  | Fzero, Fzero => Uzero radix
  | Fzero, Float sy my ey => Ufloat radix (negb sy) my ey pos_Eq
  | Float sx mx ex, Fzero => Ufloat radix sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_slow_aux2 radix sx (negb sy) mx my ex ey
  end.

Implicit Arguments Fsub_slow_aux.

Definition Fsub_slow radix mode prec (x y : float radix) :=
  Fround_at_prec mode prec (Fsub_slow_aux x y).

Implicit Arguments Fsub_slow.

Definition Fsub := Fsub_slow.

Implicit Arguments Fsub.

Definition Fsub_exact radix (x y : float radix) :=
  Fround_none (Fsub_slow_aux x y).

Implicit Arguments Fsub_exact.

(*
 * Fdiv
 *
 * 1. Shift dividend mantissa so that it has at least py + p digits.
 * 2. Perform the euclidean division.
 * 3. Compute position with remainder.
 * 4. Round to p digits.
 *
 * Complexity is fine as long as px <= 2p and py <= p.
 *)

Definition Fdiv_aux radix prec (x y : float radix) :=
  match x, y with
  | Fnan, _ => Unan radix
  | _, Fnan => Unan radix
  | _, Fzero => Unan radix
  | Fzero, _ => Uzero radix
  | Float sx mx ex, Float sy my ey =>
    let dx := count_digits radix mx in
    let dy := count_digits radix my in
    let e := (ex - ey)%Z in
    let (m2, e2) :=
      match (Zpos dy + Zpos prec + Zneg dx)%Z with
      | Zpos nb => (shift radix mx nb, (e + Zneg nb)%Z)
      | _ => (mx, e)
      end in
    match Zdiv_eucl (Zpos m2) (Zpos my) with
    | (Zpos q, r) => Ufloat radix (xorb sx sy) q e2 (adjust_pos r my pos_Eq)
    | _ => Unan radix (* dummy *)
    end
  end.

Implicit Arguments Fdiv_aux.

Definition Fdiv radix mode prec (x y : float radix) :=
  Fround_at_prec mode prec (Fdiv_aux prec x y).

Implicit Arguments Fdiv.

(*
 * Frem
 *
 * 1. Shift mantissas so that dividend and divisor have the same exponents.
 * 2. Perform the euclidean division.
 * 3. Adjust quotient to closest integer (tie breaking to even).
 * 4. Scale remainder to common exponent.
 * 5. Round remainder to p digits.
 *)

Definition Frem_aux1 radix mx my s e :=
  let (q1, r1) := Zdiv_eucl (Zpos mx) (Zpos my) in
  let (q2, r2) :=
    match
      match my with
      | xH => false
      | xO p =>
        match Zcompare r1 (Zpos p) with
        | Lt => false
        | Eq =>
          match q1 with
          | Z0 => false
          | Zpos (xO _) => false
          | _ => true
          end
        | Gt => true
        end
      | xI p =>
        match Zcompare r1 (Zpos p) with
        | Lt => false
        | Eq => false
        | Gt => true
        end
      end
    with
    | false => (q1, r1)
    | true => (q1 + 1, r1 - Zpos my)%Z
    end in
 (match q2 with
  | Zpos p => Float radix s p 0
  | Z0 => Fzero radix
  | _ => Fnan radix (* dummy *)
  end,
  match r2 with
  | Zpos p => Ufloat radix s p e pos_Eq
  | Z0 => Uzero radix
  | Zneg p => Ufloat radix (negb s) p e pos_Eq
  end).

Definition Frem_aux radix (x y : float radix) :=
  match x, y with
  | Fnan, _ => (Fnan radix, Unan radix)
  | _, Fnan => (Fnan radix, Unan radix)
  | _, Fzero => (Fnan radix, Unan radix)
  | Fzero, _ => (Fzero radix, Uzero radix)
  | Float sx mx ex, Float sy my ey =>
    let s := xorb sx sy in
    match (ex - ey)%Z with
    | Zpos nb => Frem_aux1 radix (shift radix mx nb) my s ey
    | Z0 => Frem_aux1 radix mx my s ex
    | Zneg nb => Frem_aux1 radix mx (shift radix my nb) s ex
    end
  end.

Implicit Arguments Frem_aux.

Definition Frem radix mode prec (x y : float radix) :=
  let (q, r) := Frem_aux x y in
  (q, Fround_at_prec mode prec r).

Implicit Arguments Frem.

Definition validate_radix (radix : positive) (f : Fcore_Raux.radix -> ufloat radix) : ufloat radix.
intros r f.
case_eq (Zle_bool 2 (Zpos r)).
intros H.
apply f.
exact (Fcore_Raux.Build_radix _ H).
intros _.
exact (Unan r).
Defined.

Definition convert_location l :=
  match l with
  | Fcalc_bracket.loc_Exact => pos_Eq
  | Fcalc_bracket.loc_Inexact l =>
    match l with Lt => pos_Lo | Eq => pos_Mi | Gt => pos_Up end
  end.

(*
 * Fsqrt
 *
 * 1. Shift the mantissa so that it has at least 2p-1 digits;
 *    shift it one digit more if the new exponent is not even.
 * 2. Compute the square root s (at least p digits) of the new
 *    mantissa, and its remainder r.
 * 3. Current position: r == 0  =>  Eq,
 *                      r <= s  =>  Lo,
 *                      r >= s  =>  Up.
 * 4. Round to p digits.
 *
 * Complexity is fine as long as p1 <= 2p-1.
 *)

Definition Fsqrt_aux radix prec (f : float radix) : ufloat radix :=
  match f with
  | Float false m e =>
    validate_radix radix (fun rdx =>
      match Fsqrt_core rdx (Zpos prec) (Zpos m) e with
      | (Zpos m, e, l) =>
        Ufloat radix false m e (convert_location l)
      | _ => Unan radix (* dummy *)
      end)
  | Float true _ _ => Unan radix
  | Fzero => Uzero radix
  | Fnan => Unan radix
  end.

Implicit Arguments Fsqrt_aux.

Definition Fsqrt radix mode prec (x : float radix) :=
  Fround_at_prec mode prec (Fsqrt_aux prec x).

Implicit Arguments Fsqrt.

(*
 * Fmag
 *)

Definition Fmag radix (x : float radix) :=
  match x with
  | Float _ m e => Zplus e (Zpos (count_digits radix m))
  | _ => Z0
  end.