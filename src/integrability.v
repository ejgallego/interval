Require Import List.
Require Import ZArith.
(* Require Import Reals. *)
Require Import Coquelicot.

Require Import Interval_missing.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_generic_proof.
Require Import Interval_float_sig.
Require Import Interval_interval.
Require Import Interval_interval_float_full.
(* Require Import Interval_integral. *)
Require Import Interval_bisect.

Require Import ssreflect ssrnat.

Module Integrability (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.
Module A := IntervalAlgos I.

Section Integrability.

Lemma ex_RInt_Id a b : ex_RInt (fun x => x) a b.
Proof.
Admitted. (* can't find a useful theorem *)

Section revEq.
Require Import seq.

Lemma revEq : forall A l, @List.rev A l = rev l.
Proof.
move => A.
elim => [|a l HI] //.
rewrite /= rev_cons.
by rewrite -cats1 HI.
Qed.

Lemma nthEq A n (l : seq A) def : List.nth n l def = nth def l n.
move: l.
elim Hn : n => [|n0 HIn] l.
  by case: l.
case: l HIn => [ | a0 l] HIn // .
by rewrite /= -HIn.
Qed.

Lemma mapEq A B (l : seq A) (f : A -> B) : List.map f l = map f l.
Proof.
elim: l => [|a0 l HIl] => //= .
Qed.

End revEq.

Parameter prec : I.precision.
Definition evalInt := A.BndValuator.eval prec.
Definition boundsToInt b := map A.interval_from_bp b.
Definition boundsToR b := map A.real_from_bp b.

Definition notInan (fi : Interval_interval_float.f_interval F.type) :=
  match fi with
    | Interval_interval_float.Inan => false
    | _ => true end = true.

Section MissingContinuity.
Axiom Pi : R. (* until I find it *)

(* Lemma continuous_all_comp {U V W : UniformSpace} D E (f : U -> V) (g : V -> W) : *)
(*   continuous_on D f -> continuous_on E g *)
(*   -> continuous_on D (fun x => g (f x)). *)
(* Proof. *)
(* move => Hf Hg. *)
(* apply: continuous_on_forall. *)
(* move => x HDx. *)
(* apply: continuous_comp. *)
(* apply: (continuous_continuous_on D). *)
(* Search (locally _ _). *)

(* Search _ ex_RInt. *)

(* this should probably be generalized in some fashion relatively to opp *)
(* Lemma continuous_on_Ropp D (f : R -> R) : *)
(*   continuous_on D f -> *)
(*   continuous_on D (fun x => - (f x)). *)
(* Proof. *)
(* Admitted. *)
Definition continuous_all (D : R -> Prop) (f : R -> R) :=
  forall x, D x -> continuous f x.

Lemma continuous_all_id D : continuous_all D (fun x => x).
Proof.
move => x HDx.
by apply: continuous_id.
Qed.

Lemma continuous_all_const D a : continuous_all D (fun x => a).
Proof.
by move => x HDx; apply: continuous_const.
Qed.

Lemma continuous_all_ext (D : R -> Prop) (f g : R -> R) :
  (forall x, f x = g x) -> (* why can't I relax this more? (forall x in D *)
  continuous_all D f ->
  continuous_all D g.
Proof.
move => HDfg HDf.
move => x HDx.
apply: (continuous_ext f) => // .
by apply: HDf.
Qed.

Lemma continuous_all_comp D E f g :
  continuous_all D f ->
  continuous_all E g ->
  (forall x, E (f x)) ->
  continuous_all D (fun x => g (f x)).
Proof.
move => HDf HEg HEimF.
move => x HDx.
apply: continuous_comp.
by apply: HDf.
apply: HEg.
  by apply: HEimF.
Qed.

Lemma continuous_all_Ropp :
  continuous_all (fun x => True) (fun x => - x).
Proof.
Admitted.

Lemma continuous_all_weaken (Strong : R -> Prop) (Weak : R -> Prop) f :
  (forall x : R, Weak x -> Strong x) ->
  continuous_all Strong f ->
  continuous_all Weak f.
Proof.
move => HWS HS.
move => x HW.
apply: HS.
by apply: HWS.
Qed.

Lemma continuous_all_Ropp_fun D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => - (f x)).
Proof.
move => HDf.
apply: (continuous_all_comp D (fun x => True) ) => //.
apply: continuous_all_Ropp.
Qed.

Lemma continuous_all_Rabs D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => Rabs (f x)).
Proof.
Admitted.

Lemma continuous_all_Rinv D (f : R -> R) :
  continuous_all D f ->
  (forall x, D x -> f x > 0) \/ (forall x, D x -> f x < 0) ->
  continuous_all D (fun x => / (f x)).
Proof.
Admitted.

Lemma continuous_all_Rmult D (f : R -> R) (g : R -> R) :
  continuous_all D f ->
  continuous_all D g ->
  continuous_all D (fun x => f x * g x).
Proof.
Admitted.

Lemma continuous_all_sqrt D (f : R -> R) :
  continuous_all D f ->
  (forall x, D x -> f x >= 0) ->
  continuous_all D (fun x => sqrt (f x)).
Proof.
Admitted.

Lemma continuous_all_cos D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => cos (f x)).
Proof.
Admitted.


Lemma continuous_all_sin D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => sin (f x)).
Proof.
Admitted.

Lemma continuous_all_tan D (f : R -> R) :
  continuous_all D f ->
  (forall x, D x -> (f x > - Pi / 2 /\ f x < Pi / 2)) ->
  continuous_all D (fun x => tan (f x)).
Proof.
Admitted.

Lemma continuous_all_atan D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => atan (f x)).
Proof.
Admitted.

Lemma continuous_all_exp D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => exp (f x)).
Proof.
Admitted.


Lemma continuous_all_ln D (f : R -> R) :
  continuous_all D f ->
  (forall x, D x -> f x > 0) ->
  continuous_all D (fun x => ln (f x)).
Proof.
Admitted.

Lemma continuous_all_powerRZ D (f : R -> R) n :
  continuous_all D f ->
  (match n with
     | Zpos m => True
     | Z0 => True
     | Zneg m  => (forall x, D x -> f x < 0) \/ (forall x, D x -> f x > 0)
   end
  ) ->
  continuous_all D (fun x => powerRZ (f x) n).
Proof.
Admitted.

Lemma continuous_all_Rplus (D : R -> Prop) (f g : R -> R) :
  continuous_all D f ->
  continuous_all D g ->
continuous_all D (fun x => f x + g x).
Proof.
move => Hf Hg.
move => x Hx.
apply: continuous_plus.
by apply: Hf.
by apply: Hg.
Qed.

Lemma continuous_all_Rsub (D : R -> Prop) (f g : R -> R) :
  continuous_all D f ->
  continuous_all D g ->
continuous_all D (fun x => f x - g x).
Proof.
move => Hf Hg.
move => x Hx.
apply: continuous_minus.
by apply: Hf.
by apply: Hg.
Qed.

Lemma continuous_all_Rdiv (D : R -> Prop) (f g : R -> R) :
  continuous_all D f ->
  continuous_all D g ->
  (forall x, D x ->  g x > 0) \/ (forall x, D x ->  g x < 0) ->
continuous_all D (fun x => f x / g x).
Proof.
move => Hf Hg Hgpos.
move => x Hx.
(* apply: continuous_div. *) (* unfortunately there is no such lemma *)
(* by apply: Hf. *)
(* by apply: Hg. *)
Admitted.

(* We need to capture preconditions for (unop f) to be continuous *)
Definition domain unop g (P : R -> Prop) :=
  match unop with
    | Neg => True
    | Abs => True
    | Inv => (forall x, P x -> g x < 0) \/ (forall x, P x -> g x > 0)
    | Sqr => True
    | Sqrt => (forall x, P x -> g x >= 0)
    | Cos => True
    | Sin => True
    | Tan => forall x, P x -> (g x > - Pi / 2 /\ g x < Pi / 2)
    | Atan => True
    | Exp => True
    | Ln => (forall x, P x -> g x > 0)
    | PowerInt n =>
      (match n with
         | Zpos m => True
         | Z0 => True
         | Zneg m  => (forall x, P x -> g x < 0) \/ (forall x, P x -> g x > 0)
       end
      )
  end.

Lemma domain_correct unop D g:
  continuous_all D g ->
  (domain unop g D) ->
  continuous_all D (fun x => unary real_operations unop (g x)).
Proof.
move => Hgcont.
case Hunop: unop => HD; rewrite /domain in HD.
(* and now 12 cases, one for each unary operator *)
- by apply: continuous_all_Ropp_fun.
- by apply: continuous_all_Rabs.
(* - case: HD => [Hpos|Hneg]. *)
-  apply: continuous_all_Rinv => //; case: HD.
     by right.
   by left.
- by apply: continuous_all_Rmult.
- by apply: continuous_all_sqrt.
- by apply: continuous_all_cos.
- by apply: continuous_all_sin.
- by apply: continuous_all_tan.
- by apply: continuous_all_atan .
- by apply: continuous_all_exp.
- by apply: continuous_all_ln.
- by apply: continuous_all_powerRZ .
Qed.

(* Lemma sqrt_continuous x: x > 0 -> continuous sqrt x. *)
(* Admitted. *)


(* Lemma tan_continuous x : (x > - Pi / 2 /\ x < Pi / 2) -> continuous tan x. *)
(* Admitted. *)
(* Lemma atan_continuous x : continuous atan x. *)
(* Admitted. *)
(* Lemma ln_continuous x : (x > 0) -> continuous ln x. *)
(* Admitted. *)


End MissingContinuity.

Section MissingIntegrability.

Lemma ex_RInt_Rabs f a b : ex_RInt f a b -> ex_RInt (fun x => Rabs (f x)) a b.
Admitted.

Lemma ex_RInt_Rmult f g a b : ex_RInt f a b ->
                              ex_RInt g a b ->
                              ex_RInt (fun x => f x * g x) a b.
Admitted.

End MissingIntegrability.

Section Preliminary.
Require Import seq.

Definition interval_operations := (A.BndValuator.operations prec).

Lemma evalOpRight (A : Type) (ops : operations A) (z : A) op (prog : seq term) l m :
  nth z (@eval_generic A z ops (rcons prog op) l) m =
  nth z
      (@eval_generic_body A z
         ops
         (@eval_generic _ z ops prog l) op) m.
Proof.
rewrite  /A.BndValuator.eval rev_formula revEq rev_rcons /= .
by rewrite rev_formula revEq.
Qed.

(* Lemma evalRealOpRight op prog l m : (* raw form, will probably change *) *)
(*   nth R0 (eval_real (rcons prog op) l) m = *)
(*   nth 0 *)
(*       (eval_generic_body *)
(*          0 *)
(*          real_operations *)
(*          (eval_real prog l) op) m. *)
(* Proof. *)
(* by apply: evalOpRight. *)
(* Qed. *)

(* Lemma evalIntOpRight op prog l m : *)
(*   nth I.nai (evalInt (rcons prog op) l) m = *)
(*   nth I.nai *)
(*       (eval_generic_body *)
(*          I.nai *)
(*          interval_operations *)
(*          (evalInt prog l) op) m. *)
(* Proof. *)
(* by apply: evalOpRight. *)
(* Qed. *)

(* Lemma unNamed1 unop n prog a b bounds m: *)
(*    (forall m, ex_RInt *)
(*      (fun x => nth R0 (eval_real prog (x::boundsToR bounds)) m ) *)
(*      a *)
(*      b) *)
(*    -> *)
(*    ex_RInt *)
(*      (fun x =>  *)
(*         nth R0 (eval_real (rcons prog (Unary unop n)) (x::boundsToR bounds)) m) *)
(*      a *)
(*      b. *)
(* Proof. *)
(* move => Hprog. *)
(* apply: ex_RInt_ext. *)
(* (* first we get rid of the rcons and put the operation upfront *) *)
(* exact: (fun x => nth 0 *)
(*       (eval_generic_body *)
(*          0 *)
(*          real_operations *)
(*          (eval_generic  *)
(*             0  *)
(*             real_operations  *)
(*             prog  *)
(*             (x :: boundsToR bounds))  *)
(*          (Unary unop n)) m). *)
(* move => x _. *)
(* by rewrite evalRealOpRight. *)

(* (* now we distinguish the easy case (m>0), *)
(* which is actually free from the hypothesis, *)
(* and the core of the proof, (m=0) *) *)
(* case Hm : m => [|m0]; last first. *)

(* (* easy case: m > 0 *) *)
(* - apply: ex_RInt_ext. *)
(*     exact: *)
(*       (fun x : R => *)
(*          nth 0 *)
(*              (eval_generic *)
(*                 0 *)
(*                 real_operations *)
(*                 prog *)
(*                 (x :: boundsToR bounds)%SEQ) *)
(*              m0). *)
(*     move => x Huseless. *)
(*     by rewrite -nth_behead. *)
(*   by apply: Hprog. *)

(* (* now the meat of the proof: m=0 *) *)
(* (* first get the operation up front *) *)
(* - apply: ex_RInt_ext. *)
(*   exact: *)
(*     (fun x => *)
(*        (unary *)
(*           real_operations *)
(*           unop *)
(*           (nth *)
(*              0 *)
(*              (eval_real prog (x :: boundsToR bounds)%SEQ) *)
(*              n) *)
(*        ) *)
(*     ). *)
(*   move => x _. *)
(*   by rewrite /= nthEq. *)

(*   case Hunop: unop => /=. (* and now 12 cases to treat *) *)
(*   + by apply: ex_RInt_opp; apply: Hprog. *)
(*   + by apply: ex_RInt_Rabs; apply: Hprog. *)
(*   + admit. (* false here, we need to add some hypotheses ("0 \notin I")*) *)
(*   + by apply: ex_RInt_Rmult; apply: Hprog. *)
(*   + admit. *)
(*   + admit. *)
(*   + admit. *)
(*   + admit. *)
(*   + admit. *)
(*   + admit. *)
(*   + admit. *)
(*   + admit. *)
(* Admitted. *)

(* Lemma continuous_on_comp :  *)
(*   forall (U V W : UniformSpace) (f : U -> V) (g : V -> W), *)
(* continuous_on U f -> continuous_on V g -> continuous_on U (fun x0 : U => g (f x0)). *)


Definition eval_correct_int prog i bounds m :=
  notInan (nth I.nai
          (evalInt prog (i::boundsToInt bounds))
          m).

(* Lemma notXnan_eval_correct prog i bounds m x : *)
(*   eval_correct_int prog i bounds m -> *)
(*   nth Xnan (eval_ext prog (Xreal x::map Xreal (boundsToR bounds))) m <> Xnan. *)
(* Proof. *)
(* move => Hcorrect. *)

(* Check (eval_inductive_prop_fun). *)

(* Lemma eval_eval_ext prog x bounds n r : *)
(*   nth  *)
(*     Xnan  *)
(*     (eval_ext prog (Xreal x :: map Xreal (boundsToR bounds))%SEQ)  *)
(*     n =  *)
(*   Xreal r -> *)
(*   nth 0 (eval_real prog (x :: boundsToR bounds)%SEQ) n = r. *)
(* Proof. *)
(* rewrite -2!nthEq. *)
(* have -> :  *)
(*   (Xreal x :: map Xreal (boundsToR bounds))%SEQ =  *)
(*   map Xreal (x :: boundsToR bounds)%SEQ by []. *)
(* rewrite -!mapEq. *)
(* apply: (xreal_to_real (fun xR => xR = Xreal r) (fun x => x = r)) => //= . *)
(* by move => r0 H; inversion H. *)
(* Qed. *)

Section notInanProperties.

Lemma notInan_convert i :
  I.convert i = Inan -> i = Interval_interval_float.Inan.
case: i => // .
Qed.

Definition notXnan (xR : ExtendedR) :=
  match xR with
    | Xnan => false
    | Xreal _ => true end = true.


Lemma notInan_inversion_Inv prec i :
notInan (I.inv prec i) -> ~ contains (I.convert i) (Xreal 0) .
Proof.
move => HnotInan Hcontains0.
suff: contains (I.convert (I.inv prec i)) Xnan => [Habs|].
  move: HnotInan.
  have := (xreal_ssr_compat.contains_Xnan Habs).
  by case: (I.inv prec i).
have -> : Xnan = Xinv (Xreal 0) by rewrite /= is_zero_correct_zero.
by apply: I.inv_correct.
Qed.

Lemma notInan_inversion_Inv_stronger prec i :
  notInan (I.inv prec i) ->
  (forall x, contains (I.convert i) (Xreal x) -> x < 0) \/
  (forall x, contains (I.convert i) (Xreal x) -> x > 0).
Proof.
move => HnotInan.
suff: ~ contains (I.convert i) (Xreal 0); last first.
  by apply: notInan_inversion_Inv.
move => Hnot0.
set P :=  (X in X \/ _).
set Q :=  (X in _ \/ X).
suff: ~ (~ P /\ ~ Q).
move => H_andnot.
apply: Classical_Prop.NNPP. (* can we do without classical reasoning ? *)
move => H1.
apply: H_andnot.
split.
+ move => HP.
  apply: H1.
  by left.
+ move => HQ.
  apply: H1.
  by right.
move => Habs.
apply: Hnot0.
Admitted. (* maybe reason on the middle of the interval? *)


(* the two following lemmas (and the next two) are close copies of the above, but for any negative power instead of just (-1) *)
Lemma notInan_inversion_PowNeg prec i p:
notInan (I.power_int prec i (Z.neg p)) -> ~ contains (I.convert i) (Xreal 0) .
Proof.
move => HnotInan Hcontains0.
suff: contains (I.convert (I.power_int prec i (Z.neg p))) Xnan => [Habs|].
  move: HnotInan.
  have := (xreal_ssr_compat.contains_Xnan Habs).
  by case: (I.power_int prec i (Z.neg p)).
have -> : Xnan = Xpower_int (Xreal 0) (Z.neg p) by rewrite /= is_zero_correct_zero.
by apply: I.power_int_correct.
Qed.

Lemma notInan_inversion_PowNeg_stronger prec i p :
  notInan (I.power_int prec i (Z.neg p)) ->
  (forall x, contains (I.convert i) (Xreal x) -> x < 0) \/
  (forall x, contains (I.convert i) (Xreal x) -> x > 0).
Proof.
move => HnotInan.
suff: ~ contains (I.convert i) (Xreal 0); last first.
  by apply: notInan_inversion_PowNeg.
move => Hnot0.
set P :=  (X in X \/ _).
set Q :=  (X in _ \/ X).
suff: ~ (~ P /\ ~ Q).
move => H_andnot.
apply: Classical_Prop.NNPP. (* can we do without classical reasoning ? *)
move => H1.
apply: H_andnot.
split.
+ move => HP.
  apply: H1.
  by left.
+ move => HQ.
  apply: H1.
  by right.
move => Habs.
apply: Hnot0.
Admitted.

(* maybe this lemma is false if i1 is empty? To check *)
Lemma notInan_inversion_Div prec i1 i2 :
notInan (I.div prec i1 i2) -> ~ contains (I.convert i2) (Xreal 0) .
Proof.
move => HnotInan Hcontains0.
suff: contains (I.convert (I.div prec i1 i2)) Xnan => [Habs|].
  move: HnotInan.
  have := (xreal_ssr_compat.contains_Xnan Habs).
  by case: (I.div prec i1 i2).
(* have -> : Xnan = Xdiv (Xreal 0) by rewrite /= is_zero_correct_zero. *)
(* by apply: I.inv_correct. *)
Abort.

Lemma notInan_inversion_Div_stronger prec i1 i2 :
  notInan (I.div prec i1 i2) ->
  (forall x, contains (I.convert i2) (Xreal x) -> x < 0) \/
  (forall x, contains (I.convert i2) (Xreal x) -> x > 0).
Proof.
Abort.

Lemma is_positive_positive x :
  (is_positive x = true) -> x > 0.
move => Hpos.
have H1 :=(is_positive_spec x).
rewrite Hpos in H1.
by inversion H1.
Qed.

Lemma is_positive_negative x :
  (is_positive x = false) -> x <= 0.
move => Hnpos.
have H1 :=(is_positive_spec x).
rewrite Hnpos in H1.
by inversion H1.
Qed.

Lemma is_negative_negative x :
  (is_negative x = true) -> x < 0.
move => Hneg.
have H1 :=(is_negative_spec x).
rewrite Hneg in H1.
by inversion H1.
Qed.

Lemma is_negative_positive x :
  (is_negative x = false) -> x >= 0.
move => Hneg.
have H1 :=(is_negative_spec x).
rewrite Hneg in H1.
inversion H1.
exact: Rle_ge.
Qed.

Lemma notInan_inversion_Sqrt prec i :
  notInan (I.sqrt prec i) ->
  (forall x, contains (I.convert i) (Xreal x) -> x >= 0).
Proof.
move => HnotInan x Hcontains.
suff: contains (I.convert (I.sqrt prec i)) (Xsqrt (Xreal x)).
- rewrite /Xsqrt.
  case Hposx : (is_negative x); last first.
    move => Hcontsqrt.
    by apply: is_negative_positive.
  move => HcontXnan.
  have Habs := (xreal_ssr_compat.contains_Xnan HcontXnan).
  by rewrite (notInan_convert _ Habs) in HnotInan.
by apply: I.sqrt_correct.
Qed.

Lemma notInan_inversion_Ln prec i :
  notInan (I.ln prec i) ->
  (forall x, contains (I.convert i) (Xreal x) -> x > 0).
Proof.
move => HnotInan x Hcontains.
suff: contains (I.convert (I.ln prec i)) (Xln (Xreal x)).
- rewrite /Xln.
  case Hposx : (is_positive x).
    move => Hcontln.
    by apply: is_positive_positive.
  move => HcontXnan.
  have Habs := (xreal_ssr_compat.contains_Xnan HcontXnan).
  by rewrite (notInan_convert _ Habs) in HnotInan.
by apply: I.ln_correct.
Qed.

End notInanProperties.


(* copied from Interval_tactic *)
Lemma contains_eval prec prog bounds n :
  contains
    (I.convert
       (List.nth n
                 (A.BndValuator.eval prec prog (map A.interval_from_bp bounds))
                 I.nai))
    (Xreal (List.nth n (eval_real prog (List.map A.real_from_bp bounds)) 0)).
Proof.
set (xi := List.nth n (A.BndValuator.eval prec prog (map A.interval_from_bp bounds)) I.nai).
apply (xreal_to_real (fun x => contains (I.convert xi) x) (fun x => contains (I.convert xi) (Xreal x))).
now case (I.convert xi).
easy.
unfold xi.
replace (List.map Xreal (List.map A.real_from_bp bounds)) with (List.map A.xreal_from_bp bounds).
apply A.BndValuator.eval_correct.
clear.
induction bounds.
easy.
simpl.
rewrite IHbounds.
now case a.
Qed.

Lemma contains_eval_arg prec prog bounds n i x:
  contains (I.convert i) (Xreal x) ->
  contains
    (I.convert
       (List.nth n
                 (A.BndValuator.eval prec prog (i :: map A.interval_from_bp bounds))
                 I.nai))
    (Xreal (List.nth n (eval_real prog (x :: List.map A.real_from_bp bounds)) 0)).
Proof.
move => Hcontains.
set (xi := List.nth n (A.BndValuator.eval prec prog (i :: [seq A.interval_from_bp i | i <- bounds])%SEQ) I.nai).
apply (xreal_to_real (fun x => contains (I.convert xi) x) (fun x => contains (I.convert xi) (Xreal x))).
now case (I.convert xi).
easy.
unfold xi.
replace (List.map Xreal (x :: List.map A.real_from_bp bounds)) with
((Xreal x)::(List.map A.xreal_from_bp (bounds))).
apply A.BndValuator.eval_correct_ext => //.
clear.
rewrite /=. congr (_ :: _).
induction bounds.
easy.
simpl.
rewrite IHbounds.
now case a.
Qed.

Lemma notInan_inversion_unop prog unop i bounds n :
      notInan
        (nth I.nai
             (evalInt (rcons prog (Unary unop n)) (i :: boundsToInt bounds)) 0) ->
      notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)) n).
Proof.
move => HnotInan.
rewrite evalOpRight /eval_generic_body in HnotInan.
rewrite /notInan.
case Hnan : (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) n) => // .
rewrite nthEq Hnan /= in HnotInan.
case: unop HnotInan => //= .
by case => // .
Qed.

Lemma notXnan_inversion_unop prog unop x bounds n :
      notXnan
        (nth Xnan
             (eval_ext (rcons prog (Unary unop n)) ((Xreal x) :: map A.xreal_from_bp bounds)) 0) ->
      notXnan (nth Xnan (eval_ext prog ((Xreal x) :: map A.xreal_from_bp bounds)) n).
Proof.
move => HnotXnan.
rewrite evalOpRight /eval_generic_body in HnotXnan.
rewrite /notXnan.
set xR := (nth _ _ _).
case Hnan : xR  => // .
rewrite /xR in Hnan.
rewrite nthEq Hnan in HnotXnan.
by case: unop HnotXnan => //= .
Qed.

Lemma notXnan_inversion_binop_left prog binop x bounds n1 n2 :
      notXnan
        (nth Xnan
             (eval_ext (rcons prog (Binary binop n1 n2)) (Xreal x :: map A.xreal_from_bp bounds)%SEQ) 0) ->
      notXnan (nth Xnan (eval_ext prog (Xreal x :: map A.xreal_from_bp bounds)%SEQ) n1).
Proof.
move => HnotXnan.
rewrite evalOpRight /eval_generic_body in HnotXnan.
rewrite /notXnan.
set xR := (nth _ _ _).
case Hnan : xR => // .
rewrite /xR in Hnan.
rewrite nthEq Hnan /= in HnotXnan.
by case: binop HnotXnan => //= .
Qed.

Lemma notXnan_inversion_binop_right prog binop x bounds n1 n2 :
      notXnan
        (nth Xnan
             (eval_ext (rcons prog (Binary binop n1 n2)) (Xreal x :: map A.xreal_from_bp bounds)%SEQ) 0) ->
      notXnan (nth Xnan (eval_ext prog (Xreal x :: map A.xreal_from_bp bounds)%SEQ) n2).
Proof.
move => HnotXnan.
rewrite evalOpRight /eval_generic_body in HnotXnan.
rewrite /notXnan.
set xR := (nth _ _ _).
case Hnan : xR => // .
rewrite /xR in Hnan.
case: binop HnotXnan => //= ;
  rewrite !nthEq; rewrite Hnan /= ;
  case: (nth Xnan
           (eval_generic Xnan ext_operations prog
               (Xreal x :: [seq A.xreal_from_bp i | i <- bounds])%SEQ) n1) => //=. (* dirty hack for now *)
Qed.


Lemma notInan_inversion_binop_left prog binop i bounds i1 i2 :
      notInan
        (nth I.nai
             (evalInt (rcons prog (Binary binop i1 i2)) (i :: boundsToInt bounds)%SEQ) 0) ->
      notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i1).
Proof.
move => HnotInan.
rewrite evalOpRight /eval_generic_body in HnotInan.
rewrite /notInan.
case Hnan : (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i1) => // .
rewrite nthEq Hnan /= in HnotInan.
by case: binop HnotInan => //= .
Qed.

Lemma notInan_inversion_binop_right prog binop i bounds i1 i2 :
      notInan
        (nth I.nai
             (evalInt (rcons prog (Binary binop i1 i2)) (i :: boundsToInt bounds)%SEQ) 0) ->
      notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i2).
Proof.
move => HnotInan.
- rewrite evalOpRight /eval_generic_body in HnotInan.
  rewrite /notInan.
  case Hnan : (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i2) => // .
  rewrite !nthEq Hnan /= in HnotInan.
  by case: binop HnotInan => //= ; case: (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i1).
Qed.

(* Probably useless *)
Lemma notInan_inversion_binop prog binop i bounds i1 i2 :
      notInan
        (nth I.nai
             (evalInt (rcons prog (Binary binop i1 i2)) (i :: boundsToInt bounds)%SEQ) 0) ->
      notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i1) /\
      notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) i2).
Proof.
move => HnotInan; split.
- by apply: notInan_inversion_binop_left.
- by apply: (notInan_inversion_binop_right _ binop i bounds i1).
Qed.


Lemma continuousProg_Ind op prog bounds m (U : R -> Prop) i:
  (forall x, U x ->  contains (I.convert i) (Xreal x)) ->
  notInan (nth I.nai
          (evalInt (rcons prog op) (i::boundsToInt bounds))
          m) ->
  (forall m0 : nat,
    notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) m0) ->
    continuous_all
      U
      (fun x : R => nth 0 (eval_real prog (x :: boundsToR bounds)%SEQ) m0)) ->
   continuous_all
     U
     (fun x =>
        nth
          R0
          (eval_real
             (rcons prog op)
             (x::boundsToR bounds)) m).
Proof.
move => Hi HnotInan Hprog.
apply: continuous_all_ext.
(* first we get rid of the rcons and put the operation upfront *)
exact: (fun x => nth 0
      (eval_generic_body
         0
         real_operations
         (eval_generic
            0
            real_operations
            prog
            (x :: boundsToR bounds))
         op) m).
move => x.
by rewrite evalOpRight.

(* now we distinguish the easy case (m>0),
which is actually free from the hypothesis,
and the core of the proof, (m=0) *)
case Hm : m => [|m0]; last first.

(* easy case: m > 0 *)
- apply: continuous_all_ext.
    exact:
      (fun x : R =>
         nth 0
             (eval_generic
                0
                real_operations
                prog
                (x :: boundsToR bounds)%SEQ)
             m0).
    move => x.
    by rewrite -nth_behead.
  apply: Hprog.
  by rewrite Hm evalOpRight /= in HnotInan.
(* now the meat of the proof: m=0 *)
(* first get the operation up front *)

case Hop : op => [unop n| binop n1 n2].
- apply: continuous_all_ext.
  exact:
    (fun x =>
       (unary
          real_operations
          unop
          (nth
             0
             (eval_real prog (x :: boundsToR bounds)%SEQ)
             n)
       )
    ).
  move => x.
  by rewrite /= nthEq.
  apply: domain_correct.
    apply: Hprog.
      apply: (notInan_inversion_unop _ unop).
      by rewrite -Hop -Hm. Print domain.
    (* rewrite Hop Hm evalIntOpRight /= in HnotInan. *)
  case Hunop: unop => [|||||||||||k]//= . (* and now 5 cases to treat *)
  (* inv *)
  + rewrite Hop Hm evalOpRight Hunop /= in HnotInan.
    have noZero := (notInan_inversion_Inv_stronger _ _ HnotInan).
    move : noZero => [Hleft|Hright].
    * left; move => x HUx; apply: Hleft.
      rewrite /evalInt -nthEq /boundsToR /boundsToInt.
      by apply: contains_eval_arg; apply: Hi.
    * right; move => x HUx; apply: Hright.
      rewrite /evalInt -nthEq /boundsToR /boundsToInt.
      by apply: contains_eval_arg; apply: Hi.
  (* sqrt *)
  + rewrite Hop Hm evalOpRight Hunop /= in HnotInan.
  have NonNeg := (notInan_inversion_Sqrt _ _ HnotInan).
  move => x HUx; apply: NonNeg.
  rewrite /evalInt -nthEq /boundsToR /boundsToInt.
  by apply: contains_eval_arg; apply: Hi.
  (* Tan *)
  + admit.
  (* Ln *)
  + rewrite Hop Hm evalOpRight Hunop /= in HnotInan.
  have HPositive := (notInan_inversion_Ln _ _ HnotInan).
  move => x HUx; apply: HPositive.
  rewrite /evalInt -nthEq /boundsToR /boundsToInt.
  by apply: contains_eval_arg; apply: Hi.
  (* power *)
  + case: k Hunop => // p Hunop.
    rewrite Hop Hm evalOpRight Hunop /= in HnotInan.
    have noZero := (notInan_inversion_PowNeg_stronger _ _ p HnotInan).
    move : noZero => [Hleft|Hright].
    * left; move => x HUx; apply: Hleft.
      rewrite /evalInt -nthEq /boundsToR /boundsToInt.
      by apply: contains_eval_arg; apply: Hi.
    * right; move => x HUx; apply: Hright.
      rewrite /evalInt -nthEq /boundsToR /boundsToInt.
      by apply: contains_eval_arg; apply: Hi.

(* this little intermission is for ssreflect compatibility reasons *)
have HprogBis :
  forall m0 : nat,
    notInan (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) m0) ->
    continuous_all U
                   (fun x : R =>
                      List.nth m0 (eval_real prog (x :: boundsToR bounds)%SEQ) 0).
move => m0 HnotInan2.
apply: continuous_all_ext.
exact: (fun x : R =>
             nth 0 (eval_real prog (x :: boundsToR bounds)%SEQ) m0).
move => x.
by rewrite /= -nthEq.
by apply: Hprog.

case Hbinop : binop.
 - apply: continuous_all_ext.
   exact:
     (fun x =>
        List.nth
          n1
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0 +
        List.nth
          n2
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0).
     by move => x; rewrite /=.
   apply: continuous_all_Rplus; apply: HprogBis.
   apply: (notInan_inversion_binop_left prog binop i bounds n1 n2).
     by rewrite -Hm -Hop.
   apply: (notInan_inversion_binop_right prog binop i bounds n1 n2).
     by rewrite -Hm -Hop.
 - apply: continuous_all_ext.
   exact:
     (fun x =>
        List.nth
          n1
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0 -
        List.nth
          n2
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0).
     by move => x; rewrite /=.
   apply: continuous_all_Rsub; apply: HprogBis.
   apply: (notInan_inversion_binop_left prog binop i bounds n1 n2).
     by rewrite -Hm -Hop.
   apply: (notInan_inversion_binop_right prog binop i bounds n1 n2).
     by rewrite -Hm -Hop.
 - apply: continuous_all_ext.
   exact:
     (fun x =>
        List.nth
          n1
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0 *
        List.nth
          n2
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0).
     by move => x; rewrite /=.
   apply: continuous_all_Rmult; apply: HprogBis.
   apply: (notInan_inversion_binop_left prog binop i bounds n1 n2).
     by rewrite -Hm -Hop.
   apply: (notInan_inversion_binop_right prog binop i bounds n1 n2).
     by rewrite -Hm -Hop.
 - apply: continuous_all_ext.
   exact:
     (fun x =>
        List.nth
          n1
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0 /
        List.nth
          n2
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0).
     by move => x; rewrite /=.
   apply: continuous_all_Rdiv; try apply: HprogBis.
   (* rewrite Hop Hm evalIntOpRight Hbinop /= in HnotInan. *)
   apply: (notInan_inversion_binop_left prog binop i bounds n1 n2).
     by rewrite -Hm -Hop.
   apply: (notInan_inversion_binop_right prog binop i bounds n1 n2).
     by rewrite -Hm -Hop.
   (* have noZero := (notInan_inversion_Div_stronger _ _ HnotInan). *)
   (*  move : noZero => [Hleft|Hright]. *)
   (*  * left; move => x HUx; apply: Hleft. *)
   (*    rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
   (*    by apply: contains_eval_arg; apply: Hi. *)
   (*  * right; move => x HUx; apply: Hright. *)
   (*    rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
   (*    by apply: contains_eval_arg; apply: Hi. *)
   admit.
  (* the last commented sequence will work if lemma *)
  (* notInan_inversion_Div_stronger is true*)
Qed.

Lemma continuousProg prog bounds (m : nat) (U : R -> Prop) i:
  (forall x, U x ->  contains (I.convert i) (Xreal x)) ->
  (notInan (nth I.nai
          (evalInt prog (i::boundsToInt bounds))
          m)) ->
  continuous_all
    U
    (fun x =>
       nth
         R0
         (eval_real
            prog
            (x::boundsToR bounds)) m).
Proof.
move => Hcontains.
elim/last_ind: prog m => [m0 HnotInan| prog op HI m0 HnotInan].
- rewrite /= .
  case: m0 HnotInan => [HnotInan|m1 HnotInan].
  + apply: continuous_all_ext.
    exact: (fun x => x).
    by move => x /= .
    by apply: continuous_all_id.
  + apply: (continuous_all_ext _ (fun x => nth 0 (boundsToR bounds) m1)).
    by move => x /= .
    move => x H1.
    by apply: continuous_const.
- apply: (continuousProg_Ind).
  exact: i.
  exact: Hcontains.
  exact: HnotInan.
  move => m1.
  move => HnotInan_m1.
  by apply: HI.
Qed.

Lemma integrableProg prog bounds m a b i:
  (forall x, Rmin a b <= x <= Rmax a b ->  contains (I.convert i) (Xreal x)) ->
  (notInan (nth I.nai
          (evalInt prog (i::boundsToInt bounds))
          m )) ->
  ex_RInt
    (fun x =>
       nth
         R0
         (eval_real
            prog
            (x::boundsToR bounds)) m)
    a
    b.
Proof.
move => Hcontains HnotInan.
apply: ex_RInt_continuous.
apply: (continuousProg prog bounds m _ i) => //.
Qed.


Lemma continuousProg2 prog bounds (m : nat) (U : R -> Prop) i:
  (forall x, U x ->  contains (I.convert i) (Xreal x)) ->
  (forall x,
     U x ->
     notXnan (nth Xnan
          (eval_ext prog ((Xreal x)::map A.xreal_from_bp bounds))
          m)) ->
  continuous_all
    U
    (fun x =>
       nth
         R0
         (eval_real
            prog
            (x::boundsToR bounds)) m).
Proof.
move => Hcontains.
generalize m.
elim/last_ind: prog => [m0 HnotXnan |prog op HI m0 Hm0].
- rewrite /= .
  case Hm0 : m0 => [|m1] /= .
  + by apply:(continuous_all_ext _ (fun x => x)) => x /=; try apply: continuous_all_id.
  + by apply: continuous_all_const.
-
  case Hm : m0 => [|m1]; last first.

  + apply: continuous_all_ext.
    exact:
      (fun x : R =>
         nth 0
             (eval_generic
                0
                real_operations
                prog
                (x :: boundsToR bounds)%SEQ)
             m1).
    move => x.
    by rewrite evalOpRight /=.
    apply: HI => x HUx.
    move: (Hm0 x HUx).
    by rewrite Hm evalOpRight /= .
    (* now m = 0 *)
case Hop : op => [unop n| binop n1 n2].
- apply: continuous_all_ext.
  exact:
    (fun x =>
       (unary
          real_operations
          unop
          (nth
             0
             (eval_real prog (x :: boundsToR bounds)%SEQ)
             n)
       )
    ).
  move => x.
  by rewrite evalOpRight /= nthEq.
  apply: domain_correct.
    apply: HI.
    move => x HUx.
    apply: (notXnan_inversion_unop _ unop).
    by move: (Hm0 x HUx); rewrite Hop Hm.
    (* rewrite Hop Hm evalIntOpRight /= in HnotInan. *)
  case Hunop: unop => [|||||||||||k]//= . (* and now 5 cases to treat *)
  (* inv *)
  +
    admit.
    (* rewrite Hop Hm evalOpRight Hunop /= in HnotInan. *)
    (* have noZero := (notInan_inversion_Inv_stronger _ _ HnotInan). *)
    (* move : noZero => [Hleft|Hright]. *)
    (* * left; move => x HUx; apply: Hleft. *)
    (*   rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
    (*   by apply: contains_eval_arg; apply: Hi. *)
    (* * right; move => x HUx; apply: Hright. *)
    (*   rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
    (*   by apply: contains_eval_arg; apply: Hi. *)
  (* sqrt *)
  + admit.
  (*   rewrite Hop Hm evalOpRight Hunop /= in HnotInan. *)
  (* have NonNeg := (notInan_inversion_Sqrt _ _ HnotInan). *)
  (* move => x HUx; apply: NonNeg. *)
  (* rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
  (* by apply: contains_eval_arg; apply: Hi. *)
  (* Tan *)
  + admit.
  (* Ln *)
  + admit.
    (* rewrite Hop Hm evalOpRight Hunop /= in HnotInan. *)
  (* have HPositive := (notInan_inversion_Ln _ _ HnotInan). *)
  (* move => x HUx; apply: HPositive. *)
  (* rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
  (* by apply: contains_eval_arg; apply: Hi. *)
  (* power *)
  + admit.
    (* case: k Hunop => // p Hunop. *)
    (* rewrite Hop Hm evalOpRight Hunop /= in HnotInan. *)
    (* have noZero := (notInan_inversion_PowNeg_stronger _ _ p HnotInan). *)
    (* move : noZero => [Hleft|Hright]. *)
    (* * left; move => x HUx; apply: Hleft. *)
    (*   rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
    (*   by apply: contains_eval_arg; apply: Hi. *)
    (* * right; move => x HUx; apply: Hright. *)
    (*   rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
    (*   by apply: contains_eval_arg; apply: Hi. *)
(* this little intermission is for ssreflect compatibility reasons *)
have HprogBis :
  forall m0 : nat,
    (forall x, U x ->
               notXnan (nth Xnan (eval_ext prog ((Xreal x) :: map A.xreal_from_bp bounds)%SEQ) m0)) ->
    continuous_all U
                   (fun x : R =>
                      List.nth m0 (eval_real prog (x :: boundsToR bounds)%SEQ) 0).
move => m1 HnotXnan.
apply: continuous_all_ext.
exact: (fun x : R =>
             nth 0 (eval_real prog (x :: boundsToR bounds)%SEQ) m1).
move => x1.
by rewrite /= -nthEq.
by apply: HI.

case Hbinop : binop.
 - apply: continuous_all_ext.
   exact:
     (fun x =>
        List.nth
          n1
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0 +
        List.nth
          n2
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0).
     by move => x; rewrite evalOpRight /=.
   apply: continuous_all_Rplus; apply: HprogBis.
   move => x HUx.
   apply: (notXnan_inversion_binop_left prog binop _ bounds n1 n2).
     by rewrite evalOpRight -Hm -Hop; move: (Hm0 x HUx); rewrite evalOpRight.
   move => x HUx.
   apply: (notXnan_inversion_binop_right prog binop _ bounds n1 n2).
     by rewrite evalOpRight -Hm -Hop; move: (Hm0 x HUx); rewrite evalOpRight.
 - apply: continuous_all_ext.
   exact:
     (fun x =>
        List.nth
          n1
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0 -
        List.nth
          n2
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0).
     by move => x; rewrite evalOpRight /=.
   apply: continuous_all_Rsub; apply: HprogBis.
   move => x HUx.
   apply: (notXnan_inversion_binop_left prog binop _ bounds n1 n2).
     by rewrite evalOpRight -Hm -Hop; move: (Hm0 x HUx); rewrite evalOpRight.
   move => x HUx.
   apply: (notXnan_inversion_binop_right prog binop _ bounds n1 n2).
     by rewrite evalOpRight -Hm -Hop; move: (Hm0 x HUx); rewrite evalOpRight.
 - apply: continuous_all_ext.
   exact:
     (fun x =>
        List.nth
          n1
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0 *
        List.nth
          n2
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0).
     by move => x; rewrite evalOpRight /=.
   apply: continuous_all_Rmult; apply: HprogBis.
   move => x HUx.
   apply: (notXnan_inversion_binop_left prog binop _ bounds n1 n2).
     by rewrite evalOpRight -Hm -Hop; move: (Hm0 x HUx); rewrite evalOpRight.
   move => x HUx.
   apply: (notXnan_inversion_binop_right prog binop _ bounds n1 n2).
     by rewrite evalOpRight -Hm -Hop; move: (Hm0 x HUx); rewrite evalOpRight.
 - apply: continuous_all_ext.
   exact:
     (fun x =>
        List.nth
          n1
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0 /
        List.nth
          n2
          (eval_generic 0 real_operations prog (x :: boundsToR bounds)%SEQ) 0).
     by move => x; rewrite evalOpRight /=.
   apply: continuous_all_Rdiv; try apply: HprogBis.
   (* rewrite Hop Hm evalIntOpRight Hbinop /= in HnotInan. *)
   move => x HUx.
   apply: (notXnan_inversion_binop_left prog binop _ bounds n1 n2).
     by rewrite evalOpRight -Hm -Hop; move: (Hm0 x HUx); rewrite evalOpRight.
   move => x HUx.
   apply: (notXnan_inversion_binop_right prog binop _ bounds n1 n2).
     by rewrite evalOpRight -Hm -Hop; move: (Hm0 x HUx); rewrite evalOpRight.
   (* have noZero := (notInan_inversion_Div_stronger _ _ HnotInan). *)
   (*  move : noZero => [Hleft|Hright]. *)
   (*  * left; move => x HUx; apply: Hleft. *)
   (*    rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
   (*    by apply: contains_eval_arg; apply: Hi. *)
   (*  * right; move => x HUx; apply: Hright. *)
   (*    rewrite /evalInt -nthEq /boundsToR /boundsToInt. *)
   (*    by apply: contains_eval_arg; apply: Hi. *)
   admit.
  (* the last commented sequence will work if lemma *)
  (* notInan_inversion_Div_stronger is true*)
Qed.

(* we ensure that we get the former result by using the new one *)
Lemma continuousProgAsAConsequence prog bounds (m : nat) (U : R -> Prop) i:
  (forall x, U x ->  contains (I.convert i) (Xreal x)) ->
  (notInan (nth I.nai
          (evalInt prog (i::boundsToInt bounds))
          m)) ->
  continuous_all
    U
    (fun x =>
       nth
         R0
         (eval_real
            prog
            (x::boundsToR bounds)) m).
Proof.
move => Hcontains HnotInan.
apply: (continuousProg2 _ _ _ _ i) => // x HUx.
rewrite /notXnan.
set xR := nth _ _ _.
case HxR : xR => //= .
suff: (I.convert (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) m) = Inan).
  move => Habs.
  rewrite /notInan in HnotInan.
  case Hi : (nth I.nai (evalInt prog (i :: boundsToInt bounds)%SEQ) m) Habs => //= .
  by rewrite Hi in HnotInan.
apply: xreal_ssr_compat.contains_Xnan.
rewrite -HxR /xR.
rewrite -!nthEq -!mapEq /evalInt.
by apply: A.BndValuator.eval_correct_ext; apply: Hcontains.
Qed.

End Preliminary.



End Integrability.
End Integrability.