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
Require Import Interval_integral.
Require Import Interval_bisect.

Require Import ssreflect ssrnat.

Module IntervalTactic (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.
Module A := IntervalAlgos I.

Section Integrability.

Lemma ex_RInt_Id a b : ex_RInt (fun x => x) a b.
Proof.
Admitted. (* can't find a useful theorem *)

Section revEq.
Require Import seq.

Lemma revEq : forall A l, @List.rev A l = rev l.
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

(* Lemma continuous_on_comp {U V W : UniformSpace} D E (f : U -> V) (g : V -> W) : *)
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
Definition continuous_all (D : R -> Prop) (f : R -> R) := forall x, D x -> continuous f x.

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

Lemma continuous_on_Ropp D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => - (f x)).
Proof.
Admitted.

Lemma continuous_on_Rabs D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => Rabs (f x)).
Proof.
Admitted.

Lemma continuous_on_Rinv D (f : R -> R) :
  continuous_all D f ->
  (forall x, D x -> f x > 0) \/ (forall x, D x -> f x < 0) ->
  continuous_all D (fun x => / (f x)).
Proof.
Admitted.

Lemma continuous_on_Rmult D (f : R -> R) (g : R -> R) :
  continuous_all D f ->
  continuous_all D g ->
  continuous_all D (fun x => f x * g x).
Proof.
Admitted.

Lemma continuous_on_sqrt D (f : R -> R) :
  continuous_all D f ->
  (forall x, D x -> f x > 0) ->
  continuous_all D (fun x => sqrt (f x)).
Proof.
Admitted.

Lemma continuous_on_cos D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => cos (f x)).
Proof.
Admitted.


Lemma continuous_on_sin D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => sin (f x)).
Proof.
Admitted.

Lemma continuous_on_tan D (f : R -> R) :
  continuous_all D f ->
  (forall x, D x -> (f x > - Pi / 2 /\ f x < Pi / 2)) ->
  continuous_all D (fun x => tan (f x)).
Proof.
Admitted.

Lemma continuous_on_atan D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => atan (f x)).
Proof.
Admitted.

Lemma continuous_on_exp D (f : R -> R) :
  continuous_all D f ->
  continuous_all D (fun x => exp (f x)).
Proof.
Admitted.


Lemma continuous_on_ln D (f : R -> R) :
  continuous_all D f ->
  (forall x, D x -> f x > 0) ->
  continuous_all D (fun x => ln (f x)).
Proof.
Admitted.

Lemma continuous_on_powerRZ D (f : R -> R) n :
  continuous_all D f ->
  (match n with
                       | Zpos m => True
                       | Z0 => True
                       | Zneg m  => (forall x, D x -> x < 0) \/ (forall x, D x -> x > 0)
                     end
                    ) ->
  continuous_all D (fun x => powerRZ (f x) n).
Proof.
Admitted.


(* We need to capture preconditions for (unop f) to be continuous *)
Definition domain unop g (P : R -> Prop) :=
  match unop with
    | Neg => True
    | Abs => True
    | Inv => (forall x, P x -> g x < 0) \/ (forall x, P x -> g x > 0)
    | Sqr => True
    | Sqrt => (forall x, P x -> g x > 0)
    | Cos => True
    | Sin => True
    | Tan => forall x, P x -> (g x > - Pi / 2 /\ g x < Pi / 2)
    | Atan => True
    | Exp => True
    | Ln => (forall x, P x -> g x > 0)
    | PowerInt n => (match n with
                       | Zpos m => True
                       | Z0 => True
                       | Zneg m  => (forall x, P x -> x < 0) \/ (forall x, P x -> x > 0)
                     end
                    )
  end.

Lemma domain_correct unop D g: continuous_all D g -> (domain unop g D) -> continuous_all D (fun x => unary real_operations unop (g x)).
Proof.
move => Hgcont.
case Hunop: unop => HD; rewrite /domain in HD.
(* and now 12 cases, one for each unary operator *)
- by apply: continuous_on_Ropp.
- by apply: continuous_on_Rabs.
(* - case: HD => [Hpos|Hneg]. *)
-  apply: continuous_on_Rinv => //; case: HD.
     by right.
   by left.
- by apply: continuous_on_Rmult => //.
- by apply: continuous_on_sqrt => //.
- by apply: continuous_on_cos => //.
- by apply: continuous_on_sin => //.
- by apply: continuous_on_tan => //.
- by apply: continuous_on_atan => // .
- by apply: continuous_on_exp => //.
- by apply: continuous_on_ln => //.
- by apply: continuous_on_powerRZ => // .
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

Lemma evalRealOpRight op prog bounds m x : (* raw form, will probably change *)
  nth R0 (eval_real (rcons prog op) (x::boundsToR bounds)) m =
  nth 0
      (eval_generic_body
         0
         real_operations
         (eval_generic 0 real_operations prog (x :: boundsToR bounds)) op) m.
Proof.
by rewrite /eval_real rev_formula revEq rev_rcons /= rev_formula revEq.
Qed.

Definition interval_operations := (A.BndValuator.operations prec).

Lemma evalIntOpRight op prog bounds m x : 
  nth I.nai (evalInt (rcons prog op) (x::boundsToInt bounds)) m =
  nth I.nai
      (eval_generic_body
         I.nai
         interval_operations
         (eval_generic I.nai interval_operations prog (x :: boundsToInt bounds)) op) m.
Proof.
by rewrite /evalInt /A.BndValuator.eval rev_formula revEq rev_rcons /= rev_formula revEq.
Qed.


Lemma evalRealOpRightFold op prog bounds m x : (* raw form, will probably change *)
  nth R0 (eval_real (rcons prog op) (x::boundsToR bounds)) m =
  nth 0
      (eval_generic_body
         0
         real_operations
         (fold_right
            (fun (y : term) (x0 : seq R) =>
               eval_generic_body 0 real_operations x0 y)
            (x :: boundsToR bounds) (rev prog)) op) m.
Proof.
by rewrite /eval_real rev_formula revEq rev_rcons /=.
Qed.

Lemma unNamed1 unop n prog a b bounds m:
   (forall m, ex_RInt
     (fun x => nth R0 (eval_real prog (x::boundsToR bounds)) m )
     a
     b)
   ->
   ex_RInt
     (fun x => nth R0 (eval_real (rcons prog (Unary unop n)) (x::boundsToR bounds)) m)
     a
     b.
Proof.
move => Hprog.
apply: ex_RInt_ext.
(* first we get rid of the rcons and put the operation upfront *)
exact: (fun x => nth 0
      (eval_generic_body
         0
         real_operations
         (eval_generic 0 real_operations (prog) (x :: boundsToR bounds)) (Unary unop n)) m).
move => x _.
by rewrite evalRealOpRight.

(* now we distinguish the easy case (m>0),
which is actually free from the hypothesis,
and the core of the proof, (m=0) *)
case Hm : m => [|m0]; last first.

(* easy case: m > 0 *)
- apply: ex_RInt_ext.
    exact:
      (fun x : R =>
         nth 0
             (eval_generic
                0
                real_operations
                prog
                (x :: boundsToR bounds)%SEQ)
             m0).
    move => x Huseless.
    by rewrite -nth_behead.
  by apply: Hprog.

(* now the meat of the proof: m=0 *)
(* first get the operation up front *)
- apply: ex_RInt_ext.
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
  move => x _.
  by rewrite /= nthEq.

  case Hunop: unop => /=. (* and now 12 cases to treat *)
  + by apply: ex_RInt_opp; apply: Hprog.
  + by apply: ex_RInt_Rabs; apply: Hprog.
  + admit. (* false here, we need to add some hypotheses ("0 \notin I")*)
  + by apply: ex_RInt_Rmult; apply: Hprog.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.

(* Lemma continuous_on_comp :  *)
(*   forall (U V W : UniformSpace) (f : U -> V) (g : V -> W), *)
(* continuous_on U f -> continuous_on V g -> continuous_on U (fun x0 : U => g (f x0)). *)

Lemma continuousProg unop n prog bounds m (U : R -> Prop) i:
  (forall x, U x ->  contains (I.convert i) (Xreal x)) ->
  notInan (nth I.nai
          (evalInt (rcons prog (Unary unop n)) (i::boundsToInt bounds))
          m) ->
   (forall m, continuous_all U
     (fun x => nth R0 (eval_real prog (x::boundsToR bounds)) m ))
   ->
   continuous_all U
     (fun x => nth R0 (eval_real (rcons prog (Unary unop n)) (x::boundsToR bounds)) m).
Proof.
move => Hi HnotInan Hprog.
apply: continuous_all_ext.
(* first we get rid of the rcons and put the operation upfront *)
exact: (fun x => nth 0
      (eval_generic_body
         0
         real_operations
         (eval_generic 0 real_operations (prog) (x :: boundsToR bounds)) (Unary unop n)) m).
move => x.
by rewrite evalRealOpRight.

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
  by apply: Hprog.

(* now the meat of the proof: m=0 *)
(* first get the operation up front *)
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
    by apply: Hprog.
  case Hunop: unop => //= . (* and now 5 cases to treat *)
  + have lemma : 
      forall x : R, 
        (nth 0 (eval_real prog (x :: boundsToR bounds)%SEQ) n = 0) -> 
        I.convert (nth I.nai (evalInt (rcons prog (Unary unop n)) (i :: boundsToInt bounds)%SEQ) 0) = Inan.
    * move => x H0.
      rewrite evalIntOpRight Hunop /= .
      apply: xreal_ssr_compat.contains_Xnan.
      suff: contains 
            (I.convert 
               (List.nth n
                         (eval_generic 
                            I.nai 
                            interval_operations 
                            prog
                            (i :: boundsToInt bounds)%SEQ) I.nai)) 
            (Xreal 0).
        move => Hcontains0.
        have -> : Xnan = Xinv (Xreal 0) by rewrite /= is_zero_correct_zero.
        apply: I.inv_correct.
        by apply: Hcontains0.
      have -> : Xreal 0 = nth Xnan (eval_ext prog (Xreal x :: (map Xreal (boundsToR bounds)))) n by admit.
      admit.
  (* almost there, but some technical details must be sorted out for the 
     present goal to be provable *) 
    admit.
  + admit.
  + admit.
  + admit.
  + admit.
Qed.


End Preliminary.

Lemma eval_implies_integrable prog a b boundsa boundsb proga progb bounds i m:
  let iA := (boundsToInt boundsa) in
  let iB := (boundsToInt boundsb) in
  let ia := nth 0 (evalInt proga iA) I.nai in
  let ib := nth 0 (evalInt progb iB) I.nai in
  let f := (fun x => nth m (eval_real prog (x::boundsToR bounds)) R0) in
  let fi :=
      nth m
          (evalInt prog (i::boundsToInt bounds))
          I.nai
  in
  notInan fi ->
  contains (I.convert i) (Xreal a) ->
  contains (I.convert i) (Xreal b) ->
  ex_RInt f a b.
Proof.
Require Import seq. (* here because it breaks the lemma statement *)
move: m.
elim/last_ind: prog => [m iA iB ia ib f fi Hreasonable Hconta Hcontb |
 lprog a0 Ha0l m iA iB  ia ib f fi Hreasonable Hconta Hcontb].
- case Hm : m Hreasonable => [| m0] Hreasonable.
  + apply: (ex_RInt_ext (fun x => x)) => [x H|].
      by rewrite /f Hm /= .
    exact: ex_RInt_Id.
  + apply: (ex_RInt_ext (fun _ => (List.nth m0 (List.map A.real_from_bp bounds) 0))).
    move => x _.
    by rewrite /f Hm /= .
    exact: ex_RInt_const.
- rewrite /f /eval_real.
  set g :=
    (fun x : R =>
       List.nth m
                (fold_right
                   (fun (y : term) (x0 : seq R) =>
                      eval_generic_body 0 real_operations x0 y)
                   (x :: List.map A.real_from_bp bounds)
                   (List.rev (rcons lprog a0))) 0).
  apply: (ex_RInt_ext g).
    by move => x _; rewrite /g rev_formula.
rewrite /g revEq rev_rcons.
  case Ha0 : a0 Hreasonable Hconta Hcontb => [unop n| binop m1 n] Hreasonable Hconta Hcontb.
  case Hm: m.
  +

(*   + case Hunop : unop Ha0 => Ha0 /= . *)
(*     * case Hm: m => [| n0 ]. *)
(*       apply: ex_RInt_opp.  *)
(*       apply: (ex_RInt_ext (fun x : R => *)
(*            List.nth n *)
(*              (eval_real lprog (x :: List.map A.real_from_bp bounds)%SEQ) 0)).  *)
(*         move => x _. *)
(*         by rewrite /eval_real rev_formula revEq. *)
(*         apply: Ha0l => // . *)
(*         move: Hreasonable. *)
(*         rewrite /fi /evalInt /A.BndValuator.eval. *)
(*         rewrite rev_formula revEq rev_rcons. *)
(*         rewrite Ha0 Hm /= . *)
(*         set i0 := (X in I.neg X). *)
(*         case Hi0 : i0 => [| lb ub] //= _. *)
(*         have -> : List.nth n *)
(*        (eval_generic I.nai (A.BndValuator.operations prec) lprog *)
(*           (i :: List.map A.interval_from_bp bounds)%SEQ) I.nai = i0. *)
(*         by rewrite /i0 rev_formula revEq. *)
(*         by rewrite Hi0. *)
(*         (* move : (Ha0l n0). *) *)

(*         apply: (ex_RInt_ext (fun x : R => *)
(*           List.nth n0 (eval_real lprog (x :: boundsToR bounds)%SEQ) 0)). *)
(*         move => x _. *)
(*         by rewrite /eval_real rev_formula revEq. *)
(*         apply: (Ha0l n0) => // . *)
(*         suff: notInan *)
(*                 (nth I.nai *)
(*                      (fold_right *)
(*                         (fun (y : term) (x : seq I.type) => *)
(*                            eval_generic_body I.nai (A.BndValuator.operations prec) x y) *)
(*                         (i :: boundsToInt bounds) (rev lprog)) n0). *)
(*         by rewrite nthEq /evalInt /A.BndValuator.eval rev_formula revEq. *)
(*         move: Hreasonable. *)
(*         rewrite /fi Hm /evalInt /A.BndValuator.eval.  *)
(*         rewrite rev_formula revEq rev_rcons Ha0.  *)
(*         rewrite nthEq /=. *)
(*         by rewrite /fold_right /eval_generic_body. *)




































(* Require Import seq. (* here because it breaks the lemma statement *) *)
(* move: m. *)
(* elim/last_ind: prog => [m iA iB ia ib f fi Hreasonable Hconta Hcontb | *)
(*  lprog a0 Ha0l m iA iB  ia ib f fi Hreasonable Hconta Hcontb]. *)
(* - case Hm : m Hreasonable => [| m0] Hreasonable. *)
(*   + apply: (ex_RInt_ext (fun x => x)) => [x H|]. *)
(*       by rewrite /f Hm /= . *)
(*     exact: ex_RInt_Id. *)
(*   + apply: (ex_RInt_ext (fun _ => (List.nth m0 (List.map A.real_from_bp bounds) 0))). *)
(*     move => x _.  *)
(*     by rewrite /f Hm /= . *)
(*     exact: ex_RInt_const. *)
(* - rewrite /f /eval_real. *)
(*   set g :=  *)
(*     (fun x : R => *)
(*        List.nth m *)
(*                 (fold_right *)
(*                    (fun (y : term) (x0 : seq R) => *)
(*                       eval_generic_body 0 real_operations x0 y) *)
(*                    (x :: List.map A.real_from_bp bounds)  *)
(*                    (List.rev (rcons lprog a0))) 0). *)
(*   apply: (ex_RInt_ext g). *)
(*     by move => x _; rewrite /g rev_formula. *)
(* rewrite /g revEq rev_rcons. *)
(*   case Ha0 : a0 Hreasonable Hconta Hcontb => [unop n| binop m1 n] Hreasonable Hconta Hcontb. *)
(*   (* case Hm: m. *) *)
(*   + case Hunop : unop Ha0 => Ha0 /= . *)
(*     * case Hm: m => [| n0 ]. *)
(*       apply: ex_RInt_opp.  *)
(*       apply: (ex_RInt_ext (fun x : R => *)
(*            List.nth n *)
(*              (eval_real lprog (x :: List.map A.real_from_bp bounds)%SEQ) 0)).  *)
(*         move => x _. *)
(*         by rewrite /eval_real rev_formula revEq. *)
(*         apply: Ha0l => // . *)
(*         move: Hreasonable. *)
(*         rewrite /fi /evalInt /A.BndValuator.eval. *)
(*         rewrite rev_formula revEq rev_rcons. *)
(*         rewrite Ha0 Hm /= . *)
(*         set i0 := (X in I.neg X). *)
(*         case Hi0 : i0 => [| lb ub] //= _. *)
(*         have -> : List.nth n *)
(*        (eval_generic I.nai (A.BndValuator.operations prec) lprog *)
(*           (i :: List.map A.interval_from_bp bounds)%SEQ) I.nai = i0. *)
(*         by rewrite /i0 rev_formula revEq. *)
(*         by rewrite Hi0. *)
(*         (* move : (Ha0l n0). *) *)

(*         apply: (ex_RInt_ext (fun x : R => *)
(*           List.nth n0 (eval_real lprog (x :: boundsToR bounds)%SEQ) 0)). *)
(*         move => x _. *)
(*         by rewrite /eval_real rev_formula revEq. *)
(*         apply: (Ha0l n0) => // . *)
(*         suff: notInan *)
(*                 (nth I.nai *)
(*                      (fold_right *)
(*                         (fun (y : term) (x : seq I.type) => *)
(*                            eval_generic_body I.nai (A.BndValuator.operations prec) x y) *)
(*                         (i :: boundsToInt bounds) (rev lprog)) n0). *)
(*         by rewrite nthEq /evalInt /A.BndValuator.eval rev_formula revEq. *)
(*         move: Hreasonable. *)
(*         rewrite /fi Hm /evalInt /A.BndValuator.eval.  *)
(*         rewrite rev_formula revEq rev_rcons Ha0.  *)
(*         rewrite nthEq /=. *)
(*         by rewrite /fold_right /eval_generic_body. *)


(*     * admit. *)
(*     * admit. *)
(*     * admit. *)
(*     * admit. *)
(*     * admit. *)
(*     * admit. *)
(*     * admit. *)
(*     * admit. *)
(*     * admit. *)
(*     * admit. *)
(*     * admit. *)



(* Qed. *)

(* case Ha0 : a0. *)
(* case. *)
(* Search _ RInt. *)
(* Search _ ex_RInt (fun _ => _). *)

(* About eval_inductive_prop. *)
(* Search _ term eval_real. *)
(* Check eval_generic. *)
(* Search _ term. *)
Admitted.

End Integrability.
