From Coq Require Import List Reals.
Require Import Tactic.

Open Scope R_scope.

Import Xreal Interval Tree Reify Prog.
Import Tactic.Private.
Import IT.Private.IT1.

Module F := SFBI2.

Definition plot (f : R -> R) (u d : R) (l : list I.type) :=
  forall i x, (u + d * INR i <= x <= u + d * INR (S i))%R ->
  contains (I.convert (nth i l I.nai)) (Xreal (f x)).

Lemma plot_ext :
  forall f g u d l,
  (forall x, f x = g x) ->
  plot f u d l -> plot g u d l.
Proof.
intros f g u d l H K i x Hx.
specialize (K i x Hx).
now rewrite <- H.
Qed.

Fixpoint eval_plot_aux prec (gi : I.type -> I.type -> I.type) (check : I.type -> bool) (ui di zi2 : I.type) (fi : I.type -> I.type) (i : nat) (mz xz rz : Z) (acc : list I.type) : list I.type :=
  match i with
  | O => acc
  | S i =>
    let xz' := Z.pred xz in
    let xi1 := I.add prec ui (I.mul prec di (I.fromZ prec xz')) in
    let xi2 := I.add prec ui (I.mul prec di (I.fromZ prec xz)) in
    let xi := I.join xi1 xi2 in
    let zi1 := fi xi1 in
    let yi := fi xi in
    let c := andb
      (orb (check (I.meet yi (I.lower_extent zi1))) (check (I.meet yi (I.upper_extent zi1))))
      (orb (check (I.meet yi (I.lower_extent zi2))) (check (I.meet yi (I.upper_extent zi2)))) in
    let yizi :=
      if c then (yi, zi1)
      else let fi := gi xi in (fi xi, fi xi1) in
    let mz' :=
      if Z.eqb mz xz' then (mz - Z.div2 (3 * rz))%Z
      else if c then mz
      else (xz' - 1 - Z.div2 rz)%Z in
    let mz' :=
      if Z.ltb mz' 0%Z then 0%Z else mz' in
    let firz :=
      if Z.eqb mz mz' then (fi, rz)
      else
        let xi0 := I.add prec ui (I.mul prec di (I.fromZ prec mz')) in
        (gi (I.join xi0 xi1), (xz' - mz'))%Z in
    let acc := fst yizi :: acc in
    eval_plot_aux prec gi check ui di (snd yizi) (fst firz) i mz' xz' (snd firz) acc
  end.

Definition eval_plot prec deg check hyps pf pu pv cf cu cv nb :=
  let hyps := R.merge_hyps prec hyps in
  let ui :=
    let bounds := hyps ++ map (T.eval_bnd prec) cu in
    nth 0 (A.BndValuator.eval prec pu bounds) I.nai in
  let vi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cv in
    nth 0 (A.BndValuator.eval prec pv bounds) I.nai in
  let gi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const bounds in
    fun yi =>
      let fi := nth 0 (A.TaylorValuator.eval prec deg yi pf bounds) A.TaylorValuator.TM.dummy in
      fun xi => A.TaylorValuator.TM.eval (prec, deg) fi yi xi in
  let di := I.div prec (I.sub prec vi ui) (I.fromZ prec nb) in
  let ui' := I.add prec ui (I.mul prec di (I.fromZ prec 0)) in
  let vi' := I.add prec ui (I.mul prec di (I.fromZ prec nb)) in
  eval_plot_aux prec gi check ui di I.whole (gi (I.join ui' vi')) (Z.to_nat nb) 0%Z nb nb nil.

Lemma eval_plot_correct :
  forall prec deg check vars hyps pf pu pv cf cu cv nb l,
  eval_plot prec deg check hyps pf pu pv cf cu cv (Zpos nb) = l ->
  let u := eval_real' pu vars cu in
  let v := eval_real' pv vars cv in
  eval_hyps hyps vars (
    plot (fun t => eval_real' pf (t :: vars) cf) u ((v - u) / IZR (Zpos nb)) l).
Proof.
intros prec deg check vars hyps pf pu pv cf cu cv nb l H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
revert H.
unfold eval_plot, eval_real'.
fold (compute_inputs prec hyps cu).
fold (compute_inputs prec hyps cv).
assert (Hcu := app_merge_hyps_eval_bnd prec _ _ cu H').
assert (Hcv := app_merge_hyps_eval_bnd prec _ _ cv H').
generalize (A.BndValuator.eval_correct' prec pv _ _ Hcv 0).
generalize (A.BndValuator.eval_correct' prec pu _ _ Hcu 0).
generalize (nth 0 (A.BndValuator.eval prec pv (compute_inputs prec hyps cv)) I.nai).
generalize (nth 0 (A.BndValuator.eval prec pu (compute_inputs prec hyps cu)) I.nai).
generalize (nth 0 (Prog.eval_real pv (vars ++ map (fun c => eval c nil) cv)) 0%R).
generalize (nth 0 (Prog.eval_real pu (vars ++ map (fun c => eval c nil) cu)) 0%R).
clear -H'.
intros u v ui vi Hu Hv.
intros <-.
set (bounds := A.TaylorValuator.TM.var :: _).
set (di := I.div prec (I.sub prec vi ui) (I.fromZ prec (Zpos nb))).
set (ui' := I.add prec ui (I.mul prec di (I.fromZ prec 0))).
set (vi' := I.add prec ui (I.mul prec di (I.fromZ prec (Zpos nb)))).
set (gi := fun yi =>
      let fi := nth 0 (A.TaylorValuator.eval prec deg yi pf bounds) A.TaylorValuator.TM.dummy in
      fun xi => A.TaylorValuator.TM.eval (prec, deg) fi yi xi).
set (f x := nth 0 (eval_real pf ((x :: vars) ++ map (fun c : expr => eval c nil) cf)) 0).
fold (gi (I.join ui' vi')).
set (d := ((v - u) / IZR (Zpos nb))%R).
assert (Hd : contains (I.convert di) (Xreal d)).
{ apply J.div_correct.
  now apply J.sub_correct.
  apply I.fromZ_correct. }
assert (Hg: forall ti xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (gi ti xi)) (Xreal (f x))).
{ intros ti xi x Hx.
  apply A.TaylorValuator.eval_correct with (2 := Hx).
  now apply app_merge_hyps_eval_bnd. }
rewrite <- (Z2Nat.id (Zpos nb)) at 2 by easy.
set (i := Z.to_nat (Zpos nb)).
cut (plot f (u + d * INR i) d nil).
2: now intros [|j] x _.
generalize (@nil I.type).
generalize I.whole (I.join ui' vi') 0%Z (Z.pos nb).
clearbody f gi di d i.
clear -Hu Hd Hg.
induction i as [|n IH].
{ simpl. intros _ _ _ l. now rewrite Rmult_0_r, Rplus_0_r. }
intros zi2 gxi mz rz acc Hacc.
cbn beta iota zeta delta [eval_plot_aux].
rewrite <- Nat2Z.inj_pred by apply lt_O_Sn.
simpl (Nat.pred (S n)).
set (xi1 := I.add prec ui (I.mul prec di (I.fromZ prec (Z.of_nat n)))).
set (xi2 := I.add prec ui (I.mul prec di (I.fromZ prec (Z.of_nat (S n))))).
set (xi := I.join xi1 xi2).
set (zi1 := gi gxi xi1).
set (yi := gi gxi xi).
set (c := andb
  (orb (check (I.meet yi (I.lower_extent zi1))) (check (I.meet yi (I.upper_extent zi1))))
  (orb (check (I.meet yi (I.lower_extent zi2))) (check (I.meet yi (I.upper_extent zi2))))).
clearbody c.
set (yizi := if c then (yi, zi1) else (gi xi xi, gi xi xi1)).
set (mz' :=
  if Z.eqb mz (Z.of_nat n) then (mz - Z.div2 (3 * rz))%Z
  else if c then mz
  else (Z.of_nat n - 1 - Z.div2 rz)%Z).
set (mz'' := if Z.ltb mz' 0%Z then 0%Z else mz').
clearbody mz' mz''.
set (gxi' := I.join (I.add prec ui (I.mul prec di (I.fromZ prec mz''))) xi1).
clearbody gxi'.
cut (plot f (u + d * INR n) d (fst yizi :: acc)).
{ destruct Z.eqb ; apply IH. }
clear -Hu Hd Hg Hacc.
intros [|i] x Hx.
2: {
  apply Hacc.
  revert Hx. clear.
  rewrite !S_INR.
  replace (u + d * INR n + d * (INR i + 1)) with (u + d * (INR n + 1) + d * INR i) by ring.
  replace (u + d * INR n + d * (INR i + 1 + 1)) with (u + d * (INR n + 1) + d * (INR i + 1)) by ring.
  easy. }
assert (Hxi: contains (I.convert xi) (Xreal x)).
{ apply J.join_correct with (u := u + d * (IZR (Z.of_nat n))) (v := u + d * (IZR (Z.of_nat (S n)))).
  apply J.add_correct with (1 := Hu).
  apply J.mul_correct with (1 := Hd).
  apply I.fromZ_correct.
  apply J.add_correct with (1 := Hu).
  apply J.mul_correct with (1 := Hd).
  apply I.fromZ_correct.
  rewrite Nat2Z.inj_succ, succ_IZR, <- INR_IZR_INZ.
  revert Hx. clear.
  now rewrite Rmult_0_r, Rplus_0_r, Rmult_plus_distr_l, Rplus_assoc. }
now destruct c ; simpl ; apply Hg.
Qed.

Import Float Specific_ops BigZ.

Open Scope bigZ_scope.

Goal True.
Proof.
evar (p : list I.type).
assert (plot (fun x => x^2 * sin (x^2))%R (-4) ((4 - (-4)) / IZR 1000) p).
match goal with
| |- plot ?f ?u ?d ?l =>
match d with
| ((?v - u) / IZR (Zpos ?d))%R =>
let fapp := eval cbv beta in (f reify_var) in
let vars := constr:((reify_var :: nil)%list) in
let vars := get_vars fapp vars in
let vars :=
  match get_vars fapp vars with
  | (reify_var :: ?vars)%list => vars
  end in
let vars := get_vars u vars in
let vars := get_vars v vars in
eapply plot_ext ; [
  let t := fresh "t" in intros t ;
  let fapp := eval cbv beta in (f t) in
  reify_partial fapp (t :: vars) ;
  exact (fun H => H) |] ;
reify_partial u vars ; intros <- ;
reify_partial v vars ; intros <- ;
find_hyps vars
end
end.
apply eval_plot_correct with
 (prec := F.PtoP 30) (deg := 10%nat)
 (check := let prec := F.PtoP 30 in let thr := F.scale (F.fromZ 1) (F.ZtoS (-5)) in
  fun yi => F'.le' (F.sub_UP prec (I.upper yi) (I.lower yi)) thr).
vm_compute ; apply eq_refl.
exact I.
Qed.
