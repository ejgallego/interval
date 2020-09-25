From Coq Require Import List Reals.
Require Import Tactic.

Open Scope R_scope.

Import Xreal Interval Tree Reify Prog.
Import Tactic.Private.
Import IT.Private.IT1.

Module F := SFBI2.

Definition plot (f : R -> R) (u v : R) (l : list (I.type * I.type)) :=
  forall x, (u <= x <= v)%R ->
  Exists (fun p : I.type * I.type => let (xi, yi) := p in
    contains (I.convert xi) (Xreal x) /\ contains (I.convert yi) (Xreal (f x))) l.

Lemma plot_ext :
  forall f g u v l,
  (forall x, f x = g x) ->
  plot f u v l -> plot g u v l.
Proof.
intros f g u v l H K x Hx.
specialize (K x Hx).
induction K as [[xi yi] K| [xi yi] l _ IHK].
apply Exists_cons_hd.
now rewrite <- H.
now apply Exists_cons_tl.
Qed.

Fixpoint eval_plot_aux (fi : I.type -> I.type) check n xi acc :=
  let yi := fi xi in
  match n with
  | S n =>
    match check yi with
    | true => (xi, yi) :: acc
    | false =>
      let m := I.bisect xi in
      eval_plot_aux fi check n (fst m) (eval_plot_aux fi check n (snd m) acc)
    end
  | O => (xi, yi) :: acc
  end.

Definition eval_plot prec deg limit check hyps pf pu pv cf cu cv :=
  let hyps := R.merge_hyps prec hyps in
  let ui :=
    let bounds := hyps ++ map (T.eval_bnd prec) cu in
    nth 0 (A.BndValuator.eval prec pu bounds) I.nai in
  let vi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cv in
    nth 0 (A.BndValuator.eval prec pv bounds) I.nai in
  let fi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const bounds in
    fun xi =>
      A.TaylorValuator.TM.eval (prec, deg)
        (nth 0 (A.TaylorValuator.eval prec deg xi pf bounds)
        A.TaylorValuator.TM.dummy) xi xi in
  eval_plot_aux fi check limit (I.join ui vi) nil.

Lemma eval_plot_correct :
  forall prec deg limit check vars hyps pf pu pv cf cu cv l,
  eval_plot prec deg limit check hyps pf pu pv cf cu cv = l ->
  eval_hyps hyps vars (
    plot (fun t => eval_real' pf (t :: vars) cf) (eval_real' pu vars cu) (eval_real' pv vars cv) l).
Proof.
intros prec deg limit check vars hyps pf pu pv cf cu cv l H.
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
set (fi xi := A.TaylorValuator.TM.eval (prec, deg) (nth 0 (A.TaylorValuator.eval prec deg xi pf bounds) A.TaylorValuator.TM.dummy) xi xi).
unfold plot.
intros x Hx.
set (f x := nth 0 (eval_real pf ((x :: vars) ++ map (fun c : expr => eval c nil) cf)) 0).
set (P := fun p : I.type * I.type => let (xi, yi) := p in
    contains (I.convert xi) (Xreal x) /\ contains (I.convert yi) (Xreal (f x))).
change (Exists P (eval_plot_aux fi check limit (I.join ui vi) nil)).
generalize (A.J.join_correct _ _ _ _ _ Hu Hv Hx).
generalize (I.join ui vi).
clear -H' P.
generalize (@nil (I.type * I.type)).
clear -H'.
induction limit as [|n IH].
- intros acc xi Hx.
  apply Exists_cons_hd.
  apply (conj Hx).
  simpl.
  apply A.TaylorValuator.eval_correct with (2 := Hx).
  now apply app_merge_hyps_eval_bnd.
- intros acc xi Hx.
  simpl.
  destruct check.
  + apply Exists_cons_hd.
    apply (conj Hx).
    simpl.
    apply A.TaylorValuator.eval_correct with (2 := Hx).
    now apply app_merge_hyps_eval_bnd.
  + destruct (I.bisect_correct xi _ Hx) as [H|H].
    now apply IH.
    generalize (IH acc _ H).
    clear.
    generalize (eval_plot_aux fi check n (snd (I.bisect xi)) acc).
    generalize (fst (I.bisect xi)).
    clear.
    induction n.
    * intros xi acc.
      apply Exists_cons_tl.
    * intros xi acc.
      simpl.
      destruct check.
      apply Exists_cons_tl.
      intros H.
      apply IHn.
      now apply IHn.
Qed.

Import Float Specific_ops BigZ.

Open Scope bigZ_scope.

Goal True.
evar (p : list (I.type * I.type)).
assert (plot (fun x => exp (sin x)) 0 1 p).
match goal with
| |- plot ?f ?u ?v ?l =>
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
end.
apply eval_plot_correct with
 (prec := F.PtoP 30) (deg := 10%nat) (limit := 10%nat)
 (check := let prec := F.PtoP 30 in let thr := F.scale (F.fromZ 1) (F.ZtoS (-5)) in
  fun yi => F'.le' (F.sub_UP prec (I.upper yi) (I.lower yi)) thr).
vm_compute ; apply eq_refl.
exact I.
Qed.
