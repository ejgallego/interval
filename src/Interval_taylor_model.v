Require Import Reals.
Require Import Interval_interval.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_specific_ops.
Require Import Interval_bigint_carrier.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import interval_compl.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq ssralg bigop.
Require Import poly_datatypes.
Require Import poly_inst_seq.
Require Import taylor_model_int_sharp.
Require Import coeff_inst.
Require Import rpa_inst.
Require Import xreal_ssr_compat.
Require Import Interval_univariate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Auxiliary lemmas on natural numbers *)
Lemma ltn_leq_pred m n : m < n -> m <= n.-1.
Proof. by move=> H; rewrite -ltnS (ltn_predK H). Qed.

Lemma maxnS (m n : nat) : 0 < maxn m n.+1.
Proof. by case: m =>[//|m]; rewrite maxnSS. Qed.

Lemma maxSn (m n : nat) : 0 < maxn m.+1 n.
Proof. by rewrite maxnC maxnS. Qed.

Module TM (I : IntervalOps) <: UnivariateApprox I.

(** Load the CoqApprox modules *)
Module PolX := ExactSeqPolyMonomUp FullXR.
Module Link := LinkSeqPolyMonomUp I.
Module PolI := SeqPolyMonomUpInt I.
Module Import TMI := TaylorModel I PolI PolX Link.

Inductive t_ := Const of I.type | Var | Tm of RPA.rpa.

Definition T := t_.

Definition U := (I.precision * nat)%type.

(** * Auxiliary material

The need for using a padding function (see [pad2] below) is due to the
current version of the correctness theorems of CoqApprox *)

Definition isTm (t : T) : bool := if t is Tm _ then true else false.

Definition unat (u : U) (n : nat) := (u.1, n).

Definition tmsize (tm : RPA.rpa) := PolI.tsize (RPA.approx tm).

Definition tsize (t : T) : nat :=
  match t with
    | Const _ | Var => 0
    | Tm tm => tmsize tm
  end.

Definition tm_helper1 (u : U) X (t : T) : RPA.rpa :=
  match t with
    | Const c => (TM_const u.1 c X u.2)
    | Var => let X0 := Imid X in (TM_var u.1 X0 X u.2)
    | Tm tm => tm (* ignore u, X in this branch *)
  end.

Definition tm_helper2pad (u : U) X (t : T) :=
  match t with
    | Const c => (TM_const u.1 c X u.2)
    | Var => let X0 := Imid X in (TM_var u.1 X0 X u.2)
    | Tm {| RPA.approx := pol; RPA.error := delta |} =>
      let pol' := PolI.tset_nth pol u.2 PolI.Int.tzero in
      (RPA.RPA pol' delta)
  end.

Lemma tsize_tm_helper1_geq u X t :
  tmsize (tm_helper1 u X t) >= tsize t.
Proof. by case: t. Qed.

Lemma tsize_tm_helper1_leq u X t :
  tmsize (tm_helper1 u X t) <= maxn (tsize t) (u.2).+1.
Proof.
case: t =>//; rewrite /tm_helper1.
by move=> c; rewrite /tsize /tmsize tsize_TM_const leq_max ltnSn orbC.
by rewrite /tsize /tmsize /= PolI.tsize_trec2.
move=> r /=; exact: leq_maxl.
Qed.

Lemma tsize_tm_helper1 u X t :
  tmsize (tm_helper1 u X t) = if t is Tm _ then tsize t else u.2.+1.
Proof.
case: t => [c||tm] //.
  by rewrite /tmsize tsize_TM_const.
by rewrite /tmsize PolI.tsize_trec2.
Qed.

Corollary tsizeS_tm_helper1 u X t :
  0 < tsize t ->
  tmsize (tm_helper1 u X t) = tsize t.
Proof. by have := tsize_tm_helper1 u X t; case: t. Qed.

Lemma tsize_tm_helper2pad_maxn u X t :
  tmsize (tm_helper2pad u X t) = maxn (tsize t) (u.2).+1.
Proof.
case: t; rewrite /tm_helper2pad.
by move=> c; rewrite /tsize /tmsize tsize_TM_const (appP idP maxn_idPr).
rewrite /tsize /tmsize /= PolI.tsize_trec2 (appP idP maxn_idPr) //.
by move =>  [pol delta]; rewrite /tsize /tmsize /= PolI.tsize_set_nth maxnC.
Qed.

Corollary tsize_tm_helper2pad u X t :
  tsize t <= (u.2).+1 ->
  tmsize (tm_helper2pad u X t) = (u.2).+1.
Proof. move=> Hn; rewrite tsize_tm_helper2pad_maxn //; exact/maxn_idPr. Qed.

Lemma i_validTM_Xnan (X0 X: interval) (tm: RPA.rpa) (f: ExtendedR -> ExtendedR):
  i_validTM X0 X tm f -> i_validTM X0 X tm (fun x => Xmask (f x) x).
Proof.
case=> /= [H1 H2 H3].
split=>//=.
move=> xi0 Hxi0.
move/(_ xi0 Hxi0) in H3.
have [a [h1 h2 h3]] := H3.
exists a.
split=>//.
move=> x Hx.
move/(_ x Hx) in h3.
case: x Hx h3 => [|r] Hx h3 //.
simpl in h3 |- *.
rewrite teval_in_nan in h3.
by rewrite [FullXR.tsub tt _ _]Xsub_Xnan_r in h3.
Qed.

Definition not_nil (tf : T) : bool :=
  match tf with
    | Const _ => true
    | Var => true
    | Tm tm => 0 < tmsize tm
  end.

Lemma sizeS_not_nil (tf : T) : 0 < tsize tf -> not_nil tf.
Proof. by case: tf =>[//|//|r]. Qed.

Definition approximates (X : I.type) (f:ExtendedR->ExtendedR) (tf : T) : Prop :=
(** The main predicate involved in this Module implementation *)
  let X0 := Imid X in
  [/\ f Xnan = Xnan,
    not_nil tf,
    not_empty (I.convert X0) &
    forall u : U,
    let tm := tm_helper1 u X tf in
    i_validTM (I.convert X0) (I.convert X) tm f].

Lemma tm_helper1_correct u Y f tf :
  approximates Y f tf ->
  approximates Y f (Tm  (tm_helper1 u Y tf)).
Proof.
case: tf => [c|| tm]; rewrite /approximates //=; case; intuition split =>//.
by rewrite /tmsize tsize_TM_const.
by rewrite /tmsize PolI.tsize_trec2.
Qed.

Lemma tm_helper2pad_correct u X f tf :
  approximates X f tf ->
  tsize tf <= (u.2) ->
  approximates X f (Tm  (tm_helper2pad u X tf)).
Proof.
case: tf => [c||[pol delta]]; rewrite /approximates /=.
- by case=>*; split=>//; rewrite /tmsize tsize_TM_const.
- by case=>*; split=>//; rewrite /tmsize PolI.tsize_trec2.
case=> [NN SS h0 H] Hsize.
do 1!split=>//.
rewrite /tmsize /= PolI.tsize_set_nth /= maxnC; exact: maxnS.
move=> u0.
have [H1 H2 H3] := H u0.
split=>//= xi0 Hxi0.
have /= [a [h1 h2 h3]] := H3 xi0 Hxi0.
exists (PolX.tset_nth a u.2 (Xreal 0)).
rewrite PolI.tsize_set_nth PolX.tsize_set_nth h1.
split=>//.
  move=> k Hk.
  case: (ltnP k (PolI.tsize pol)) => Hineq.
    rewrite PolI.tnth_set_nth PolX.tnth_set_nth.
    case: (k == u.2); first exact: PolI.Int.zero_correct.
    exact: h2.
  rewrite PolI.tnth_set_nth PolX.tnth_set_nth.
  case: (k == u.2); first exact: PolI.Int.zero_correct.
  rewrite PolI.tnth_out // PolX.tnth_out //.
  exact: PolI.Int.zero_correct.
  by rewrite h1.
move=> x Hx.
have := h3 x Hx.
rewrite !is_horner_mask => H'.
rewrite PolX.tsize_set_nth.
rewrite /tmsize /= -h1 in Hsize.
rewrite -(big_mkord xpredT
  (fun i => FullXR.tmul tt (PolX.tnth (PolX.tset_nth a u.2 (Xreal 0)) i)
  (FullXR.tpow tt (FullXR.tsub tt x xi0) i))).
have [Hnan|[Hnan|[Hr1 Hr2]]] : x = Xnan \/ (xi0 = Xnan \/
  (x = Xreal (proj_val x) /\ xi0 = Xreal (proj_val xi0))).
  case: (x); case: (xi0); intuition done.
- by rewrite Hnan /= in H' *.
- by rewrite Hnan [FullXR.tsub tt x Xnan]Xsub_Xnan_r /= in H' *.
rewrite (big_cat_nat Xadd_monoid (n := PolX.tsize a)) =>//.
  rewrite [in X in Xadd_monoid _ X]big1_seq /=.
    rewrite Xadd_0_r.
    rewrite big_mkord.
    rewrite (eq_bigr (fun i =>
    FullXR.tmul tt (PolX.tnth a (fintype.nat_of_ord i))
    (FullXR.tpow tt (FullXR.tsub tt x xi0) (fintype.nat_of_ord i)))).
      exact: H'.
    move=> i _; rewrite PolX.tnth_set_nth ifF //.
    apply/eqP=> Hi.
    rewrite -Hi in Hsize.
    by case: i {Hi} Hsize =>/= m Hm; rewrite leqNgt Hm.
  move=> i; rewrite mem_index_iota => Hi.
  rewrite PolX.tnth_set_nth.
  rewrite Hr1 Hr2 [FullXR.tpow _ _ _]Xpow_idem Xpow_Xreal.
  case: (i == u.2).
    by rewrite /FullXR.tmul /= Rmult_0_l.
  rewrite PolX.tnth_out.
  by rewrite /FullXR.tmul /= Rmult_0_l.
  by case/andP: Hi.
rewrite (appP idP maxn_idPl); exact: ltnW.
Qed.

Definition pad2 (u0 : U) (X : I.type) (arg : T * T) : T * T :=
  let X0 := Imid X in
  let (t1, t2) := arg in
  let n1 := tsize t1 in
  let n2 := tsize t2 in
  match nat_compare n1 n2 with
    | Eq => if isTm t1 && isTm t2
            then (t1, t2)
            else (* degenerate case *)
              let u := unat u0 n1 in
              (Tm (tm_helper2pad u X t1), Tm (tm_helper2pad u X t2))
    | Lt (* n1 < n2 *) => let u := unat u0 n2.-1 in
      (Tm (tm_helper2pad u X t1), Tm (tm_helper1 u X t2))
    | Gt (* n1 > n2 *) => let u := unat u0 n1.-1 in
      (Tm (tm_helper1 u X t1), Tm (tm_helper2pad u X t2))
  end.

Lemma pad2_correct : forall u X f g t,
  approximates X f t.1 -> approximates X g t.2 ->
  let t' := pad2 u X t in
  approximates X f t'.1 /\ approximates X g t'.2.
Proof.
move=> u X f g [t1 t2] Hf Hg.
rewrite /pad2.
case: (nat_compare_spec (tsize t1) (tsize t2)).
- move=> H.
  case: (isTm t1 && isTm t2); first by split.
  split; apply: tm_helper2pad_correct =>//.
  by rewrite H.
- move=> Hsize.
  simpl in *.
  split.
    apply: tm_helper2pad_correct =>//=.
    move/ltP in Hsize.
    exact: ltn_leq_pred.
  exact: tm_helper1_correct.
- move=> Hsize.
  simpl in *.
  split; last first.
    apply: tm_helper2pad_correct =>//=.
    move/ltP in Hsize.
    exact: ltn_leq_pred.
  exact: tm_helper1_correct.
Qed.

Lemma tsize_pad2 : forall u X t, let t' := pad2 u X t in
  tsize t'.2 = tsize t'.1.
Proof.
move=> u X [t1 t2] /=.
case: (nat_compare_spec (tsize t1) (tsize t2)) =>/=.
- move=> H.
  case: (isTm t1 && isTm t2); first by rewrite H.
  by rewrite /= !tsize_tm_helper2pad H.
- move/ltP=> H.
  rewrite tsize_tm_helper2pad /=; last by rewrite (ltn_predK H) ltnW.
  rewrite [tmsize _]tsizeS_tm_helper1; first by rewrite (ltn_predK H).
  exact: (leq_trans _ H).
- move/ltP=> H.
  rewrite tsize_tm_helper2pad /=; last by rewrite (ltn_predK H) ltnW.
  rewrite [tmsize _]tsizeS_tm_helper1; first by rewrite (ltn_predK H).
  exact: (leq_trans _ H).
Qed.

Lemma isTm_pad2 : forall u X t, let t' := pad2 u X t in
  isTm t'.1 /\ isTm t'.2.
Proof.
move=> u X [t1 t2] /=.
case: (nat_compare_spec (tsize t1) (tsize t2));
  case: t1 => [c||tm]; case: t2 => [c'||tm']; done.
Qed.

(** * Main definitions and correctness claims *)

Definition add (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let t' := pad2 u X (t1, t2) in
  let M1 := tm_helper1 u X t'.1 in
  let M2 := tm_helper1 u X t'.2 in
  (* argument X is not used in the very end as TM_add doesn't need it *)
  Tm (TM_add u.1 M1 M2).

Lemma add_correct :
  forall u (Y : I.type) f tf g tg,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xadd (f x) (g x)) (add u Y tf tg).
Proof.
move=> u Y f tf g tg Hf Hg.
have [[NN SS H1 H2] [_ _ _ H3]] := @pad2_correct u Y f g (tf, tg) Hf Hg.
split=>//.
by rewrite NN.
rewrite /add.
set t' := pad2 u Y (tf, tg) in SS *.
rewrite /= /tmsize size_TM_add /=.
rewrite [PolI.tsize _]tsize_tm_helper1.
case: t'.1 SS; rewrite ?(maxSn,maxnS) //.
rewrite /not_nil /=.
move=> r Hr.
by rewrite -(prednK Hr) maxSn.
move=> u'.
apply: TM_add_correct; [|exact: H2 u|exact: H3 u].
rewrite ![PolI.tsize _]tsize_tm_helper1 tsize_pad2.
by case: pad2 (isTm_pad2 u Y (tf, tg)) => [[c|| tm][c'|| tm']] [].
Qed.

Definition var : T := Var.

Theorem var_correct :
  forall (X : I.type), not_empty (I.convert X) ->
  approximates X id var.
Proof.
move=> X HX.
do 1!split=>//; first exact: not_empty_Imid.
move=> u.
apply: TM_var_correct; first exact: Imid_subset.
(* FIXME: This hypothesis in TM_var_correct should directly be [not_empty...] *)
move/not_empty_Imid in HX.
case: HX => x Hx; by exists (Xreal x).
Qed.

Definition const : I.type -> T := Const.

Theorem const_correct :
  forall (c : I.type) (r : R), contains (I.convert c) (Xreal r) ->
  forall (X : I.type), not_empty (I.convert X) ->
  approximates X (Xmask (Xreal r)) (const c).
Proof.
move=> c r Hcr X [v Hv].
split; [done|done|by apply: not_empty_Imid; exists v|].
move=> u.
apply i_validTM_Xnan.
apply TM_const_correct =>//.
  apply: not_empty_Imid.
  by exists v.
apply: Imid_subset.
by exists v.
Qed.

(*
Theorem const_correct_rev :
  forall (c : I.type) (r : R) (X : I.type),
  approximates X (fun x => Xreal r) (const c) ->
  contains (I.convert c) (Xreal r).
Proof.
move=> c r X [H1 [H2 H3]].
Abort.
*)

(* No need for optimizing [eval], as it's only used once in the end
Definition eval (u : U) (X : I.type) (t : T) : I.type :=
  match t with
    | Const C => C
    | Var => X
    | Tm X0 tm =>
      I.add u.1 (PolI.teval u.1 (RPA.approx tm) (I.sub u.1 X X0)) (RPA.error tm)
  end.
*)

Definition eval (u : U) (Y X : I.type) (t : T) : I.type :=
  let X0 := Imid Y in
  let tm := tm_helper1 u Y t in
  I.add u.1 (PolI.teval u.1 (RPA.approx tm) (I.sub u.1 X X0)) (RPA.error tm).

Theorem eval_correct :
  forall u (Y : I.type) f tf, approximates Y f tf ->
  forall (X : I.type), I.subset X Y ->
  forall x, contains (I.convert X) x ->
  contains (I.convert (eval u Y X tf)) (f x).
Proof.
move=> u Y f tf Hf X HXY x HXx.
rewrite /eval.
have {Hf} := tm_helper1_correct u Hf.
move: (tm_helper1 u Y tf) => tm Htm.
have {Htm} [NN SS H0] := Htm.
move/(_ u) => [/= H1 H2 H3].
set c0 := I.convert_bound (I.midpoint Y).
have {H3} [|qx [H4 H5 H6]] := H3 c0.
  apply: Imid_contains.
  apply: not_empty'E.
  exists x.
  apply: subset_contains HXx.
  exact: I.subset_correct.
move/(_ x) in H6.
apply I.subset_correct in HXY.
move/(_ (subset_contains _ _ HXY _ HXx)) in H6.
have Hnan: f x <> Xnan /\ I.convert (RPA.error tm) <> IInan ->
  PolX.teval tt qx (FullXR.tsub tt x c0) =
  Xreal (proj_val (PolX.teval tt qx (FullXR.tsub tt x c0))).
  case=> Hfx HD.
  case Eqx : PolX.teval => [|r] //; [exfalso].
  rewrite Eqx [FullXR.tsub tt _ _]Xsub_Xnan_r /contains in H6.
  by case: I.convert H6 HD.
case ED : (I.convert (RPA.error tm)) => [|a b].
rewrite (Iadd_Inan_propagate_r _ _ ED (y := PolX.teval tt qx (Xsub x c0))) //.
apply: teval_contains =>//.
apply: I.sub_correct =>//.
apply Imid_contains.
(* duplicate *)
apply: not_empty'E.
exists x.
exact: subset_contains HXx.
have->: f x = Xadd (PolX.teval tt qx (FullXR.tsub tt x c0))
  (FullXR.tsub tt (f x) (PolX.teval tt qx (FullXR.tsub tt x c0))).
case Efx : (f x) => [|r]; first by rewrite XaddC.
rewrite Efx ED in Hnan.
rewrite Hnan //=.
by congr Xreal; auto with real.
apply I.add_correct =>//.
apply: teval_contains; first by split.
apply: I.sub_correct =>//.
apply: Imid_contains.
(* duplicate *)
apply: not_empty'E.
exists x.
exact: subset_contains HXx.
Qed.

(*
Definition exp (u : U) (X : I.type) (t : T) : T :=
  let X0 := Imid X in
  let tm := (tm_helper1 u X t) in
  let n := (tmsize tm).-1 in
  Tm (TM_comp u.1 (TM_exp u.1) (tm_helper1 u X t) X0 X n).

Lemma exp_correct :
  forall u (Y : I.type) f tf, approximates Y f tf ->
  approximates Y (fun x => Xexp (f x)) (exp u Y tf).
Proof.
move=> u Y f t Hmain.
- have [NN SS H1 Hf] := Hmain; split; [by rewrite NN|idtac|done|move=>u'].
  by rewrite /not_nil /exp /tmsize /exp size_TM_comp.
  have {Hf} [H2 H3 H4] := Hf u.
  have [v Hv] := H1.
  apply (TM_comp_correct u.1) =>//.
  + by exists (Xreal v).
  + have {H4} [a [H H' H'']] := H4 _ Hv.
    exists (PolX.tnth a 0).
    apply: H'.
    case: t SS {Hmain H2 H H''} =>[c||tm //] Hnn.
      by rewrite /tmsize tsize_TM_const.
    by rewrite /tmsize PolI.tsize_trec2.
  + rewrite /tmsize.
    rewrite /= /tmsize in SS.
    by case: PolI.tsize SS.
  + move=> *; split; last by rewrite PolI.tsize_trec1.
    exact: TM_exp_correct.
Save.
*)

Definition exp (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Const c => Const (I.exp u.1 c)
    | Var => let X0 := Imid X in Tm (TM_exp u.1 X0 X u.2)
    | Tm tm => let X0 := Imid X in let n := (tmsize tm).-1 in
      Tm (TM_comp u.1 (TM_exp u.1) tm X0 X n)
  end.

Lemma use_TM_var (dummy : U) (Y : I.type) (f : ExtendedR -> ExtendedR) :
  approximates Y f Var -> forall x, contains (I.convert Y) x -> f x = x.
Proof.
case=> [H0 H1 H2 H3] [//|r].
have [/= H4 H5 H6] := H3 dummy.
have [v Hv] := H2.
have [a [H7 H8 H9]] := H6 _ Hv.
move=> Hr.
have H := H9 _ Hr.
rewrite /TI.T_var /= in H.
rewrite /TI.Rec.var_rec in H.
admit.
Qed.

Lemma exp_correct :
  forall u (Y : I.type) f tf, approximates Y f tf ->
  approximates Y (fun x => Xexp (f x)) (exp u Y tf).
Proof.
move=> u Y f [c||tm] Hmain.
- have [NN SS H1 Hf] := Hmain; split; [by rewrite NN|done|done|move=>u'].
  simpl in Hf.
  have {Hf} [H2 H3 H4] := Hf u'.
  simpl.
  admit. (* i_validTM *)
- have [NN SS H1 Hf] := Hmain; split; [by rewrite NN|idtac|done|move=>u'].
  by rewrite /not_nil /exp /tmsize PolI.tsize_trec1.
  eapply TM_fun_eq.
    move=> x Hx.
    symmetry.
    rewrite (use_TM_var u Hmain).
    reflexivity.
    done.
  have {Hf} [H2 H3 H4] := Hf u'.
  apply TM_exp_correct =>//.
  have [v Hv] := H1; by exists (Xreal v).
- have [NN SS H1 Hf] := Hmain; split; [by rewrite NN|idtac|done|move=>u'].
  by rewrite /not_nil /exp /tmsize /exp size_TM_comp.
  have {Hf} [H2 H3 H4] := Hf u'.
  have [v Hv] := H1.
  apply (TM_comp_correct u.1) =>//.
  + by exists (Xreal v).
  + have {H4} [a [H H' H'']] := H4 _ Hv.
    exists (PolX.tnth a 0).
    exact: H'.
  + rewrite /tmsize.
    rewrite /= /tmsize in SS.
    by case: PolI.tsize SS.
  + move=> *; split; last by rewrite PolI.tsize_trec1.
    exact: TM_exp_correct.
Save.

End TM.
