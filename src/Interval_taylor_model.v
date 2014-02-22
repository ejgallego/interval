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
(*
(*
  TODO: We may add such a Boolean pred (or a more efficient one) in IntervalOps
*)
Definition Inot_empty (ix : I.type) : bool :=
  I.subset (Imid ix) ix.

Lemma Inot_empty_correct (ix : I.type) :
  Inot_empty ix = true -> not_empty (I.convert ix).
Proof.
rewrite /Inot_empty.
move/I.subset_correct.
move/subset_contains=> H.
exists 0%Re. (* FIXME *)
apply: H.
Abort.
*)

(** * Main type definitions *)

Inductive t_ := Const of I.type | Var | Tm of RPA.rpa.

Definition T := t_.

Definition U := (I.precision * nat)%type.

(** * Auxiliary material

The need for using a padding function (see [pad2] below) is due to the
current version of the correctness theorems of CoqApprox *)

Definition isConst (t : T) : bool := if t is Const _ then true else false.

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
by move=> c; rewrite /tsize /tmsize size_TM_const leq_max ltnSn orbC.
by rewrite /tsize /tmsize /= PolI.tsize_trec2.
move=> r /=; exact: leq_maxl.
Qed.

Lemma tsize_tm_helper1 u X t :
  tmsize (tm_helper1 u X t) = if t is Tm _ then tsize t else u.2.+1.
Proof.
case: t => [c||tm] //.
  by rewrite /tmsize size_TM_const.
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
by move=> c; rewrite /tsize /tmsize size_TM_const (appP idP maxn_idPr).
by rewrite /tsize /tmsize /= PolI.tsize_trec2 (appP idP maxn_idPr) //.
by move =>  [pol delta]; rewrite /tsize /tmsize /= PolI.tsize_set_nth maxnC.
Qed.

Corollary tsize_tm_helper2pad u X t :
  tsize t <= (u.2).+1 ->
  tmsize (tm_helper2pad u X t) = (u.2).+1.
Proof. move=> Hn; rewrite tsize_tm_helper2pad_maxn //; exact/maxn_idPr. Qed.

Definition not_nil (tf : T) : bool :=
  match tf with
    | Const _ => true
    | Var => true
    | Tm tm => tmsize tm != 0
  end.

Lemma not_nilF (t : T) :
  not_nil t = false -> tsize t = 0.
Proof. by case: t =>// tm; rewrite /not_nil /=; case: tmsize. Qed.

(** * Define the main validity predicate *)

Definition approximates (X : I.type) (f:ExtendedR->ExtendedR) (tf : T) : Prop :=
  let X0 := Imid X in
  [/\ f Xnan = Xnan,
    not_nil tf &
    not_empty (I.convert X) ->
    match tf with
      | Const c =>
        forall x : R, (* utterly *) contains (I.convert c) (f (Xreal x))
      | Var =>
        forall x : R, (* utterly *) f (Xreal x) = Xreal x
      | Tm tm =>
        i_validTM (I.convert X0) (I.convert X) tm f
    end].

Theorem approximates_ext :
  forall f g h xi,
  (forall x, f x = g x) ->
  approximates xi f h -> approximates xi g h.
Proof.
move=> f g h xi Hfg [Hnan Hcont Hmain].
split=>//.
by rewrite -Hfg.
move=> Hne; move/(_ Hne): Hmain.
case: h {Hcont}=> [c| |tm] Hmain *; rewrite -?Hfg //.
apply: TM_fun_eq Hmain.
move=> *; exact: Hfg.
Qed.

Lemma tm_helper1_correct u Y f tf :
  approximates Y f tf ->
  approximates Y f (Tm (tm_helper1 u Y tf)).
Proof.
case: tf =>[c||tm]; rewrite /approximates //; case => Hnan _ H; split=>//=.
- by rewrite /tmsize size_TM_const.
- move=> Hne; move/(_ Hne) in H.
  apply TM_const_correct =>//.
  exact: not_empty_Imid.
  exact: Imid_subset.
- by rewrite /tmsize PolI.tsize_trec2.
- move=> Hne; move/(_ Hne) in H.
  eapply (TM_fun_eq (f := id)).
  move=> [|x] Hx; by symmetry.
  apply: TM_var_correct =>//.
  exact: Imid_subset.
  apply not_empty_Imid in Hne.
  by have [v Hv] := Hne; exists (Xreal v).
Qed.

Lemma tm_helper2pad_correct u X f tf :
  approximates X f tf ->
  tsize tf <= (u.2) ->
  approximates X f (Tm  (tm_helper2pad u X tf)).
Proof.
case: tf => [c||[pol delta]]; rewrite /approximates /=.
- case=> Hnan _ H; split=>//.
  by rewrite /tmsize -lt0n size_TM_const ltnS //.
  move=> Hne; move/(_ Hne) in H.
  apply TM_const_correct=>//.
  exact: not_empty_Imid.
  exact: Imid_subset.
- case=> Hnan Hnil H Hu; split=>//.
  by rewrite /tmsize -lt0n PolI.tsize_trec2 ltnS //.
  move=> Hne; move/(_ Hne) in H.
  apply: (TM_fun_eq (f := id)).
  move=> [|x] Hx; by symmetry.
  apply: TM_var_correct =>//.
  exact: Imid_subset.
  apply not_empty_Imid in Hne.
  by have [v Hv] := Hne; exists (Xreal v).
case=> [NN SS H] Hsize.
do 1!split=>//.
rewrite /tmsize /= PolI.tsize_set_nth /= maxnC -lt0n; exact: maxnS.
move=> Hne; move/(_ Hne) in H.
have [H1 H2 H3] := H.
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
  if isTm t1 then
    if isTm t2 then
      let n1 := tsize t1 in
      let n2 := tsize t2 in
      match nat_compare n1 n2 with
      | Eq => arg (* frequent case *)
      | Lt => let u := unat u0 n2.-1 in (Tm (tm_helper2pad u X t1), t2)
      | Gt => let u := unat u0 n1.-1 in (t1, Tm (tm_helper2pad u X t2))
      end
    else
      if not_nil t1 then
        let u := unat u0 (tsize t1).-1 in (t1, Tm (tm_helper1 u X t2))
      else (* degenerate case *)
        (Tm (tm_helper2pad u0 X t1), Tm (tm_helper1 u0 X t2))
  else
    if isTm t2 then
      if not_nil t2 then
        let u := unat u0 (tsize t2).-1 in (Tm (tm_helper1 u X t1), t2)
      else (* degenerate case *)
        (Tm (tm_helper1 u0 X t1), Tm (tm_helper2pad u0 X t2))
    else (Tm (tm_helper1 u0 X t1), Tm (tm_helper1 u0 X t2)).

Theorem pad2_correct : forall u X f g t,
  approximates X f t.1 -> approximates X g t.2 ->
  let t' := pad2 u X t in
  approximates X f t'.1 /\ approximates X g t'.2.
Proof.
move=> u X f g [t1 t2] Hf Hg.
rewrite /pad2.
case E1: (isTm t1); case E2: (isTm t2).
(* both Tm *)
case: (nat_compare_spec (tsize t1) (tsize t2)) => H.
(* t1 = t2 *)
by split.
(* t1 < t2 *)
split=>//; apply: tm_helper2pad_correct; move/ltP in H=>//; exact: ltn_leq_pred.
(* t2 < t1 *)
split=>//; apply: tm_helper2pad_correct; move/ltP in H=>//; exact: ltn_leq_pred.
(* only t1 *)
case Ene: not_nil.
  by split=>//; apply: tm_helper1_correct.
move/not_nilF in Ene.
split=>//=.
  apply: tm_helper2pad_correct=>//.
  by rewrite Ene.
exact: tm_helper1_correct.
(* only t2 *)
case Ene: not_nil.
  by split=>//; apply: tm_helper1_correct.
move/not_nilF in Ene.
split=>//=.
  exact: tm_helper1_correct.
apply: tm_helper2pad_correct=>//.
by rewrite Ene.
(* none Tm *)
by split; apply tm_helper1_correct.
Qed.

Theorem size_pad2 : forall u X t, let t' := pad2 u X t in
  tsize t'.2 = tsize t'.1.
Proof.
move=> u X [t1 t2] /=.
case E1: (isTm t1); case E2: (isTm t2).
(* both Tm *)
case: (nat_compare_spec (tsize t1) (tsize t2)) => H.
(* t1 = t2 *)
done.
(* t1 < t2 *)
move/ltP in H.
rewrite /= tsize_tm_helper2pad /=; last by rewrite (ltn_predK H) ltnW.
by rewrite (ltn_predK H).
(* t2 < t1 *)
move/ltP in H.
rewrite /= tsize_tm_helper2pad /=; last by rewrite (ltn_predK H) ltnW.
by rewrite (ltn_predK H).
(* only t1 *)
case Ene: not_nil =>//.
(* . *)
rewrite /not_nil in Ene.
rewrite /= !tsize_tm_helper1.
case: t2 Ene E2 =>[c2| |t2] Ene E2 //.
(* . *)
case: t1 Ene E1 =>[c1| |t1] Ene E1 //.
rewrite -/(is_true _) -lt0n in Ene.
by rewrite /= (ltn_predK Ene).
(* . *)
case: t1 Ene E1 =>[c1| |t1] Ene E1 //.
rewrite -/(is_true _) -lt0n in Ene.
by rewrite /= (ltn_predK Ene).
(* . *)
move/not_nilF in Ene.
rewrite /= tsize_tm_helper1 tsize_tm_helper2pad.
by case: t2 E2.
by rewrite Ene.
(* . *)
(* only t2 *)
case Ene: not_nil =>//.
(* . *)
rewrite /not_nil in Ene.
rewrite /= !tsize_tm_helper1.
case: t1 Ene E1 =>[c1| |t1] Ene E1 //.
(* . *)
case: t2 Ene E2 =>[c2| |t2] Ene E2 //.
rewrite -/(is_true _) -lt0n in Ene.
by rewrite /= (ltn_predK Ene).
(* . *)
case: t2 Ene E2 =>[c2| |t2] Ene E2 //.
rewrite -/(is_true _) -lt0n in Ene.
by rewrite /= (ltn_predK Ene).
(* . *)
move/not_nilF in Ene.
rewrite /= tsize_tm_helper1 tsize_tm_helper2pad.
by case: t1 E1.
by rewrite Ene.
(* none Tm *)
rewrite /= !tsize_tm_helper1.
by case: t1 E1 E2; case: t2.
Qed.

(* A "confidence" lemma (not used elsewhere in the development) *)
Remark size_pad2_l u X t :
  let t' := pad2 u X t in
  tsize t'.1 >= maxn (tsize t.1) (tsize t.2).
Proof.
case: t => [t1 t2] /=.
rewrite geq_max.
apply/andP; split.
(* . t1 *)
case E1: (isTm t1); case E2: (isTm t2).
(* both Tm *)
case: (nat_compare_spec (tsize t1) (tsize t2)) => H.
(* t1 = t2 *)
done.
(* t1 < t2 *)
move/ltP in H.
rewrite /= tsize_tm_helper2pad /=; last by rewrite (ltn_predK H) ltnW.
rewrite (ltn_predK H); exact: ltnW.
(* t2 < t1 *)
exact: leqnn.
(* only t1 *)
case Ene: not_nil =>//=.
(* . *)
rewrite tsize_tm_helper2pad_maxn.
exact: leq_maxl.
(* only t2 *)
case Ene: not_nil =>//=.
(* . *)
by rewrite tsize_tm_helper1_geq.
(* . *)
by rewrite tsize_tm_helper1_geq.
(* none Tm *)
rewrite /= !tsize_tm_helper1.
by case: t1 E1 E2; case: t2.
(****************)
(* . t2 *)
case E1: (isTm t1); case E2: (isTm t2).
(* both Tm *)
case: (nat_compare_spec (tsize t1) (tsize t2)) => H.
(* t1 = t2 *)
by rewrite H.
(* t1 < t2 *)
move/ltP in H.
rewrite /= tsize_tm_helper2pad /=; last by rewrite (ltn_predK H) ltnW.
by rewrite (ltn_predK H).
(* t2 < t1 *)
by move/ltP/ltnW in H.
(* only t1 *)
case Ene: not_nil =>//=.
(* . *)
by case: t2 E1 E2.
(* . *)
rewrite tsize_tm_helper2pad_maxn.
by case: t2 E1 E2.
(* only t2 *)
case Ene: not_nil =>//=.
(* . *)
rewrite /= !tsize_tm_helper1.
case: t1 E1 E2 Ene; case: t2 =>//.
(* . *)
move=> r _ _ _ /=.
rewrite -/(is_true _).
rewrite -lt0n.
by move/ltn_predK->.
(* . *)
move=> r _ _ /=.
rewrite -/(is_true _).
rewrite -lt0n.
by move/ltn_predK->.
(* . *)
by move/not_nilF: Ene =>->.
(* none Tm *)
by case: t1 E1 E2; case: t2 =>//.
Qed.

Theorem isTm_pad2 : forall u X t, let t' := pad2 u X t in
  isTm t'.1 /\ isTm t'.2.
Proof.
move=> u X [t1 t2] /=.
by case E1: (isTm t1); case E2: (isTm t2)=>//;
  case: (nat_compare_spec (tsize t1) (tsize t2));
  case: (not_nil t1); case: (not_nil t2)=>//.
Qed.

(** * Main definitions and correctness claims *)

Definition const : I.type -> T := Const.

Theorem const_correct :
  forall (c : I.type) (r : R), contains (I.convert c) (Xreal r) ->
  forall (X : I.type),
  approximates X (Xmask (Xreal r)) (const c).
Proof. by move=> c r Hcr X; split=>// ?. Qed.

Definition dummy : T := TM.const I.nai.

Theorem dummy_correct xi f :
  f Xnan = Xnan -> TM.approximates xi f dummy.
Proof.
move=> Hnan.
split=>//.
rewrite /dummy /approximates.
move=> Hne x.
by rewrite I.nai_correct.
Qed.

Definition var : T := Var.

Theorem var_correct :
  forall (X : I.type),
  approximates X id var.
Proof. by move=> *; split. Qed.

Definition eval (u : U) (Y X : I.type) (t : T) : I.type :=
  if I.subset X Y (* && Inot_empty X *) then
    let X0 := Imid Y in
    let tm := tm_helper1 u Y t in
    I.add u.1 (PolI.teval u.1 (RPA.approx tm) (I.sub u.1 X X0)) (RPA.error tm)
  else I.nai (* or I.whole ? *).

Theorem eval_correct :
  forall u (Y : I.type) f tf, approximates Y f tf ->
  forall (X : I.type),
  forall x, contains (I.convert X) x ->
  contains (I.convert (eval u Y X tf)) (f x).
Proof.
move=> u Y f tf Hf X x HXx.
rewrite /eval.
case HXY: I.subset; last by rewrite I.nai_correct.
move/I.subset_correct: (HXY) => HXY'.
(* case HneX: Inot_empty; last by rewrite I.nai_correct. *)
(* move/Inot_empty_correct in HneX. *)
have /= {Hf} := tm_helper1_correct u Hf.
move: (tm_helper1 u Y tf) => tm Htm.
have {Htm} [Hnan Hnil Htm] := Htm.
have HneY: not_empty (I.convert Y).
apply not_empty'E; exists x; exact: subset_contains HXY' _ _.
move/(_ HneY): Htm.
case => [/= Hzero Hsubset Hmain].
set c0 := I.convert_bound (I.midpoint Y).
have [|qx [Hsize Hcont Hdelta]] := Hmain c0.
  apply: Imid_contains.
  apply: not_empty'E.
  exists x.
  apply: subset_contains HXx.
  exact: I.subset_correct.
move/(_ x) in Hdelta.
apply I.subset_correct in HXY.
move/(_ (subset_contains _ _ HXY _ HXx)) in Hdelta.
have Hreal: f x <> Xnan /\ I.convert (RPA.error tm) <> IInan ->
  PolX.teval tt qx (FullXR.tsub tt x c0) =
  Xreal (proj_val (PolX.teval tt qx (FullXR.tsub tt x c0))).
  case=> Hfx HD.
  case Eqx : PolX.teval => [|r] //; [exfalso].
  rewrite Eqx [FullXR.tsub tt _ _]Xsub_Xnan_r /contains in Hdelta.
  by case: I.convert Hdelta HD.
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
rewrite Efx ED in Hreal.
rewrite Hreal //=.
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

Definition add_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let t' := pad2 u X (t1, t2) in
  let M1 := tm_helper1 u X t'.1 in
  let M2 := tm_helper1 u X t'.2 in
  Tm (TM_add u.1 M1 M2).

Definition add (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Const c1, Const c2 => Const (I.add u.1 c1 c2)
    | _, _ => add_slow u X t1 t2
  end.

Lemma add_slow_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xadd (f x) (g x)) (add_slow u Y tf tg).
Proof.
move=> u Y tf tg f g Hf Hg.
have [[Hnan Hnil H] [_ _ H']] := @pad2_correct u Y f g (tf, tg) Hf Hg.
split=>//.
by rewrite Hnan.
rewrite /add_slow.
set t' := pad2 u Y (tf, tg) in Hnil *.
rewrite /= /tmsize size_TM_add /=.
rewrite ![PolI.tsize _]tsize_tm_helper1.
case: t'.1 Hnil =>[c'| |t'1]; rewrite -lt0n ?maxSn //.
rewrite /not_nil /= -lt0n.
move=> H'1.
by rewrite -(ltn_predK H'1) maxSn.
move=> Hne; move/(_ Hne) in H; move/(_ Hne) in H'.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
red.
apply: TM_add_correct;
  first
    (rewrite ![PolI.tsize _]tsize_tm_helper1 size_pad2;
    case: pad2 (isTm_pad2 u Y (tf, tg)) => [[c|| tm][c'|| tm']] []; done);
  move: H H' {Hnil}; case: (pad2 _ _ _).1; case: (pad2 _ _ _).2 =>// *;
    try (apply: TM_const_correct =>//; exact: Imid_subset);
    apply TM_var_correct_cor =>//; (try apply: Imid_subset =>//);
    exists (Xreal v); done.
Qed.

Theorem add_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xadd (f x) (g x)) (add u Y tf tg).
Proof.
move=> u Y [cf| |tf] [cg| |tg] f g Hf Hg; try exact: add_slow_correct.
split=>//.
by case: Hf =>->.
case: Hf => _ _ H Hne; move/(_ Hne) in H.
red=> x; apply: I.add_correct=>//.
by case: Hg => _ _ H'; move/(_ Hne) in H'.
Qed.

Definition opp_slow (u : U) (X : I.type) (t : T) : T :=
  Tm (TM_opp (tm_helper1 u X t)).

Definition opp (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Const c => Const (I.neg c)
    | _ => opp_slow u X t
  end.

Lemma opp_slow_correct :
  forall u (Y : I.type) tf f,
  approximates Y f tf ->
  approximates Y (fun x => Xneg (f x)) (opp_slow u Y tf).
Proof.
move=> u Y tf f [Hnan Hnil Hmain].
split=>//.
by rewrite Hnan.
rewrite /opp_slow.
rewrite /= /tmsize size_TM_opp /=.
rewrite ![PolI.tsize _]tsize_tm_helper1.
by case: tf Hnil Hmain =>[c'| |tf'].
move=> Hne; move/(_ Hne) in Hmain.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
apply: TM_opp_correct.
case: tf Hmain {Hnil} => * //;
  try (apply: TM_const_correct =>//; exact: Imid_subset);
  apply TM_var_correct_cor =>//; (try apply: Imid_subset =>//);
  exists (Xreal v); done.
Qed.

Theorem opp_correct : forall u (Y : I.type) tf f,
  approximates Y f tf ->
  approximates Y (fun x => Xneg (f x)) (opp u Y tf).
Proof.
move=> u Y [cf| |tf] f [Hnan Hnil Hmain]; try exact: opp_slow_correct.
split=>//.
by rewrite Hnan.
move=> Hne; move/(_ Hne) in Hmain.
by red=> x; apply: I.neg_correct.
Qed.

Definition sub_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let t' := pad2 u X (t1, t2) in
  let M1 := tm_helper1 u X t'.1 in
  let M2 := tm_helper1 u X t'.2 in
  Tm (TM_sub u.1 M1 M2).

Definition sub (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Const c1, Const c2 => Const (I.sub u.1 c1 c2)
  (*| Var, Var => Const (I.fromZ 0)*)
    | _, _ => sub_slow u X t1 t2
  end.

Lemma sub_slow_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xsub (f x) (g x)) (sub_slow u Y tf tg).
Proof.
move=> u Y tf tg f g Hf Hg.
have [[Hnan Hnil H] [_ _ H']] := @pad2_correct u Y f g (tf, tg) Hf Hg.
split=>//.
by rewrite Hnan.
rewrite /sub_slow.
set t' := pad2 u Y (tf, tg) in Hnil *.
rewrite /= /tmsize size_TM_sub /=.
rewrite ![PolI.tsize _]tsize_tm_helper1.
case: t'.1 Hnil =>[c'| |t'1]; rewrite -lt0n ?maxSn //.
rewrite /not_nil /= -lt0n.
move=> H'1.
by rewrite -(ltn_predK H'1) maxSn.
move=> Hne; move/(_ Hne) in H; move/(_ Hne) in H'.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
red.
apply: TM_sub_correct;
  first
    (rewrite ![PolI.tsize _]tsize_tm_helper1 size_pad2;
    case: pad2 (isTm_pad2 u Y (tf, tg)) => [[c|| tm][c'|| tm']] []; done);
  move: H H' {Hnil}; case: (pad2 _ _ _).1; case: (pad2 _ _ _).2 =>// *;
    try (apply: TM_const_correct =>//; exact: Imid_subset);
    apply TM_var_correct_cor =>//; (try apply: Imid_subset =>//);
    exists (Xreal v); done.
Qed.

Theorem sub_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xsub (f x) (g x)) (sub u Y tf tg).
Proof.
move=> u Y [cf| |tf] [cg| |tg] f g Hf Hg; try exact: sub_slow_correct.
split=>//.
by case: Hf =>->.
case: Hf => _ _ H Hne; move/(_ Hne) in H.
red=> x; apply: I.sub_correct=>//.
by case: Hg => _ _ H'; move/(_ Hne) in H'.
Qed.

Definition mul_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let t' := pad2 u X (t1, t2) in
  let M1 := tm_helper1 u X t'.1 in
  let M2 := tm_helper1 u X t'.2 in
  let X0 := Imid X in
  let n := (tsize t'.1).-1 in
  Tm (TM_mul u.1 M1 M2 X0 X n).

Definition mul (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Const c1, Const c2 => Const (I.mul u.1 c1 c2)
    | _, _ => mul_slow u X t1 t2
  end.

Lemma mul_slow_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xmul (f x) (g x)) (mul_slow u Y tf tg).
Proof.
move=> u Y tf tg f g Hf Hg.
have [[Hnan Hnil H] [_ _ H']] := @pad2_correct u Y f g (tf, tg) Hf Hg.
split=>//.
by rewrite Hnan.
rewrite /mul_slow.
set t' := pad2 u Y (tf, tg) in Hnil *.
(* ... *)
move=> Hne; move/(_ Hne) in H; move/(_ Hne) in H'.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
apply TM_mul_correct=>//.
by exists (Xreal v).
(* . *)
rewrite /t' ![PolI.tsize _]tsize_tm_helper1.
have := isTm_pad2 u Y (tf, tg).
case: pad2=>//=.
by case=> [c1| |t1] b [].
(* . *)
rewrite /t' ![PolI.tsize _]tsize_tm_helper1 size_pad2.
have := isTm_pad2 u Y (tf, tg).
case: pad2=>//=.
by move=> a [c2| |t2] [].
(* . *)
move: Hnil.
rewrite lt0n /t' /not_nil.
have := isTm_pad2 u Y (tf, tg).
by case: pad2 => [[c1| |t1][c2| |t2]] [].
(* . *)
case: t'.1 H H'; case: t'.2 =>// *;
  try (apply: TM_const_correct =>//; exact: Imid_subset);
  apply TM_var_correct_cor =>//; (try apply: Imid_subset =>//);
  exists (Xreal v); done.
(* . *)
case: t'.1 H H'; case: t'.2 =>// *;
  try (apply: TM_const_correct =>//; exact: Imid_subset);
  apply TM_var_correct_cor =>//; (try apply: Imid_subset =>//);
  exists (Xreal v); done.
Qed.

Theorem mul_correct :
  forall u (Y : I.type) tf tg f g,
  approximates Y f tf -> approximates Y g tg ->
  approximates Y (fun x => Xmul (f x) (g x)) (mul u Y tf tg).
Proof.
move=> u Y [cf| |tf] [cg| |tg] f g Hf Hg; try exact: mul_slow_correct.
split=>//.
by case: Hf =>->.
case: Hf => _ _ H Hne; move/(_ Hne) in H.
red=> x; apply: I.mul_correct=>//.
by case: Hg => _ _ H'; move/(_ Hne) in H'.
Qed.

(* Naive version of exp

Definition exp (u : U) (X : I.type) (t : T) : T :=
  let X0 := Imid X in
  let tm := (tm_helper1 u X t) in
  let n := (tmsize tm).-1 in
  Tm (TM_comp u.1 (TM_exp u.1) (tm_helper1 u X t) X0 X n).
*)

Definition exp (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Const c => Const (I.exp u.1 c)
    | Var => let X0 := Imid X in Tm (TM_exp u.1 X0 X u.2)
    | Tm tm => let X0 := Imid X in let n := (tmsize tm).-1 in
      Tm (TM_comp u.1 (TM_exp u.1) tm X0 X n)
  end.

Theorem exp_correct :
  forall u (Y : I.type) f tf, approximates Y f tf ->
  approximates Y (fun x => Xexp (f x)) (exp u Y tf).
Proof.
move=> u Y f [c||tm] Hf.
- have [Hnan Hnil Hc] := Hf; split; [by rewrite Hnan|done|].
  red=> HneY x.
  apply: I.exp_correct.
  exact: Hc.
- have [Hnan Hnil Hid] := Hf; split=>//; first by rewrite Hnan.
  by rewrite /not_nil /tmsize /= PolI.tsize_trec1.
  simpl.
  move=> HneY; move/(_ HneY) in Hid.
  eapply TM_fun_eq.
  case=> [|x]; last by move=> *; rewrite Hid.
  by rewrite Hnan.
  apply: TM_exp_correct.
  exact: Imid_subset.
  apply not_empty_Imid in HneY.
  have [y Hy] := HneY; by exists (Xreal y).
- have [Hnan Hnil Htm] := Hf; split; first by rewrite Hnan.
  by rewrite /not_nil /exp /tmsize /exp size_TM_comp.
  move=> HneY; move/(_ HneY) in Htm.
  have [Hzero Hsubset Hmain] := Htm.
  have Hne' := not_empty_Imid HneY.
  have [m Hm] := Hne'.
  apply (TM_comp_correct u.1) =>//.
  + by exists (Xreal m).
  + have  [a [H H' H'']] := Hmain _ Hm.
    exists (PolX.tnth a 0).
    apply: H'.
    by rewrite /= -lt0n in Hnil.
  + rewrite /tmsize.
    rewrite /= /tmsize in Hnil.
    by case: PolI.tsize Hnil.
  + move=> *; split; last by rewrite PolI.tsize_trec1.
    exact: TM_exp_correct.
Save.

End TM.
