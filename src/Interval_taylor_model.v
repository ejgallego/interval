Require Import Reals ZArith.
Require Import Interval_interval.
Require Import Interval_xreal.
Require Import Interval_definitions.
Require Import Interval_generic.
Require Import Interval_specific_ops.
Require Import Interval_bigint_carrier.
Require Import Interval_interval_float.
Require Import Interval_interval_float_full.
Require Import interval_compl.
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq bigop.
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

(** * Auxiliary lemmas on natural numbers *)

Lemma ltn_leq_pred m n : m < n -> m <= n.-1.
Proof. by move=> H; rewrite -ltnS (ltn_predK H). Qed.

Lemma maxnS (m n : nat) : 0 < maxn m n.+1.
Proof. by case: m =>[//|m]; rewrite maxnSS. Qed.

Lemma maxSn (m n : nat) : 0 < maxn m.+1 n.
Proof. by rewrite maxnC maxnS. Qed.

(** * Parameterized Module for Taylor Models *)

Module TM (I : IntervalOps) <: UnivariateApprox I.
(* Erik: We might add a Boolean counterpart of not_empty in IntervalOps *)

(** ** Load the CoqApprox modules *)

Module PolX := ExactSeqPolyMonomUp FullXR.
Module Link := LinkSeqPolyMonomUp I.
Module PolI := SeqPolyMonomUpInt I.
Module Import TMI := TaylorModel I PolI PolX Link.

(** ** Main type definitions *)

Inductive t_ := Dummy | Const of I.type | Var | Tm of RPA.rpa.

Definition T := t_.

Definition U := (I.precision * nat)%type.

(** ** Auxiliary material

The need for using a padding function (see [pad2] below) is due to the
current version of the correctness theorems of CoqApprox *)

Definition isDummy (t : T) : bool := if t is Dummy then true else false.
(* Definition isConst (t : T) : bool := if t is Const _ then true else false. *)
Definition isTm (t : T) : bool := if t is Tm _ then true else false.

Definition unat (u : U) (n : nat) := (u.1, n).

Definition tmsize (tm : RPA.rpa) := PolI.tsize (RPA.approx tm).

Definition tsize (t : T) : nat :=
  match t with
    | Dummy | Const _ | Var => 0
    | Tm tm => tmsize tm
  end.

Definition tm_helper1 (u : U) X (t : T) : RPA.rpa :=
  match t with
    | Dummy => TM_const u.1 I.nai X u.2
    | Const c => let X0 := Imid X in TM_cst u.1 c X0 X u.2
    | Var => let X0 := Imid X in (TM_var u.1 X0 X u.2)
    | Tm tm => tm (* ignore u, X in this branch *)
  end.

Definition tm_helper2pad (u : U) X (t : T) :=
  match t with
    | Dummy => TM_const u.1 I.nai X u.2
    | Const c => let X0 := Imid X in (TM_cst u.1 c X0 X u.2)
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
by rewrite /tsize /tmsize size_TM_const leq_max ltnSn orbC.
by move=> c; rewrite /tsize /tmsize size_TM_cst leq_max ltnSn orbC.
by rewrite /tsize /tmsize /= PolI.tsize_trec2.
move=> r /=; exact: leq_maxl.
Qed.

Lemma tsize_tm_helper1 u X t :
  tmsize (tm_helper1 u X t) = if t is Tm _ then tsize t else u.2.+1.
Proof.
case: t => [|c||tm] //.
  by rewrite /tmsize size_TM_const.
  by rewrite /tmsize size_TM_cst.
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
by rewrite /tsize /tmsize size_TM_const (appP idP maxn_idPr).
by move=> c; rewrite /tsize /tmsize size_TM_cst (appP idP maxn_idPr).
by rewrite /tsize /tmsize /= PolI.tsize_trec2 (appP idP maxn_idPr) //.
by move =>  [pol delta]; rewrite /tsize /tmsize /= PolI.tsize_set_nth maxnC.
Qed.

Corollary tsize_tm_helper2pad u X t :
  tsize t <= (u.2).+1 ->
  tmsize (tm_helper2pad u X t) = (u.2).+1.
Proof. move=> Hn; rewrite tsize_tm_helper2pad_maxn //; exact/maxn_idPr. Qed.

Definition not_nil (tf : T) : bool :=
  match tf with
    | Dummy => true
    | Const _ => true
    | Var => true
    | Tm tm => tmsize tm != 0
  end.

Lemma not_nilF (t : T) :
  not_nil t = false -> tsize t = 0.
Proof. by case: t =>// tm; rewrite /not_nil /=; case: tmsize. Qed.

(** ** Define the main validity predicate *)

Definition approximates (X : I.type) (tf : T) (f:ExtendedR->ExtendedR) : Prop :=
  let X0 := Imid X in
  [/\ f Xnan = Xnan,
    not_nil tf &
    match tf with
      | Dummy => True
      | Const c => is_const f X c
      | Var =>
        forall x : R, contains (I.convert X) (Xreal x) ->
        f (Xreal x) = Xreal x
      | Tm tm =>
        not_empty (I.convert X) ->
        i_validTM (I.convert X0) (I.convert X) tm f
    end].

Theorem approximates_ext f g xi t :
  (forall x, f x = g x) ->
  approximates xi t f -> approximates xi t g.
Proof.
move=> Hfg [Hnan Hcont Hmain].
split=>//.
by rewrite -Hfg.
case: t Hmain {Hcont} =>[|c| |tm] Hmain; rewrite -?Hfg //.
exact: is_const_ext_weak Hfg _.
by move=> *; rewrite -Hfg; apply: Hmain.
move=> Hne; move/(_ Hne): Hmain.
apply TM_fun_eq.
move=> *; exact: Hfg.
Qed.

Lemma tm_helper1_correct u Y tf f :
  approximates Y tf f ->
  approximates Y (Tm (tm_helper1 u Y tf)) f.
Proof.
case: tf =>[|c||tm]; rewrite /approximates //; case => Hnan ? H; split=>//=.
- by rewrite /tmsize size_TM_const.
  move=> ?; apply: TM_const_correct_strong.
  exact: not_empty_Imid.
  exact: Imid_subset.
  by rewrite I.nai_correct.
- by rewrite /tmsize size_TM_cst.
- move=> Hne.
  apply TM_cst_correct_strong =>//.
  exact: Imid_subset.
  apply: not_empty'E.
  exact: not_empty_Imid.
- by rewrite /tmsize PolI.tsize_trec2.
- move=> Hne.
  apply: TM_var_correct_strong=>//.
    exact: Imid_subset.
  apply not_empty_Imid in Hne.
  by have [v Hv] := Hne; exists (Xreal v).
Qed.

Lemma tm_helper2pad_correct u X tf f :
  approximates X tf f ->
  tsize tf <= (u.2) ->
  approximates X (Tm  (tm_helper2pad u X tf)) f.
Proof.
case: tf => [|c||[pol delta]]; rewrite /approximates /=.
- case=> Hnan _ _; split=>//.
  by rewrite /tmsize -lt0n size_TM_const ltnS //.
  move=> Hne.
  apply TM_const_correct_strong=>//.
  exact: not_empty_Imid.
  exact: Imid_subset.
  by rewrite I.nai_correct.
- case=> Hnan _ H; split=>//.
  by rewrite /tmsize -lt0n size_TM_cst ltnS //.
  move=> Hne.
  apply TM_cst_correct_strong=>//.
  exact: Imid_subset.
  apply: not_empty'E; exact: not_empty_Imid.
- case=> Hnan Hnil H Hu; split=>//.
  by rewrite /tmsize -lt0n PolI.tsize_trec2 ltnS //.
  move=> Hne.
  apply: (TM_fun_eq_real (f := id)).
    by move=> *; symmetry; apply: H.
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

Theorem pad2_correct u X f g t :
  approximates X t.1 f -> approximates X t.2 g ->
  let t' := pad2 u X t in
  approximates X t'.1 f /\ approximates X t'.2 g.
Proof.
move: t => [t1 t2] Hf Hg.
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

Theorem size_pad2 u X t :
  let t' := pad2 u X t in
  tsize t'.2 = tsize t'.1.
Proof.
move: t => [t1 t2] /=.
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
case: t2 Ene E2 =>[|c2| |t2] Ene E2 //.
(* . *)
case: t1 Ene E1 =>[| c1| |t1] Ene E1 //.
rewrite -/(is_true _) -lt0n in Ene.
by rewrite /= (ltn_predK Ene).
(* . *)
case: t1 Ene E1 =>[|c1| |t1] Ene E1 //.
rewrite -/(is_true _) -lt0n in Ene.
by rewrite /= (ltn_predK Ene).
(* . *)
case: t1 Ene E1 =>[|c1| |t1] Ene E1 //.
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
case: t1 Ene E1 =>[|c1| |t1] Ene E1 //.
(* . *)
case: t2 Ene E2 =>[|c2| |t2] Ene E2 //.
rewrite -/(is_true _) -lt0n in Ene.
by rewrite /= (ltn_predK Ene).
(* . *)
case: t2 Ene E2 =>[|c2| |t2] Ene E2 //.
rewrite -/(is_true _) -lt0n in Ene.
by rewrite /= (ltn_predK Ene).
(* . *)
case: t2 Ene E2 =>[|c2| |t2] Ene E2 //.
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

(** A "confidence" lemma (not used elsewhere in the development) *)
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
(*================*)
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
move=> r _ _ _ /=; exact: leqSpred.
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

Theorem isTm_pad2 u X t :
  let t' := pad2 u X t in
  isTm t'.1 /\ isTm t'.2.
Proof.
move: t => [t1 t2] /=.
by case E1: (isTm t1); case E2: (isTm t2)=>//;
  case: (nat_compare_spec (tsize t1) (tsize t2));
  case: (not_nil t1); case: (not_nil t2)=>//.
Qed.

(** ** Main definitions and correctness claims *)

Definition const : I.type -> T := Const.

Theorem const_correct (c : I.type) (r : R) :
  contains (I.convert c) (Xreal r) ->
  forall (X : I.type),
  approximates X (const c) (Xmask (Xreal r)).
Proof. move=> Hcr X; split=>//=; by exists (Xreal r). Qed.

Definition dummy : T := Dummy.

Theorem dummy_correct xi f :
  f Xnan = Xnan -> TM.approximates xi dummy f.
Proof. done. Qed.

Definition var : T := Var.

Theorem var_correct (X : I.type) :
  approximates X var id.
Proof. done. Qed.

(*
Definition eval_slow (u : U) (t : T) (Y X : I.type) : I.type :=
  if I.subset X Y (* && Inot_empty X *) then
    let X0 := Imid Y in
    let tm := tm_helper1 u Y t in
    I.add u.1 (PolI.teval u.1 (RPA.approx tm) (I.sub u.1 X X0)) (RPA.error tm)
  else I.nai (* or I.whole ? *).
*)

Definition eval (u : U) (t : T) (Y X : I.type) : I.type :=
  if I.subset X Y then
  match t with
  | Dummy => I.nai
  | Const c => I.mask c X (* the need for I.mask comes from I.extension below *)
  | Var => X
  | Tm tm =>
    let X0 := Imid Y in
    let tm := tm_helper1 u Y t in
    I.add u.1
      (PolI.teval u.1 (RPA.approx tm) (I.sub u.1 X X0))
      (RPA.error tm)
  end
  else I.nai.

Theorem eval_correct u (Y : I.type) tf f :
  approximates Y tf f -> I.extension f (eval u tf Y).
Proof.
move=> Hf X x Hx.
rewrite /eval.
case HXY: I.subset; last by rewrite I.nai_correct.
move/I.subset_correct: (HXY) => Hsubset.
case: tf Hf => [ |c| |tm].
(* Dummy *)
by rewrite I.nai_correct.
(* Const *)
case.
move=> Hnan _ [y Hy1 Hy2].
case: x Hx =>[|x] Hx.
  move/contains_Xnan in Hx.
  have H0 : contains (I.convert Y) (Xreal 0).
  by apply: subset_contains Hsubset _ _; rewrite Hx.
  rewrite Hnan.
  have->: Xnan = Xmask (f (Xreal 0)) Xnan by [].
  apply: I.mask_correct =>//.
  by rewrite Hy2.
  by rewrite Hx.
have->: f (Xreal x) = Xmask (f (Xreal x)) (Xreal x) by [].
apply: I.mask_correct=>//.
rewrite Hy2 //.
exact: subset_contains Hsubset _ _.
(* Var *)
case.
case: x Hx =>[|x] Hx; first by move->.
move=> _ _ /(_ x) ->//.
exact: subset_contains Hsubset _ _.
(* Tm *)
move=> Hf.
have /= {Hf} := tm_helper1_correct u Hf=> Htm.
have {Htm} [Hnan Hnil Htm] := Htm.
have HneY: not_empty (I.convert Y).
apply not_emptyE; exists x; exact: subset_contains Hsubset _ _.
move/(_ HneY): Htm.
case => [/= Hzero _ Hmain].
set c0 := I.convert_bound (I.midpoint Y).
have [|qx [Hsize Hcont Hdelta]] := Hmain c0.
  apply: Imid_contains.
  apply: not_emptyE.
  exists x.
  apply: subset_contains Hx.
  exact: I.subset_correct.
move/(_ x) in Hdelta.
apply I.subset_correct in HXY.
move/(_ (subset_contains _ _ HXY _ Hx)) in Hdelta.
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
apply: not_emptyE.
exists x.
exact: subset_contains Hx.
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
apply: not_emptyE.
exists x.
exact: subset_contains Hx.
Qed.

Definition add_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let t' := pad2 u X (t1, t2) in
  let M1 := tm_helper1 u X t'.1 in
  let M2 := tm_helper1 u X t'.2 in
  Tm (TM_add u.1 M1 M2).

Definition add (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Dummy, _ | _, Dummy => Dummy
    | Const c1, Const c2 => Const (I.add u.1 c1 c2)
    | _, _ => add_slow u X t1 t2
  end.

Lemma add_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (add_slow u Y tf tg) (fun x => Xadd (f x) (g x)).
Proof.
move=> Hf Hg.
have [[Hnan Hnil H] [_ _ H']] := @pad2_correct u Y f g (tf, tg) Hf Hg.
split=>//.
by rewrite Hnan.
rewrite /add_slow.
set t' := pad2 u Y (tf, tg) in Hnil *.
rewrite /= /tmsize size_TM_add /=.
rewrite ![PolI.tsize _]tsize_tm_helper1.
case: t'.1 Hnil =>[|c'| |t'1]; rewrite -lt0n ?maxSn //.
rewrite /not_nil /= -lt0n.
move=> H'1.
by rewrite -(ltn_predK H'1) maxSn.
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
apply: TM_add_correct;
  first
    (rewrite ![PolI.tsize _]tsize_tm_helper1 size_pad2;
    case: pad2 (isTm_pad2 u Y (tf, tg)) => [[|c||tm][|c'||tm']] []; done);
  move: H H' {Hnil}; case: (pad2 _ _ _).1; case: (pad2 _ _ _).2 =>// *;
  try (apply: TM_const_correct_strong;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem add_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (add u Y tf tg) (fun x => Xadd (f x) (g x)).
Proof.
move: tf tg => [|cf| |tf] [|cg| |tg] Hf Hg;
  case: (Hf) => Hfnan _ _;
  try exact: add_slow_correct;
  try by simpl; apply: dummy_correct; rewrite Hfnan.
split=>//; first by rewrite Hfnan.
case: Hf => _ _ [yf Hyf1 Hyf2].
case: Hg => _ _ [yg Hyg1 Hyg2].
exists (Xadd yf yg); first exact: I.add_correct.
by move=> x Hx; rewrite Hyf2 // Hyg2.
Qed.

Definition opp_slow (u : U) (X : I.type) (t : T) : T :=
  Tm (TM_opp (tm_helper1 u X t)).

Definition opp (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Dummy => Dummy
    | Const c => Const (I.neg c)
    | _ => opp_slow u X t
  end.

Lemma opp_slow_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (opp_slow u Y tf) (fun x => Xneg (f x)).
Proof.
move=> [Hnan Hnil Hmain].
split=>//.
by rewrite Hnan.
rewrite /opp_slow.
rewrite /= /tmsize size_TM_opp /=.
rewrite ![PolI.tsize _]tsize_tm_helper1.
by case: tf Hnil Hmain =>[|c'| |tf'].
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
apply: TM_opp_correct.
case: tf Hmain {Hnil} => * //;
  try (apply: TM_const_correct_strong;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem opp_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (opp u Y tf) (fun x => Xneg (f x)).
Proof.
move: tf => [|cf| |tf] [Hnan Hnil Hmain]; try exact: opp_slow_correct.
by simpl; apply: dummy_correct; rewrite Hnan.
split=>//; first by rewrite Hnan.
have [y Hy1 Hy2] := Hmain.
exists (Xneg y); first exact: I.neg_correct.
by move=> x Hx; rewrite Hy2.
Qed.

Definition sub_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let t' := pad2 u X (t1, t2) in
  let M1 := tm_helper1 u X t'.1 in
  let M2 := tm_helper1 u X t'.2 in
  Tm (TM_sub u.1 M1 M2).

Definition sub (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Dummy, _ | _, Dummy => Dummy
    | Const c1, Const c2 => Const (I.sub u.1 c1 c2)
  (*| Var, Var => Const (I.fromZ 0) : FIXME *)
    | _, _ => sub_slow u X t1 t2
  end.

Lemma sub_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (sub_slow u Y tf tg) (fun x => Xsub (f x) (g x)).
Proof.
move=> Hf Hg.
have [[Hnan Hnil H] [_ _ H']] := @pad2_correct u Y f g (tf, tg) Hf Hg.
split=>//.
by rewrite Hnan.
rewrite /sub_slow.
set t' := pad2 u Y (tf, tg) in Hnil *.
rewrite /= /tmsize size_TM_sub /=.
rewrite ![PolI.tsize _]tsize_tm_helper1.
case: t'.1 Hnil =>[|c'| |t'1]; rewrite -lt0n ?maxSn //.
rewrite /not_nil /= -lt0n.
move=> H'1.
by rewrite -(ltn_predK H'1) maxSn.
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
red.
apply: TM_sub_correct;
  first
    (rewrite ![PolI.tsize _]tsize_tm_helper1 size_pad2;
    case: pad2 (isTm_pad2 u Y (tf, tg)) => [[|c|| tm][|c'|| tm']] []; done);
  move: H H' {Hnil}; case: (pad2 _ _ _).1; case: (pad2 _ _ _).2 =>// *;
  try (apply: TM_const_correct_strong;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem sub_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (sub u Y tf tg) (fun x => Xsub (f x) (g x)).
Proof.
move: tf tg => [|cf| |tf] [|cg| |tg] Hf Hg;
  case: (Hf) => Hfnan _ _;
  try exact: sub_slow_correct;
  try by simpl; apply: dummy_correct; rewrite Hfnan.
split=>//; first by rewrite Hfnan.
case: Hf => _ _ [yf Hyf1 Hyf2].
case: Hg => _ _ [yg Hyg1 Hyg2].
exists (Xsub yf yg); first exact: I.sub_correct.
by move=> x Hx; rewrite Hyf2 // Hyg2.
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
    | Dummy, _ | _, Dummy => Dummy
    | Const c1, Const c2 => Const (I.mul u.1 c1 c2)
    | Const c1, _ => Tm (TM_mul_mixed u.1 c1 (tm_helper1 u X t2) )
    | _, Const c2 => Tm (TM_mul_mixed u.1 c2 (tm_helper1 u X t1) )
    | _, _ => mul_slow u X t1 t2
  end.

Lemma mul_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (mul_slow u Y tf tg) (fun x => Xmul (f x) (g x)).
Proof.
move=> Hf Hg.
have [[Hnan Hnil H] [_ _ H']] := @pad2_correct u Y f g (tf, tg) Hf Hg.
split=>//.
by rewrite Hnan.
rewrite /mul_slow.
set t' := pad2 u Y (tf, tg) in Hnil *.
(* ... *)
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
apply TM_mul_correct=>//.
by exists (Xreal v).
(* . *)
rewrite /t' ![PolI.tsize _]tsize_tm_helper1.
have := isTm_pad2 u Y (tf, tg).
case: pad2=>//=.
by case=> [|c1| |t1] b [].
(* . *)
rewrite /t' ![PolI.tsize _]tsize_tm_helper1 size_pad2.
have := isTm_pad2 u Y (tf, tg).
case: pad2=>//=.
by move=> a [|c2| |t2] [].
(* . *)
move: Hnil.
rewrite lt0n /t' /not_nil.
have := isTm_pad2 u Y (tf, tg).
by case: pad2 => [[|c1| |t1][|c2| |t2]] [].
(* . *)
case: t'.1 H H'; case: t'.2 =>// *;
  try (apply: TM_const_correct_strong;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
(* . *)
case: t'.1 H H'; case: t'.2 =>// *;
  try (apply: TM_const_correct_strong;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem mul_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (mul u Y tf tg) (fun x => Xmul (f x) (g x)).
Proof.
move: tf tg => [|cf| |tf] [|cg| |tg] Hf Hg;
  case: (Hf) => Hfnan _ _;
  try exact: mul_slow_correct;
  try by simpl; apply: dummy_correct; rewrite Hfnan.
(* Const . Const *)
split=>//; first by rewrite Hfnan.
case: Hf => _ _ [yf Hyf1 Hyf2].
case: Hg => _ _ [yg Hyg1 Hyg2].
exists (Xmul yf yg); first exact: I.mul_correct.
by move=> x Hx; rewrite Hyf2 // Hyg2.
(* Const . Var *)
have [Hnan1 Hnil1 H1] := Hf;
have [Hnan2 Hnil2 H2] := Hg;
split=>//;
  first (by rewrite Hnan1);
  first (by rewrite /= /tmsize size_TM_mul_mixed size_TM_var);
  red=>Hne.
apply: TM_mul_mixed_correct_strong =>//.
  apply: not_empty'E; exact: not_empty_Imid.
apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
apply: not_empty'E; exact: not_empty_Imid.
(* Const . Tm *)
have [Hnan1 Hnil1 H1] := Hf;
have [Hnan2 Hnil2 H2] := Hg;
split=>//;
  first (by rewrite Hnan1);
  first (by rewrite /= /tmsize size_TM_mul_mixed (*size_TM_var*));
  red=>Hne.
apply: TM_mul_mixed_correct_strong =>//.
  apply: not_empty'E; exact: not_empty_Imid.
exact: H2.
(* Var . Const *)
have [Hnan1 Hnil1 H1] := Hf;
have [Hnan2 Hnil2 H2] := Hg;
split=>//;
  first (by rewrite Hnan1);
  first (by rewrite /= /tmsize size_TM_mul_mixed size_TM_var);
  red=>Hne.
apply: TM_fun_eq (fun x _ => XmulC (g x) (f x)) _.
apply: TM_mul_mixed_correct_strong =>//.
  apply: not_empty'E; exact: not_empty_Imid.
apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
apply: not_empty'E; exact: not_empty_Imid.
(* Tm . Const *)
have [Hnan1 Hnil1 H1] := Hf;
have [Hnan2 Hnil2 H2] := Hg;
split=>//;
  first (by rewrite Hnan1);
  first (by rewrite /= /tmsize size_TM_mul_mixed (*size_TM_var*));
  red=>Hne.
apply: TM_fun_eq (fun x _ => XmulC (g x) (f x)) _.
apply: TM_mul_mixed_correct_strong =>//.
  apply: not_empty'E; exact: not_empty_Imid.
exact: H1.
Qed.

Definition div_slow (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  let t' := pad2 u X (t1, t2) in
  let M1 := tm_helper1 u X t'.1 in
  let M2 := tm_helper1 u X t'.2 in
  let X0 := Imid X in
  let n := (tsize t'.1).-1 in
  Tm (TM_div u.1 M1 M2 X0 X n).

Definition div (u : U) (X : I.type) (t1 : T) (t2 : T) : T :=
  match t1, t2 with
    | Dummy, _ | _, Dummy => Dummy
    | Const c1, Const c2 => Const (I.div u.1 c1 c2)
    | _, Const c2 => Tm (TM_div_mixed_r u.1 (tm_helper1 u X t1) c2)
  (*| Var, Var => Const (I.fromZ 1) : FIXME *)
    | _, _ => div_slow u X t1 t2
  end.

Lemma div_slow_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (div_slow u Y tf tg) (fun x => Xdiv (f x) (g x)).
Proof.
move=> Hf Hg.
have [[Hnan Hnil H] [Hnan' _ H']] := @pad2_correct u Y f g (tf, tg) Hf Hg.
split=>//.
by rewrite Hnan.
rewrite /div_slow.
set t' := pad2 u Y (tf, tg) in Hnil *.
(* ... *)
move=> Hne.
have Hne' : not_empty (I.convert (Imid Y)) by apply not_empty_Imid.
have [v Hv] := Hne'.
apply TM_div_correct=>//.
by exists (Xreal v).
(* . *)
rewrite /t' ![PolI.tsize _]tsize_tm_helper1.
have := isTm_pad2 u Y (tf, tg).
case: pad2=>//=.
by case=> [|c1| |t1] b [].
(* . *)
rewrite /t' ![PolI.tsize _]tsize_tm_helper1 size_pad2.
have := isTm_pad2 u Y (tf, tg).
case: pad2=>//=.
by move=> a [|c2| |t2] [].
(* . *)
move: Hnil.
rewrite lt0n /t' /not_nil.
have := isTm_pad2 u Y (tf, tg).
by case: pad2 => [[|c1| |t1][|c2| |t2]] [].
(* . *)
case: t'.1 H H'; case: t'.2 =>// *;
  try (apply: TM_const_correct_strong;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
(* . *)
case: t'.1 H H'; case: t'.2 =>// *;
  try (apply: TM_const_correct_strong;
    by [exists v|exact: Imid_subset|rewrite I.nai_correct]);
  try (apply: TM_cst_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  try (apply: TM_var_correct_strong =>//;
    by [exact: Imid_subset|exists (Xreal v)]);
  by auto 2.
Qed.

Theorem div_correct u (Y : I.type) tf tg f g :
  approximates Y tf f -> approximates Y tg g ->
  approximates Y (div u Y tf tg) (fun x => Xdiv (f x) (g x)).
Proof.
move: tf tg => [|cf| |tf] [|cg| |tg] Hf Hg;
  case: (Hf) => Hfnan _ _;
  try exact: div_slow_correct;
  try by simpl; apply: dummy_correct; rewrite Hfnan.
(* Const . Const *)
split=>//; first by rewrite Hfnan.
case: Hf => _ _ [yf Hyf1 Hyf2].
case: Hg => _ _ [yg Hyg1 Hyg2].
exists (Xdiv yf yg); first exact: I.div_correct.
by move=> x Hx; rewrite Hyf2 // Hyg2.
(* Var . Const *)
have [Hnan1 Hnil1 H1] := Hf;
have [Hnan2 Hnil2 H2] := Hg;
split=>//;
  first (by rewrite Hnan1);
  first (by rewrite /= /tmsize size_TM_div_mixed_r size_TM_var);
  red=>Hne.
apply: TM_div_mixed_r_correct_strong =>//.
  apply: not_empty'E; exact: not_empty_Imid.
apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
apply: not_empty'E; exact: not_empty_Imid.
(* Const . Tm *)
have [Hnan1 Hnil1 H1] := Hf;
have [Hnan2 Hnil2 H2] := Hg;
split=>//;
  first (by rewrite Hnan1);
  first (by rewrite /= /tmsize size_TM_div_mixed_r);
  red=>Hne.
apply: TM_div_mixed_r_correct_strong =>//.
  apply: not_empty'E; exact: not_empty_Imid.
exact: H1.
Qed.

Definition abs (u : U) (X : I.type) (t : T) : T :=
  if isDummy t then Dummy else
  let e := eval u t X X in
  match I.sign_large e with
  | Xeq | Xgt => t
  | Xlt => opp u X t
  | Xund => Tm (TM_const u.1 (I.abs e) X u.2)
  end.

Lemma Isign_large_Xabs (u : U) (tf : T) (Y X : I.type) f :
  approximates Y tf f ->
  match I.sign_large (eval u tf Y X) with
    | Xeq =>
      forall x, contains (I.convert X) x ->
      Xabs (f x) = f x (* weak but sufficient *)
    | Xgt =>
      forall x, contains (I.convert X) x ->
      Xabs (f x) = f x
    | Xlt =>
      forall x, contains (I.convert X) x ->
      Xabs (f x) = Xneg (f x)
    | Xund => True
  end.
Proof.
case=> [Hnan Hnil Hmain].
case: I.sign_large (I.sign_large_correct (eval u tf Y X)) =>//.
- move=> H x Hx.
  rewrite (H (f x)) /= ?Rabs_R0 //.
  exact: eval_correct.
- move=> H x Hx.
  set fx := f x.
  have [|Hfx Hsign] := H fx; first exact: eval_correct.
  rewrite /Xabs Hfx /=; congr Xreal.
  by rewrite Rabs_left1.
move=> H x Hx.
set fx := f x.
have [|Hfx Hsign] := H fx; first exact: eval_correct.
rewrite /Xabs Hfx /=; congr Xreal.
by rewrite Rabs_right; auto with real.
Qed.

Lemma not_empty_dec (X : interval) : {not_empty X} + {~ not_empty X}.
Proof. (* without ssr tactics *)
case X.
  left.
  now exists R0.
intros l u; destruct l as [|l]; destruct u as [|u].
now left; exists R0.
now left; exists u; split; trivial; apply Rle_refl.
now left; exists l; split; trivial; apply Rle_refl.
destruct (Rle_lt_dec l u) as [H|H].
now left; exists l; split; trivial; apply Rle_refl.
right; intros K.
destruct K as [x [H1 H2]].
now apply Rle_not_lt with (1 := Rle_trans _ _ _ H1 H2).
Defined.

Local Ltac byp a b := move=> x Hx; rewrite a //; exact: b.
Local Ltac foo :=
  by move=> Hne; apply: TM_const_correct_strong;
  [ exact: not_empty_Imid | exact: Imid_subset
  | move=> x Hx; apply: I.abs_correct; exact: eval_correct].

Theorem abs_correct u (Y : I.type) tf f :
  approximates Y tf f ->
  approximates Y (abs u Y tf) (fun x => Xabs (f x)).
Proof.
move=> Hf; case: (Hf) => [Hnan Hnil Hmain].
rewrite /abs.
case E: (isDummy tf); first by split; rewrite 1?Hnan.
split.
- by rewrite Hnan.
- case: I.sign_large=>//.
    rewrite /opp /=.
    case: tf Hf Hnil {Hmain E} => [| | |tf] Hf //=.
      rewrite /tmsize size_TM_opp.
      by rewrite size_TM_var.
    by rewrite /tmsize size_TM_opp.
  by rewrite /not_nil /tmsize size_TM_const.
case: I.sign_large (@Isign_large_Xabs u tf Y Y f Hf) => Habs;
  case: tf Hf Hnil Hmain Habs {E} => [|cf| |tf] Hf Hnil Hmain Habs //.
- have [[|y] Hy1 Hy2] := Hmain;
    first (by exists Xnan =>//; move=> x Hx; rewrite Hy2);
    have [[z Hz]|H] := not_empty_dec (I.convert Y);
    by exists (Xreal y); [| move=> x Hx; rewrite Habs // Hy2].
- byp Habs Hmain.
- move=> Hne; move: (Hmain Hne); apply: TM_fun_eq_real;
  byp Habs Hmain.
- have [[|y] Hy1 Hy2] := Hmain;
    first (by
      exists (Xneg Xnan); first exact: I.neg_correct; move=> x Hx; rewrite Hy2);
    have [[z Hz]|H] := not_empty_dec (I.convert Y);
    exists (Xneg (Xreal y));
    by [exact: I.neg_correct | move=> x Hx; rewrite Habs // Hy2].
- red=> Hne.
  apply: (@TM_fun_eq_real (fun x => Xneg (f x))).
  move=> *; symmetry; exact: Habs.
  apply: TM_opp_correct.
  apply: TM_var_correct_strong =>//.
  exact: Imid_subset.
  apply Imid_contains in Hne.
  by eexists; apply Hne.
- red=> Hne.
  apply: (@TM_fun_eq_real (fun x => Xneg (f x))).
  move=> *; symmetry; exact: Habs.
  apply: TM_opp_correct.
  exact: Hmain.
- have [[|y] Hy1 Hy2] := Hmain;
    first (by exists Xnan =>//; move=> x Hx; rewrite Hy2);
    have [[z Hz]|H] := not_empty_dec (I.convert Y);
    by exists (Xreal y); [| move=> x Hx; rewrite Habs // Hy2].
- byp Habs Hmain.
- move=> Hne; move: (Hmain Hne); apply: TM_fun_eq_real; byp Habs Hmain.
- foo.
- foo.
- foo.
- foo.
Qed.

(** ** Generic implementation of basic functions *)

Definition fun_gen
  (fi : I.precision -> I.type -> I.type)
  (ftm : I.precision -> TM_type)
  (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Dummy => Dummy
    | Const c => Const (fi u.1 c)
    | Var => let X0 := Imid X in Tm (ftm u.1 X0 X u.2)
    | Tm tm => let X0 := Imid X in let n := (tmsize tm).-1 in
      Tm (TM_comp u.1 (ftm u.1) tm X0 X n)
  end.

Lemma fun_gen_correct
  (fi : I.precision -> I.type -> I.type)
  (ftm : I.precision -> TM_type)
  (fx : ExtendedR -> ExtendedR)
  (ft := fun_gen fi ftm) :
  fx Xnan = Xnan ->
  (forall prec : I.precision, I.extension fx (fi prec)) ->
  (forall prec X0 X n, tmsize (ftm prec X0 X n) = n.+1) ->
  (forall prec X0 X n,
    subset (I.convert X0) (I.convert X) ->
    (exists t : ExtendedR, contains (I.convert X0) t) ->
    i_validTM (I.convert X0) (I.convert X) (ftm prec X0 X n) fx) ->
  forall (u : U) (X : I.type) (tf : T) (f : ExtendedR -> ExtendedR),
  approximates X tf f ->
  approximates X (ft u X tf) (fun x => fx (f x)).
Proof.
move=> Hpro Hext Hsiz Hvalid u X [|c| |tm] f [Hnan Hnil Hmain].
- by apply: dummy_correct; rewrite Hnan Hpro.
- split; [by rewrite Hnan|done|simpl].
  have [y Hy1 Hy2] := Hmain.
  exists (fx y); first exact: Hext.
  by move=> x Hx; rewrite Hy2.
- split=>//; first by rewrite Hnan.
  by rewrite /not_nil /ft /fun_gen /= Hsiz.
  simpl.
  move=> HneY.
  eapply TM_fun_eq.
  case=> [|x]; last by move=> *; rewrite Hmain.
  by rewrite Hnan.
  apply: Hvalid.
  exact: Imid_subset.
  apply not_empty_Imid in HneY.
  have [y Hy] := HneY; by exists (Xreal y).
- split; first by rewrite Hnan.
  by rewrite /not_nil /ft /fun_gen /tmsize size_TM_comp.
  move=> HneY; move/(_ HneY) in Hmain.
  have [Hzero Hsubset Htm] := Hmain.
  have Hne' := not_empty_Imid HneY.
  have [m Hm] := Hne'.
  apply (TM_comp_correct u.1) =>//.
  + by exists (Xreal m).
  + rewrite /tmsize.
    rewrite /= /tmsize in Hnil.
    by case: PolI.tsize Hnil.
  + move=> *; split; first exact: Hvalid.
    by rewrite -/(tmsize _) Hsiz.
Qed.

(*
Definition inv (u : U) (X : I.type) (t : T) : T :=
  match t with
    | Const c => Const (I.inv u.1 c)
    | Var => let X0 := Imid X in Tm (TM_inv u.1 X0 X u.2)
    | Tm tm => let X0 := Imid X in let n := (tmsize tm).-1 in
      Tm (TM_inv_comp u.1 tm X0 X n)
  end.
*)

Definition inv := Eval hnf in fun_gen I.inv TM_inv.

Theorem inv_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (inv u Y tf) (fun x => Xinv (f x)).
Proof.
apply: fun_gen_correct =>//.
exact: I.inv_correct.
by move=>*; rewrite /tmsize PolI.tsize_trec1. (* TODO : refactor *)
exact: TM_inv_correct.
Qed.

Definition sqrt := Eval hnf in fun_gen I.sqrt TM_sqrt.

Theorem sqrt_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (sqrt u Y tf) (fun x => Xsqrt (f x)).
Proof.
apply: fun_gen_correct =>//.
exact: I.sqrt_correct.
by move=>*; rewrite /tmsize PolI.tsize_trec1.
exact: TM_sqrt_correct.
Qed.

Definition exp := Eval hnf in fun_gen I.exp TM_exp.

Theorem exp_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (exp u Y tf) (fun x => Xexp (f x)).
Proof.
apply: fun_gen_correct =>//.
exact: I.exp_correct.
by move=>*; rewrite /tmsize PolI.tsize_trec1.
exact: TM_exp_correct.
Qed.

Definition cos := Eval hnf in fun_gen I.cos TM_cos.

Theorem cos_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (cos u Y tf) (fun x => Xcos (f x)).
Proof.
apply: fun_gen_correct =>//.
exact: I.cos_correct.
by move=>*; rewrite /tmsize PolI.tsize_trec2.
exact: TM_cos_correct.
Qed.

Definition sin := Eval hnf in fun_gen I.sin TM_sin.

Theorem sin_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (sin u Y tf) (fun x => Xsin (f x)).
Proof.
apply: fun_gen_correct =>//.
exact: I.sin_correct.
by move=>*; rewrite /tmsize PolI.tsize_trec2.
exact: TM_sin_correct.
Qed.

Definition TM_tan_slow prec X0 X n :=
  TM_div prec (TM_sin prec X0 X n) (TM_cos prec X0 X n) X0 X n.

Definition tan := Eval hnf in fun_gen I.tan TM_tan_slow.

Theorem tan_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (tan u Y tf) (fun x => Xtan (f x)).
Proof.
apply: fun_gen_correct =>//.
exact: I.tan_correct.
by move=> *; rewrite /tmsize size_TM_mul. (* TODO : refactor *)
move=> prec X0 X n Hsubset [x Hx].
rewrite /TM_tan_slow; change n with (n.+1.-1); apply: TM_div_correct =>//.
(* OK since Xtan := fun x : ExtendedR => Xdiv (Xsin x) (Xcos x) *)
eexists; exact Hx.
by rewrite PolI.tsize_trec2. (* TODO : refactor *)
by rewrite PolI.tsize_trec2. (* TODO : refactor *)
apply: TM_sin_correct =>//.
eexists; exact Hx.
apply: TM_cos_correct =>//.
eexists; exact Hx.
Qed.

Definition atan (u : U) (X : I.type) (t : T) : T :=
(* FIXME: this is a very naive definition, ideally we should rely on TM_atan *)
  Tm (TM_const u.1 (I.atan u.1 (eval u t X X)) X u.2).

Theorem atan_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (atan u Y tf) (fun x => Xatan (f x)).
Proof.
move=> u Y tf f [Hnan Hnil Hmain].
split=>//; first by rewrite Hnan.
by rewrite /= /tmsize size_TM_const.
move=> Hne; apply: TM_const_correct_strong.
exact: not_empty_Imid.
exact: Imid_subset.
move=> x Hx.
apply: I.atan_correct.
exact: eval_correct.
Qed.

Definition power_int p := Eval cbv delta[fun_gen] beta in
  match p with
(*| 0%Z => fun u xi t => Const (I.fromZ 1) *)
  | 1%Z => fun u xi t => t
  | _ => fun_gen
           (fun prec x => I.power_int prec x p)
           (fun prec => TM_power_int prec p)
  end.

Theorem power_int_correct :
  forall (p : Z) u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (power_int p u Y tf) (fun x => Xpower_int (f x) p).
Proof.
move=> p u Y tf f Hf.
have [Hnan Hnil Hmain] := Hf.
have [Hp|Hp] := Z.eq_dec p 1%Z.
(* . *)
(* rewrite Hp.
apply (@approximates_ext (fun x => Xmask (Xreal 1) (f x)))=>//. *)
(* . *)
rewrite Hp.
apply (@approximates_ext f)=>//.
move=> x; rewrite /Xinv.
case: (f x) =>[//|r].
by rewrite /= Rmult_1_r.
(* . *)
case: p Hp =>[|p'|p']=>//; (try case: p'=>[p''|p''|]) =>// H;
apply: (fun_gen_correct
  (fi := fun prec x => I.power_int prec x _)
  (ftm := fun prec => TM_power_int prec _)
  (fx := fun x => Xpower_int x _)) =>//;
try (by move=> *; apply: I.power_int_correct);
try (by move=> *; rewrite /tmsize size_TM_power_int);
by move=> *; apply: TM_power_int_correct.
Qed.

Definition sqr := power_int 2.

Theorem sqr_correct :
  forall u (Y : I.type) tf f,
  approximates Y tf f ->
  approximates Y (sqr u Y tf) (fun x => Xsqr (f x)).
Proof.
move=> u Y tf f Hf.
apply: (@approximates_ext (fun x => Xpower_int (f x) 2%Z)).
move=> x; rewrite /Xpower_int /Xsqr.
case: (f x) =>[//|r].
by rewrite /= Rmult_1_r.
exact: power_int_correct.
Qed.

End TM.
