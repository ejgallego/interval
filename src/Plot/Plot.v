From Coq Require Import Reals List.
Require Import Tactic.

Import Xreal Interval Tree Reify Prog.
Import Tactic.Private.
Import IT.Private.IT1.

Module F := SFBI2.

Definition plot1 (f : R -> R) (ox dx : R) (l : list I.type) :=
  forall i x, (ox + dx * INR i <= x <= ox + dx * INR (S i))%R ->
  contains (I.convert (nth i l I.nai)) (Xreal (f x)).

Lemma plot_ext :
  forall f g u d l,
  (forall x, f x = g x) ->
  plot1 f u d l -> plot1 g u d l.
Proof.
intros f g u d l H K i x Hx.
specialize (K i x Hx).
now rewrite <- H.
Qed.

Fixpoint bound_plot_aux prec (fi : I.type -> I.type) (ui di : I.type) (xz : Z) (i : nat) (acc : I.type) : I.type :=
  match i with
  | O => acc
  | S i =>
    let xz := Z.succ xz in
    let xi := I.add prec ui (I.mul prec di (I.fromZ prec xz)) in
    bound_plot_aux prec fi ui di xz i (I.join (fi xi) acc)
  end.

Definition bound_plot prec hyps pf cf oxi dxi nb :=
  let bounds := R.merge_hyps prec hyps ++ map (T.eval_bnd prec) cf in
  let fi xi := nth 0 (A.BndValuator.eval prec pf (xi :: bounds)) I.nai in
  bound_plot_aux prec fi oxi dxi 0%Z (Z.to_nat nb) (fi oxi).

Fixpoint sample_plot_aux prec (gi : I.type -> I.type -> I.type) (check : I.type -> bool) (ui di zi2 : I.type) (fi : I.type -> I.type) (i : nat) (mz xz rz : Z) (acc : list I.type) : list I.type :=
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
    sample_plot_aux prec gi check ui di (snd yizi) (fst firz) i mz' xz' (snd firz) acc
  end.

Definition sample_plot prec deg check hyps pf cf oxi dxi nb :=
  let hyps := R.merge_hyps prec hyps in
  let gi :=
    let bounds := hyps ++ map (T.eval_bnd prec) cf in
    let bounds := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const bounds in
    fun yi =>
      let fi := nth 0 (A.TaylorValuator.eval prec deg yi pf bounds) A.TaylorValuator.TM.dummy in
      fun xi => A.TaylorValuator.TM.eval (prec, deg) fi yi xi in
  let ui := I.add prec oxi (I.mul prec dxi (I.fromZ prec 0)) in
  let vi := I.add prec oxi (I.mul prec dxi (I.fromZ prec nb)) in
  sample_plot_aux prec gi check oxi dxi I.whole (gi (I.join ui vi)) (Z.to_nat nb) 0%Z nb nb nil.

Lemma sample_plot_correct :
  forall prec deg check vars hyps pf cf oxi dxi ox dx nb l,
  contains (I.convert oxi) (Xreal ox) ->
  contains (I.convert dxi) (Xreal dx) ->
  sample_plot prec deg check hyps pf cf oxi dxi (Zpos nb) = l ->
  eval_hyps hyps vars (
    plot1 (fun t => eval_real' pf (t :: vars) cf) ox dx l).
Proof.
intros prec deg check vars hyps pf cf oxi dxi ox dx nb l Box Bdx <-.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
unfold sample_plot, eval_real'.
set (bounds := A.TaylorValuator.TM.var :: _).
set (ui := I.add prec oxi (I.mul prec dxi (I.fromZ prec 0))).
set (vi := I.add prec oxi (I.mul prec dxi (I.fromZ prec (Zpos nb)))).
set (gi := fun yi =>
      let fi := nth 0 (A.TaylorValuator.eval prec deg yi pf bounds) A.TaylorValuator.TM.dummy in
      fun xi => A.TaylorValuator.TM.eval (prec, deg) fi yi xi).
set (f x := nth 0 (eval_real pf ((x :: vars) ++ map (fun c : expr => eval c nil) cf)) 0%R).
fold (gi (I.join ui vi)).
assert (Hg: forall ti xi x, contains (I.convert xi) (Xreal x) -> contains (I.convert (gi ti xi)) (Xreal (f x))).
{ intros ti xi x Hx.
  apply A.TaylorValuator.eval_correct with (2 := Hx).
  now apply app_merge_hyps_eval_bnd. }
rewrite <- (Z2Nat.id (Zpos nb)) at 2 by easy.
set (i := Z.to_nat (Zpos nb)).
cut (plot1 f (ox + dx * INR i) dx nil).
2: now intros [|j] x _.
generalize (@nil I.type).
generalize I.whole (I.join ui vi) 0%Z (Z.pos nb).
clearbody f gi i.
clear -Box Bdx Hg.
induction i as [|n IH].
{ simpl. intros _ _ _ _ l. now rewrite Rmult_0_r, Rplus_0_r. }
intros zi2 gxi mz rz acc Hacc.
cbn beta iota zeta delta [sample_plot_aux].
rewrite <- Nat2Z.inj_pred by apply lt_O_Sn.
simpl (Nat.pred (S n)).
set (xi1 := I.add prec oxi (I.mul prec dxi (I.fromZ prec (Z.of_nat n)))).
set (xi2 := I.add prec oxi (I.mul prec dxi (I.fromZ prec (Z.of_nat (S n))))).
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
set (gxi' := I.join (I.add prec oxi (I.mul prec dxi (I.fromZ prec mz''))) xi1).
clearbody gxi'.
cut (plot1 f (ox + dx * INR n) dx (fst yizi :: acc)).
{ destruct Z.eqb ; apply IH. }
clear -Box Bdx Hg Hacc.
intros [|i] x Hx.
2: {
  apply Hacc.
  revert Hx. clear.
  rewrite !S_INR.
  replace (ox + dx * INR n + dx * (INR i + 1))%R with (ox + dx * (INR n + 1) + dx * INR i)%R by ring.
  replace (ox + dx * INR n + dx * (INR i + 1 + 1))%R with (ox + dx * (INR n + 1) + dx * (INR i + 1))%R by ring.
  easy. }
assert (Hxi: contains (I.convert xi) (Xreal x)).
{ apply J.join_correct with (u := (ox + dx * (IZR (Z.of_nat n)))%R) (v := (ox + dx * (IZR (Z.of_nat (S n))))%R).
  apply J.add_correct with (1 := Box).
  apply J.mul_correct with (1 := Bdx).
  apply I.fromZ_correct.
  apply J.add_correct with (1 := Box).
  apply J.mul_correct with (1 := Bdx).
  apply I.fromZ_correct.
  rewrite Nat2Z.inj_succ, succ_IZR, <- INR_IZR_INZ.
  revert Hx. clear.
  now rewrite Rmult_0_r, Rplus_0_r, Rmult_plus_distr_l, Rplus_assoc. }
now destruct c ; simpl ; apply Hg.
Qed.

Definition clamp_lower (v : Basic.float Basic.radix2) (h : Z) :=
  match v with
  | Basic.Fzero => 0%Z
  | Basic.Fnan => 0%Z
  | Basic.Float true _ _ => 0%Z
  | Basic.Float false m e =>
    let v := Z.shiftl (Zpos m) e in
    if Z.leb h v then h else v
  end.

Definition clamp_upper (v : Basic.float Basic.radix2) (h : Z) :=
  match v with
  | Basic.Fzero => 0%Z
  | Basic.Fnan => h
  | Basic.Float true _ _ => 0%Z
  | Basic.Float false m e =>
    let v:=
      match e with
      | Z0 => Zpos m
      | Zpos e' => Z.shiftl (Zpos m) e
      | Zneg e' => Z.shiftl (Zpos m + (Z.shiftl 1 (Zpos e')) - 1) e
      end in
    if Z.leb h v then h else v
  end.

Definition clamp (xi : I.type) (h : Z) :=
  match xi with
  | Float.Inan => (0%Z, h)
  | Float.Ibnd xl xu => (clamp_lower (F.toF xl) h, clamp_upper (F.toF xu) h)
  end.

Theorem clamp_correct :
  forall xi h x,
  contains (I.convert xi) (Xreal x) ->
  (0 <= x <= IZR h)%R ->
  let yi := clamp xi h in
  (IZR (fst yi) <= x <= IZR (snd yi))%R.
Proof.
intros [|xl xu] h x Bx Hx.
{ easy. }
split ; simpl in * ; unfold F.toX in Bx.
- destruct F.toF as [| |[|] mx ex] ; try easy.
  apply Rle_trans with (2 := proj1 Bx).
  clear.
  unfold clamp_lower.
  apply Rle_trans with (IZR (Z.shiftl (Zpos mx) ex)).
  { destruct (Z.leb_spec h (Z.shiftl (Zpos mx) ex)) as [H|H].
    now apply IZR_le.
    apply Rle_refl. }
  unfold Basic.FtoR.
  destruct ex as [|ex|ex].
  + apply Rle_refl.
  + rewrite Z.shiftl_mul_pow2 by easy.
    apply Rle_refl.
  + rewrite Z.shiftl_div_pow2 by easy.
    rewrite <- Raux.Zfloor_div.
    apply Raux.Zfloor_lb.
    apply Zaux.Zgt_not_eq.
    now apply Z.pow_pos_nonneg.
- destruct (F.toF xu) as [| |[|] mx ex] ; try easy.
  { apply Rle_trans with (1 := proj2 Bx).
    apply Rlt_le, Generic_proof.FtoR_Rneg. }
  unfold clamp_upper.
  destruct Z.leb.
  { easy. }
  apply Rle_trans with (1 := proj2 Bx).
  clear.
  destruct ex as [|ex|ex].
  + apply Rle_refl.
  + rewrite Z.shiftl_mul_pow2 by easy.
    apply Rle_refl.
  + rewrite Z.shiftl_div_pow2 by easy.
    rewrite Z.shiftl_mul_pow2 by easy.
    simpl Z.opp. simpl Basic.FtoR.
    fold (2 ^ Zpos ex)%Z.
    apply Generic_proof.Rdiv_ge_mult_pos.
    apply IZR_lt.
    now apply Z.pow_pos_nonneg.
    rewrite <- mult_IZR.
    apply IZR_le.
    apply Z.lt_pred_le.
    replace (Zpos mx + 1 * 2 ^ Zpos ex - 1)%Z with (Zpos mx - 1 + 1 * 2 ^ Zpos ex)%Z by ring.
    rewrite Zdiv.Z_div_plus_full.
    apply Z.mul_succ_div_gt.
    now apply Z.pow_pos_nonneg.
    apply Zaux.Zgt_not_eq.
    now apply Z.pow_pos_nonneg.
Qed.

Fixpoint clamp_plot prec (vi ei : I.type) (h : Z) (l : list I.type) : list (Z * Z) :=
  match l with
  | nil => nil
  | cons yi l =>
    let r := clamp (I.mul prec (I.sub prec yi vi) ei) h in
    cons r (clamp_plot prec vi ei h l)
  end.

Definition plot2 (f : R -> R) (ox dx oy dy : R) (h : Z) (l : list (Z * Z)) :=
  forall i x, (ox + dx * INR i <= x <= ox + dx * INR (S i))%R ->
  (oy <= f x <= oy + dy * IZR h)%R ->
  let r := nth i l (0%Z, h) in
  (oy + dy * IZR (fst r) <= f x <= oy + dy * IZR (snd r))%R.

Lemma affine_transf :
  forall oy dy y1 y2 y : R,
  (0 < dy)%R ->
  (oy + dy * y1 <= y <= oy + dy * y2)%R <-> (y1 <= (y - oy) / dy <= y2)%R.
Proof.
intros oy dy y1 y2 y Hdy.
replace y with (oy + dy * ((y - oy) / dy))%R at 1 2.
2: now field ; apply Rgt_not_eq.
split ; intros [H1 H2] ; split.
- apply Rmult_le_reg_l with (1 := Hdy).
  apply Rplus_le_reg_l with (1 := H1).
- apply Rmult_le_reg_l with (1 := Hdy).
  apply Rplus_le_reg_l with (1 := H2).
- apply Rplus_le_compat_l.
  apply Rmult_le_compat_l with (2 := H1).
  now apply Rlt_le.
- apply Rplus_le_compat_l.
  apply Rmult_le_compat_l with (2 := H2).
  now apply Rlt_le.
Qed.

Lemma clamp_plot_correct :
  forall prec oyi dyi f ox dx oy dy h l1 l2,
  (0 < dy)%R ->
  contains (I.convert oyi) (Xreal oy) ->
  contains (I.convert dyi) (Xreal (/dy)) ->
  clamp_plot prec oyi dyi h l1 = l2 ->
  plot1 f ox dx l1 ->
  plot2 f ox dx oy dy h l2.
Proof.
intros prec oyi dyi f ox dx oy dy h l l2 Hdy Boy Bdy <-.
intros H i x Hx Hy.
specialize (H i x Hx).
revert i ox H Hx.
induction l as [|yi l IH] ; intros [|i] ox Hl Hx ; simpl.
- now rewrite Rmult_0_r, Rplus_0_r.
- now rewrite Rmult_0_r, Rplus_0_r.
- assert (By: contains (I.convert (I.mul prec (I.sub prec yi oyi) dyi)) (Xreal ((f x - oy) / dy))).
  { apply J.mul_correct with (2 := Bdy).
    apply J.sub_correct with (2 := Boy).
    now apply Hl. }
  generalize (clamp_correct (I.mul prec (I.sub prec yi oyi) dyi) h ((f x - oy) / dy)%R By).
  destruct clamp as [y1 y2].
  simpl.
  clear -Hdy Hy.
  intros H.
  apply affine_transf with (1 := Hdy).
  apply H.
  apply affine_transf with (1 := Hdy).
  now rewrite Rmult_0_r, Rplus_0_r.
- apply (IH i (ox + dx * INR 1)%R Hl).
  now rewrite 2!Rplus_assoc, <- 2!Rmult_plus_distr_l, 2!(Rplus_comm 1), <- 2!S_INR.
Qed.

Definition get_bounds (prec : F.precision) (l : list I.type): F.type * F.type :=
  let yi :=
    match l with
    | cons hi l => List.fold_left I.join l hi
    | nil => I.empty
    end in
  (I.lower yi, I.upper yi).
  (*
  let mi := I.div prec (I.sub prec yi2 yi1) (I.fromZ prec 20) in
  (I.sub prec yi1 mi, I.add prec yi2 mi)
  *)

Declare ML Module "interval_plot".

Ltac plot1_aux prec f x1 x2 w tac_t :=
  let p := fresh "__plot1" in
  let Hp := fresh "__Hp" in
  let ox := reify x1 constr:(@nil R) in
  let dx := reify constr:(((x2 - x1) / IZR (Zpos w))%R) constr:(@nil R) in
  let ox := eval vm_compute in (I.lower (T.eval_bnd prec ox)) in
  let dx := eval vm_compute in (I.upper (T.eval_bnd prec dx)) in
  let oxr := eval cbv -[IZR Rdiv] in (proj_val (I.convert_bound ox)) in
  let dxr := eval cbv -[IZR Rdiv] in (proj_val (I.convert_bound dx)) in
  evar (p : list I.type) ;
  assert (Hp : plot1 f oxr dxr p) ; [
    let fapp := eval cbv beta in (f reify_var) in
    let vars := constr:((reify_var :: nil)%list) in
    let vars := get_vars fapp vars in
    let vars :=
      match get_vars fapp vars with
      | (reify_var :: ?vars)%list => vars
      end in
    eapply plot_ext ; [
      let t := fresh "t" in intros t ;
      let fapp := eval cbv beta in (f t) in
      reify_partial fapp (t :: vars) ;
      exact (fun H => H) |] ;
    find_hyps vars ;
    let thr := tac_t ox dx in
    apply (sample_plot_correct prec) with
      (deg := 10%nat) (nb := w)
      (check := fun yi => F'.le' (F.sub_UP prec (I.upper yi) (I.lower yi)) thr)
      (1 := I.singleton_correct ox)
      (2 := I.singleton_correct dx) ;
    vm_compute ;
    exact (eq_refl p)
  | revert Hp ;
    unfold p ;
    clear p ].

Ltac plot2_aux prec f x1 x2 w h tac_t tac_b :=
  let p := fresh "__plot2" in
  let ox := fresh "__ox" in
  let dx := fresh "__dx" in
  let oy := fresh "__oy" in
  let dy := fresh "__dy" in
  let Hp := fresh "__Hp" in
  evar (p : list (Z * Z)) ;
  evar (ox : R) ;
  evar (dx : R) ;
  evar (oy : R) ;
  evar (dy : R) ;
  assert (Hp: plot2 f ox dx oy dy (Zpos h) p) ; [
    let tac_t := fun ox dx => tac_t prec ox dx w h in
    plot1_aux prec f x1 x2 w tac_t ;
    let y1y2 := tac_b prec in
    let oy' := constr:(fst y1y2) in
    let dy' := eval vm_compute in (F.div_UP prec (F.sub_UP prec (snd y1y2) oy') (F.fromZ (Zpos h))) in
    let oyr := eval cbv -[IZR Rdiv] in (proj_val (I.convert_bound oy')) in
    let dyr := eval cbv -[IZR Rdiv] in (proj_val (I.convert_bound dy')) in
    refine (clamp_plot_correct prec _ _ _ _ _ oyr dyr _ _ _ _ (I.singleton_correct oy') (J.inv_correct prec _ _ (I.singleton_correct dy')) _) ;
    [ apply Rdiv_lt_0_compat ;
      now apply IZR_lt
    | vm_compute ;
      exact (eq_refl p) ]
  | revert Hp ;
    unfold ox, dx, oy, dy, p ;
    clear ox dx oy dy p ].

Definition get_threshold prec hyps pf cf ox dx w h :=
  let w' := 50%Z in
  let dx := I.mul prec (I.singleton dx) (I.div prec (I.fromZ prec (Zpos w)) (I.fromZ prec w')) in
  let yi := bound_plot prec hyps pf cf (I.singleton ox) dx w' in
  F.div_UP prec (F.sub_UP prec (I.upper yi) (I.lower yi)) (F.fromZ_DN prec (Zpos h)).

Ltac plot_get_threshold prec ox dx w h :=
  match goal with
  | |- eval_hyps ?hyps _ (plot1 (fun t => eval_real' ?pf (t :: _) ?cf) _ _ _) =>
    eval vm_compute in (get_threshold prec hyps pf cf ox dx w h)
  end.

Ltac plot_get_bounds prec :=
  match goal with
  | |- plot1 _ _ _ ?p -> _ =>
    eval vm_compute in (get_bounds prec p)
  end.

Goal True.
Proof.
(*
let prec := eval vm_compute in (F.PtoP 52) in
let h := constr:(700%positive) in
plot2_aux prec (fun x => x^2 * sin (x^2))%R (-4)%R 4%R 1000%positive 700%positive
  ltac:(plot_get_threshold) ltac:(plot_get_bounds).
display_plot.
*)
(*
let prec := eval vm_compute in (F.PtoP 90) in
let h := constr:(700%positive) in
plot2_aux prec (fun x => 1 + x * (4503599627370587 * powerRZ 2 (-52) + x * (4503599627370551 * powerRZ 2 (-53) + x * (6004799497195935 * powerRZ 2 (-55) + x * (6004799498485985 * powerRZ 2 (-57) + x * (2402017533563707 * powerRZ 2 (-58) + x * (6405354563481393 * powerRZ 2 (-62)))))))- exp x)%R
  (-1/32)%R (1/32)%R 1000%positive 700%positive
  ltac:(plot_get_threshold) ltac:(plot_get_bounds).
display_plot.
*)
intros.
exact I.
Qed.

(* plot [-1./32:1./32] 1 + x * (4503599627370587. * 2**(-52) + x * (4503599627370551. * 2**(-53) + x * (6004799497195935. * 2**(-55) + x * (6004799498485985. * 2**(-57) + x * (2402017533563707. * 2**(-58) + x * (6405354563481393. * 2**(-62))))))) - exp(x) *)
