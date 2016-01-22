Require Import Reals.
Require Import Coquelicot.

Require Import ssreflect.

Section MissingContinuity.

Lemma continuous_Rinv x :
  x <> 0 ->
  continuous (fun x => / x) x.
Proof.
move => Hxneq0.
apply continuity_pt_filterlim. (* strange: apply works but not apply: *)
apply: continuity_pt_inv => // .
apply continuity_pt_filterlim.
apply: continuous_id.
Qed.

Lemma continuous_Rinv_comp (f : R -> R) x:
  continuous f x ->
  f x <> 0 ->
  continuous (fun x => / (f x)) x.
Proof.
move => Hcont Hfxneq0.
apply: continuous_comp => //.
by apply: continuous_Rinv.
Qed.

Lemma continuous_cos x : continuous cos x.
Proof.
apply continuity_pt_filterlim.
by apply: continuity_cos => // .
Qed.

Lemma continuous_cos_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => cos (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => //.
by apply: continuous_cos.
Qed.

Lemma continuous_sin x : continuous sin x.
Proof.
apply continuity_pt_filterlim.
by apply: continuity_sin => // .
Qed.

Lemma continuous_sin_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => sin (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => //.
by apply: continuous_sin.
Qed.

Lemma continuous_atan x : continuous atan x.
Proof.
admit. (* how do I prove this? *)
Qed.

Lemma continuous_atan_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => atan (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => //.
by apply: continuous_atan.
Qed.

Lemma continuous_exp x : continuous exp x.
Proof.
admit. (* couldn't find it *)
Qed.

Lemma continuous_exp_comp (f : R -> R) x:
  continuous f x ->
  continuous (fun x => exp (f x)) x.
Proof.
move => Hcont.
apply: continuous_comp => //.
by apply: continuous_exp.
Qed.

(* 0 <= x is an unnecessary hypothesis thanks to sqrt(-x) = 0 for x >= 0 *)
(* still I don't know how to explain this to Coquelicot *)
Lemma continuous_sqrt x : (0 <= x) -> continuous sqrt x.
Proof.
move => Hx.
apply continuity_pt_filterlim.
by apply: continuity_pt_sqrt.
Qed.

Lemma continuous_sqrt_comp (f : R -> R) x:
  continuous f x ->
  0 <= f x ->
  continuous (fun x => sqrt (f x)) x.
Proof.
move => Hcont Hfxpos.
apply: continuous_comp => // .
by apply: continuous_sqrt.
Qed.

Lemma continuous_ln x : (0 < x) -> continuous ln x.
Proof.
move => Hxgt0.
Admitted.

Lemma continuous_Rabs_comp f (x : R) :
  continuous f x -> continuous (fun x0 => Rabs (f x0)) x.
Proof.
move => Hcontfx.
apply: continuous_comp => // .
apply: continuous_Rabs.
Qed.

End MissingContinuity.

Section MissingIntegrability.

Lemma ex_RInt_Rabs f a b : ex_RInt f a b -> ex_RInt (fun x => Rabs (f x)) a b.
move => Hintfx.
Admitted.

End MissingIntegrability.


Section Integrability.

Variables (V : CompleteNormedModule R_AbsRing) (g : R -> V) (a b c d : R).

Lemma ex_RInt_Chasles_sub :
 a <= b -> b <= c -> c <= d -> ex_RInt g a d -> ex_RInt g b c.
Proof.
move=> leab lebc lecd hiad; apply: (ex_RInt_Chasles_1 _ _ _ d) => //. 
by apply: (ex_RInt_Chasles_2 _ a) => //; split=> //; apply: (Rle_trans _ c).
Qed.

End Integrability.

(* Below : a couple of helper lemmas about maj/min of integrals *)
(* We should probably also add the more general case of ra <= rb *)
Section IntegralEstimation.

Variables (f : R -> R) (ra rb : R).

Hypothesis ltab : ra < rb.

Hypothesis fint : ex_RInt f ra rb.

Lemma RInt_le_r (u : R) : 
 (forall x : R, ra <= x <= rb -> f x <= u) -> RInt f ra rb / (rb - ra) <= u.
Proof.
move=> hfu; apply/Rle_div_l;first by apply: Rgt_minus.
have -> : u * (rb - ra) = RInt (fun _ => u) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
admit. (* FIXME easy *)
Qed.

Lemma RInt_le_l (l : R) : 
  (forall x : R, ra <= x <= rb -> l <= f x) -> l <= RInt f ra rb / (rb - ra).
Proof.
move=> hfl; apply/Rle_div_r; first by apply: Rgt_minus.
have -> : l * (rb - ra) = RInt (fun _ => l) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
admit. (* FIXME easy *)
Qed.

Lemma RInt_le_r_strict (u : R) :
 (forall x : R, ra < x < rb -> f x <= u) -> RInt f ra rb / (rb - ra) <= u.
Proof.
move=> hfu; apply/Rle_div_l;first by apply: Rgt_minus.
have -> : u * (rb - ra) = RInt (fun _ => u) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
Qed.

Lemma RInt_le_l_strict (l : R) :
  (forall x : R, ra < x < rb -> l <= f x) -> l <= RInt f ra rb / (rb - ra).
Proof.
move=> hfl; apply/Rle_div_r; first by apply: Rgt_minus.
have -> : l * (rb - ra) = RInt (fun _ => l) ra rb.
  by rewrite RInt_const Rmult_comm.
apply: RInt_le => //; first exact: Rlt_le.
exact: ex_RInt_const.
Qed.

End IntegralEstimation.