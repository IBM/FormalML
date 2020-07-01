(** * Completeness of functions with uniform convergence over a domain *)

Require Import ZArith Reals Psatz.
Require Import Coquelicot.Coquelicot.
Require Import  posreal_complements cball.

From Coq Require Import ssreflect.

Set Implicit Arguments.

(** ** Uniform Space structure for functions with domains *)

Section domfct_UniformSpace.

Variable (T : Type) (U : UniformSpace) (I : T -> Prop).

Notation IT := {t : T | I t}.
Notation "[ f ]" := (fun (t' : IT) => let (t,_) := t' in f t).

Definition domfct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, I t -> ball (x t) eps (y t).

Lemma domfct_ball_center x (e : posreal) : domfct_ball x e x.
Proof. by move => t _; apply ball_center. Qed.

Lemma domfct_ball_sym x y e : domfct_ball x e y -> domfct_ball y e x.
Proof. by move => H t Ht; apply ball_sym; auto. Qed.

Lemma domfct_ball_triangle x y z e1 e2 : domfct_ball x e1 y -> domfct_ball y e2 z ->
  domfct_ball x (e1 + e2) z.
Proof. move => H1 H2 t Ht; eapply ball_triangle; auto. Qed.

Definition domfct_UniformSpace_mixin :=
  UniformSpace.Mixin _ _ domfct_ball_center domfct_ball_sym domfct_ball_triangle.

Definition domfct_UniformSpace :=
  UniformSpace.Pack (T -> U) domfct_UniformSpace_mixin (T -> U).

Lemma domfct_ball_ext f f' g g' e : (forall t, I t -> f t = f' t) -> (forall t, I t -> g t = g' t) ->
  domfct_ball f e g -> domfct_ball f' e g'.
Proof.
  move => H1 H2 H3 t Ht.
  by rewrite -H1 // -H2 //; apply H3.
Qed.

Lemma domfct_ball_ext_l f f' g e : (forall t, I t -> f t = f' t) -> domfct_ball f e g -> domfct_ball f' e g.
Proof. by move => H; apply domfct_ball_ext. Qed.

Lemma domfct_ball_ext_r f g g' e : (forall t, I t -> g t = g' t) -> domfct_ball f e g -> domfct_ball f e g'.
Proof. by move => H; apply domfct_ball_ext. Qed.


End domfct_UniformSpace.


(** ** Properties specific to real-valued functions *)

Section Rdomfct_cball.
Variable (I : R -> Prop).
(*Notation "{R,I -> R}" := (@domfct_CompleteSpace R_CompleteSpace R_CompleteSpace I).*)
Notation "{R,I -> R}" := (@domfct_UniformSpace R_UniformSpace R_UniformSpace I).
Notation dball := (@ball {R,I -> R}).
Notation dcball := (@cball {R,I -> R}).
Notation dball0 := (@ball {R,I -> R} (fun _ => 0)).
Notation dcball0 := (@cball {R,I -> R} (fun _ => 0)).
Implicit Types (f g : {R,I -> R}).

Lemma domfct_cball_ext (f f' g g' : {R,I -> R}) r : (forall t, I t -> f t = f' t) -> (forall t, I t -> g t = g' t)
  -> dcball f r g -> dcball f' r g'.
Proof.
  move => Hf Hg Hfg e.
  eapply domfct_ball_ext.
  by apply Hf. by apply Hg.
  apply Hfg.
Qed.

Lemma domfct_cball_ext_l (f f' g : {R,I -> R}) r : (forall t, I t -> f t = f' t) ->
  dcball f r g -> dcball f' r g.
Proof. by move => H; apply domfct_cball_ext. Qed.

Lemma domfct_cball_ext_r (f g g' : {R,I -> R}) r : (forall t, I t -> g t = g' t) ->
  dcball f r g -> dcball f r g'.
Proof. by move => H; apply domfct_cball_ext. Qed.

Lemma R_dballE f g r : dball f r g <-> forall t, I t -> Rabs (g t - f t) < r.
Proof.
  split.
+ by move => H t It; apply R_ballE, H.
+ by move => H; move => t It; apply R_ballE, H.
Qed.

Lemma R_dball0E f r : dball0 r f <-> forall t, I t -> Rabs (f t) < r.
Proof.
  split.
+ move => H t It; replace (f t) with (f t - 0); last by ring.
  by apply R_dballE with (f:=fun _ => 0).
+ move => H; apply R_dballE => t It.
  rewrite Rminus_0_r; auto.
Qed.

Lemma R_dcballE f g r : dcball f r g <-> forall t, I t -> Rabs (g t - f t) <= r.
Proof.
  split.
+ by move => H t It; apply R_cballE => e; apply H.
+ move => H e; move => t It; apply R_ballE; case: e (H t It) => e He /=; lra.
Qed.

Lemma R_dcball0E f r : dcball0 r f <-> forall t, I t -> Rabs (f t) <= r.
Proof.
  split.
+ move => H t It; replace (f t) with (f t - 0); last by ring.
  by apply R_dcballE with (f:=fun _ => 0).
+ move => H; apply R_dcballE => t It.
  rewrite Rminus_0_r; auto.
Qed.


Lemma Rdomfct_close f g : close f g <-> forall t, I t -> f t = g t.
Proof.
  split.
+ move => /cball_0_close /R_dcballE H t It; symmetry.
  by apply Rminus_diag_uniq, Rabs_eq_0, Rle_antisym; [apply H | apply Rabs_pos].
+ move => H e; move => t It; rewrite H => //; apply ball_center.
Qed.


End Rdomfct_cball.


(** ** Completeness *)

Section domfct_CompleteSpace.

Context {T : Type} {U : CompleteSpace} {I : T -> Prop}.

Notation "{T,I -> U}" := (domfct_UniformSpace U I).
Notation dball := (domfct_ball U I).

Lemma complete_cauchy_domfct (F : ((T -> U) -> Prop) -> Prop) : ProperFilter F ->
  (forall (eps : posreal), exists f, F (dball f eps)) ->
  forall (eps : posreal), F (dball (lim_fct F) eps).
Proof.
  move => ProperF CauchyF eps.
  move: (CauchyF (eps/3)%:posreal) => [f Hf].
  eapply filter_imp; last apply Hf.
  move => g Hg t Ht; apply ball_le with (eps/3+eps/3+eps/3); first by rewrite /=; lra.
  eapply ball_triangle; last by apply Hg.
  pose Ft := filtermap (fun h => h t) F.
  have Ftht (h : T -> U) (e : posreal) : F (dball h e) -> Ft (ball (h t) e)
    by move => Hh; rewrite /Ft /filtermap; eapply filter_imp; last apply Hh; move => k Hk; apply Hk.
  have Ftft : Ft (ball (f t) (eps/3)) by apply Ftht.
  have ProperFt : ProperFilter Ft by apply filtermap_proper_filter.
  have CauchyFt : cauchy Ft
    by move => e;  move: (CauchyF e) => [h Hh]; exists (h t); apply Ftht.
  have Ftlimt : Ft (ball (lim_fct F t) (eps/3))
    by rewrite /lim_fct; apply complete_cauchy.
  have Hu : exists u, ball (lim_fct F t) (eps/3) u /\ ball (f t) (eps/3) u
    by apply filter_ex; apply filter_and.
  move: Hu => [u [Hu1 /ball_sym Hu2]].
  by apply ball_triangle with u.
Qed.

Lemma close_lim_domfct : forall F1 F2, filter_le F1 F2 -> filter_le F2 F1 ->
  @close {T,I -> U} (lim_fct F1) (lim_fct F2).
Proof. by move => F1 F2 H1 H2 e t Ht; apply close_lim_fct. Qed.


Definition domfct_CompleteSpace_mixin :=
  CompleteSpace.Mixin {T,I -> U} lim_fct complete_cauchy_domfct close_lim_domfct.

Definition domfct_CompleteSpace :=
  CompleteSpace.Pack (T -> U) (CompleteSpace.Class _ _ domfct_CompleteSpace_mixin) (T -> U).


End domfct_CompleteSpace.

