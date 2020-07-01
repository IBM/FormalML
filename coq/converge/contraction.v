Require Import PArith Psatz Reals.
Require Import Coquelicot.Coquelicot.

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import posreal_complements cball.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section BanachComplete.
Variable U : CompleteSpace.
Variable F : U -> U.
Variable mu : nonnegreal.

Definition lipschitz_on (P : U -> Prop) :=
  forall x y : U, forall r : nonnegreal,
     P x -> P y -> cball x r y -> cball (F x) (mu*r) (F y).

Lemma lipschitz_on_subset (P Q : U -> Prop) : subset Q P ->
    lipschitz_on P -> lipschitz_on Q.
Proof. by move => HPQ HP x y r Hx Hy; apply:HP; apply: HPQ. Qed.

(* An SBall {| center := u; offset := s; radius := r |} models
   a ball B(u, r), with 0 <= r, packaged with an auxiliary s,
   such that 0 <= s *)
Record SBall := mkSBall {
  center : U;
  offset : nonnegreal;
  radius : nonnegreal;
}.

Definition SBall_pred (SB : SBall) : U -> Prop :=
  cball (center SB) (radius SB).

Coercion SBall_pred : SBall >-> Funclass.

(* An interesting SBall {| center := u; offset := s; radius := r |}
   verifies the SBallProp, i.e:
   - F is Lipschitz on B(u,r)
   - F u \in B(u, s)
   - s + m * r <= r

In particular, an interesting SBall is stable under F. *)

Record SBallProp (SB : SBall) := mkSBallProp {
  lipschitz_cond : lipschitz_on SB;
  center_offset : cball (center SB) (offset SB) (F (center SB));
  strong_stable : offset SB + mu * radius SB <= radius SB;
}.


Lemma SBallProp_stable (SB : SBall) :
  SBallProp SB -> forall x, SB x -> SB (F x).
Proof.
  move => SBP x Hx.
  eapply cball_le; first apply SBP.
  eapply cball_triangle; first apply SBP.
  apply SBP => //; apply cball_center.
Qed.

(* A contracting F acts via SBall_map on interesting SBalls: 
the 'image' of an SBall sb is an SBall, which is moreover included  
in sb *)

Definition SBall_map (SB : SBall) : SBall :=
 {| center := F (center SB);
    offset := (mu * offset SB)%:nonnegreal;
    radius := (mu * radius SB)%:nonnegreal; |}.

Section SBallMap.

Hypothesis Hmu1 : mu < 1.
Variable (SB : SBall) (SBP : SBallProp SB).
Notation x0 := (center SB).
Notation b := (offset SB).
Notation r := (radius SB).
Notation SB' := (SBall_map SB).

Lemma SBall_map_subset : subset SB' SB.
Proof.
  rewrite /SBall_pred /= => x H.
  eapply cball_le; first apply SBP.
  eapply cball_triangle => //.
  apply SBP.
Qed.

Lemma SBall_map_subset' x : SB x -> SB' (F x).
Proof.
  move => Hx.
  apply SBP => //; apply cball_center.
Qed.

Lemma SBall_map_SBallProp : SBallProp SB'.
Proof.
  apply mkSBallProp => /=.
+ eapply lipschitz_on_subset; last apply SBP.
  apply SBall_map_subset.
+ apply SBP; last apply SBP.
  apply cball_center.
  eapply cball_le; last apply SBP.
  move: (strong_stable SBP) (nonnegreal_mult' mu r); lra.
+ rewrite -Rmult_plus_distr_l; apply Rmult_le_compat_l => //.
  apply SBP.
Qed.

End SBallMap.

(* Now the actual proof of the Banach fixed-point theorem *)
Section BanachFixpoint.
(* The Lipschitz coefficient is < 1 *)
Hypothesis Hmu1 : mu < 1.

(* We assume an initial interesting SBall 
 SB := {| center := x0, offset := b, radius := r}, and we denote
  SB' its image under the action of F. *)
Variable (SB : SBall) (SBP : SBallProp SB).
Notation x0 := (center SB).
Notation b := (offset SB).
Notation r := (radius SB).
Notation SB' := (SBall_map SB).

(* The iterated 'images' of the initial SB under F *)
(* use ssrnat.iter ? *)
Fixpoint IBall (n : nat) : SBall := match n with
  | 0 => SB
  | S n => SBall_map (IBall n)
end.

(* These iterated images are all SBalls *)
Lemma IBall_SBallProp n : SBallProp (IBall n).
Proof. elim: n => [ // | n IHn]; apply SBall_map_SBallProp, IHn. Qed.

(* Radius of the iterated images *)
Lemma IBall_radius n : radius (IBall n) = mu^n * r :> R.
Proof. elim: n => [ | n IHn] /=; rewrite ?IHn; ring. Qed.

(* This radius tends to zero *)
Lemma lim_IBall_radius (e : posreal) :
  exists N, forall n, (N <= n)%nat -> radius (IBall n) < e.
Proof.
case: (Rle_lt_or_eq_dec 0 r (cond_nonneg r)) => Hr; last first.
+ by exists 0%nat => n _; rewrite IBall_radius -Hr Rmult_0_r.
+ have /pow_lt_1_zero h : Rabs mu < 1 by rewrite Rabs_pos_eq.
case: (h (e / (mkposreal Hr))) => // N /=HN; exists N => n Hn.
rewrite IBall_radius -[X in X*_<_]Rabs_pos_eq => //.
have -> : e = e / r * r :> R by field; lra.
by apply Rmult_lt_compat_r => //; apply HN.
Qed.

(* The iterated images are nested *)
Lemma IBall_subset m n : (m <= n)%nat -> subset (IBall n) (IBall m).
Proof.
  elim: n m => [ m /le_n_0_eq Hm| n IHn m /le_lt_eq_dec [Hm | Hm]].
+ rewrite Hm; apply subset_refl.
+ eapply subset_trans; first apply SBall_map_subset, IBall_SBallProp.
  apply IHn; lia.
+ rewrite Hm; apply subset_refl.
Qed.

(* The filter used to construct the fixed point *)
Definition BF (P : U -> Prop) := exists n, subset (IBall n) P.

Lemma BF_true : BF (fun _ => True).
Proof. by exists 0%nat. Qed.

Lemma BF_imp  (P Q : U -> Prop) : subset P Q -> BF P -> BF Q.
Proof. by move=> sPQ [n nP]; exists n; apply: subset_trans sPQ. Qed.

Lemma BF_and (P Q : U -> Prop) : BF P -> BF Q -> BF (fun x => P x /\ Q x).
Proof.
  move => [n HP] [m HQ]; exists (max n m) => x Hx; split.
+ eapply HP, IBall_subset; last apply Hx.
  apply Max.le_max_l.
+ eapply HQ, IBall_subset; last apply Hx.
  apply Max.le_max_r.
Qed.

Lemma BF_ex P : BF P -> exists x, P x.
Proof. move => [n HP]; eexists; apply HP, cball_center. Qed.

Global Instance BF_filter : ProperFilter BF.
Proof.
  apply Build_ProperFilter; last apply Build_Filter.
+ exact: BF_ex.
+ apply BF_true.
+ apply BF_and.
+ apply BF_imp.
Qed.

(* It is a Cauchy filter *)
Lemma BF_cauchy : cauchy BF.
Proof.
  move => e; case: (lim_IBall_radius e) => N HN.
  exists (center (IBall N)); eapply BF_imp.
  apply cball_ball_subset, (HN N); lia.
  exists N; apply subset_refl.
Qed.

(* Therefore it has a limit bf, the candidate fixed point. *)
Notation bf := (lim BF).
Notation BF_complete_cauchy := (complete_cauchy BF BF_filter BF_cauchy).

Definition is_fixpoint x := close x (F x).

(* existence and unicity of fixpoint *)

Lemma BF_lim_inside_iball n : IBall n bf.
Proof.
  apply cball_close => e.
  case: (BF_complete_cauchy e) => n' Hn'.
  set m := max n n'; exists (center (IBall m)); split.
+ eapply IBall_subset; last apply cball_center; apply Max.le_max_l.
+ apply Hn'; eapply IBall_subset; last apply cball_center; apply Max.le_max_r.
Qed.

Lemma BF_lim_inside_sball : SB bf.
Proof. exact: (BF_lim_inside_iball 0%nat). Qed.

Lemma BF_map_lim_inside_iball n : IBall n (F bf).
Proof.
  apply SBallProp_stable; first apply IBall_SBallProp.
  apply BF_lim_inside_iball.
Qed.

Lemma inside_iball_unique v w :
  (forall n, IBall n v) -> (forall n, IBall n w) -> close v w.
Proof.
  move => Hv Hw e. 
  case: (lim_IBall_radius (e/2)%:posreal) => n Hn.
  replace (e : R) with (e/2+e/2); last by field.
  apply ball_triangle with (center (IBall n)).
+ eapply ball_sym, cball_ball_subset; last apply Hv; apply Hn; lia.
+ eapply cball_ball_subset; last apply Hw; apply Hn; lia.
Qed.

Lemma BF_lim_is_fixpoint : is_fixpoint bf.
Proof.
  apply inside_iball_unique.
  apply BF_lim_inside_iball.
  apply BF_map_lim_inside_iball.
Qed.

Lemma fixpoint_inside_iball v : SB v -> is_fixpoint v -> forall n, IBall n v.
Proof.
  move => Hv Hfix.
  elim => [ // | n IHn].
  apply cball_close => e; exists (F v); split.
  apply SBall_map_subset' => //; first apply IBall_SBallProp. auto.
Qed.

Lemma fixpoint_unique v w : SB v -> SB w -> is_fixpoint v -> is_fixpoint w -> close v w.
Proof.
  move => Hv Hw Hfixv Hfixw.
  by apply inside_iball_unique; apply fixpoint_inside_iball.
Qed.



(*

(* The limit bf lies inside the initial SBall. *)
Lemma BF_fixpoint_inside : SB bf.
Proof.
  apply cball_close => e.
  case: (BF_complete_cauchy e) => N HN.
  exists (center (IBall N)); split.
+ have HN0 : (0 <= N)%nat by lia.
  apply (IBall_subset HN0), cball_center.
+ apply HN, cball_center.
Qed.

Arguments cball_ball_subset {U x} r1 {r2}.

(* And it is a indeed a fixed point for F *)
Lemma BF_is_fixpoint : is_fixpoint bf.
Proof.
suff cball_version (e : posreal) : cball bf e (F bf).
  move=> e; apply: (cball_ball_subset (e / 2))=> //. case: e=> /= e; lra.
have [m Hm] := BF_complete_cauchy (e/2)%:posreal.
pose IBPm := IBall_SBallProp m.
have H0m : (0 <= m)%nat by lia.
have -> : e = e / 2 + e / 2 :> R by field.
apply cball_triangle with (F (center (IBall m))).
+ eapply ball_cball_subset, Hm, SBallProp_stable => //; apply cball_center.
+ apply cball_le with (mu*(e/2)).
  * by rewrite -[X in _<=X]Rmult_1_l; apply Rlt_le, Rmult_lt_compat_r.
  * apply SBP => /=.
    - by eapply (IBall_subset H0m), cball_center.
    - exact BF_fixpoint_inside.
    - by apply ball_cball_subset, ball_sym, Hm, cball_center.
Qed.

*)


End BanachFixpoint.

End BanachComplete.
