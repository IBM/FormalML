Require Import Reals Coquelicot.Coquelicot.
Require Import Omega.

Set Bullet Behavior "Strict Subproofs".
(*

****************************************************************************************
This file is an attempt to prove the Banach Fixed Point theorem. We state it in terms of 
Kozen's coinductive proof rule.

This file roughly follows the same proof attempt as in Boldo et al's work in the Elfic 
library where they proved the Lax-Milgram Theorem. 

****************************************************************************************

 *)

(** Contractive Mappings in Complete Metric Spaces. **)

(* Note:  `ball x eps y` states that y lies in a ball of center x and radius eps.*)

Context {V : CompleteSpace}.


Definition is_lipschitz (f : V -> V) (k : R):= k > 0 /\ forall x y eps, eps > 0 -> ball x eps y -> ball (f x) (k*eps) (f y).

Definition is_contractive (f : V -> V) := exists k0 , k0 < 1 /\ is_lipschitz f k0.


Fixpoint iter_fun (n : nat) (f : V -> V) (v : V) :=
  match n with
  | 0 => v
  | S k => f (iter_fun k f v)
  end.


(* Helper lemmas. *)

Lemma Rpow_gt_0 (n0 : nat) {k : R} (hk : k > 0) : k^n0 > 0.
Proof.
  induction n0 as [| n0 iH0].
  simpl. firstorder. 
  simpl. exact (Rmult_gt_0_compat _ _ hk iH0).
Qed.

Lemma k_le_one_ne_one {k : R} (Hk : 0 < k < 1) : k - 1 <> 0 .
Proof.
  destruct Hk as [Hk1 Hk2].
  intros notk. assert (k=1) by exact (Rminus_diag_uniq _ _ notk); clear notk.
  rewrite H in Hk2.
  exact (Rlt_irrefl _ Hk2).
Qed.


Lemma Rinv_nonneg {k : R} (Hk : 0<k<1): 0 <= /(1-k).
Proof.
  left. apply Rinv_0_lt_compat.
  apply Rlt_Rminus. firstorder.
Qed.

Lemma Rminus_pow_le_one {k : R} (m : nat) (Hk : 0 < k <1) : 1 - k^m <= 1.
Proof.
  left.
  apply Rminus_lt. ring_simplify.
  apply Ropp_lt_gt_0_contravar. apply Rpow_gt_0. firstorder.
Qed.

Lemma dist_iter_fun_aux_1 {f : V -> V}{k eps : R} (x : V) (hk : 0 < k < 1) (Hf : is_lipschitz f k) : forall (n : nat) , (eps > 0) -> 
      ball x eps (f x) -> ball (iter_fun n f x) ((k^n)*eps) (iter_fun (n+1) f x).
Proof.
  intros n Heps H.
  destruct Hf as [Hk Hp].
  induction n as [| n0 iH].
  *
    simpl. assert (1*eps = eps) by ring. now rewrite H0.
  *
    simpl. 
    specialize (Hp (iter_fun n0 f x) (iter_fun (n0+1) f x) ((k^n0 * eps))).
    assert (k * k^n0 * eps = k*(k^n0 * eps)) by ring. rewrite H0. apply Hp.
    apply (Rmult_gt_0_compat _ _). exact (Rpow_gt_0 _ Hk).
    assumption.
    exact iH.
Qed.


(*Helper lemma for the inductive step in the next proof.*)
Lemma geom_sum {k : R} (hk : 0 < k < 1)(m0 n : nat) : let D :=  k ^ n * (k ^ S (S m0) - 1) / (k - 1)  in D = k^n * (k^ (S m0) - 1)/(k-1)  + k^(n+ S m0).
Proof.
  intros D. 
  assert (Kne1 : k - 1 <> 0) by exact (k_le_one_ne_one hk).
  field_simplify ; try assumption.
  rewrite pow_add,<- tech_pow_Rmult. unfold D ; field_simplify_eq ; try assumption.
  assert (k ^ S (S m0) = k^2 * k^m0) by (rewrite <-tech_pow_Rmult, <- tech_pow_Rmult ; ring).
  rewrite H ; ring.
Qed.


Lemma dist_iter_fun_aux_2 {f : V -> V}{k eps : R} (x : V) (hk : 0 < k < 1)(Hf : is_lipschitz f k) :
  forall (m  n : nat), (m > 0)%nat -> (eps > 0) ->
                let D := k^n * (k^m - 1)/(k-1) in
                ball x eps (f x) -> ball (iter_fun n f x) (D*eps) (iter_fun (n+m) f x).
Proof.
  intros m n Hm0 eps0 D Hxfx.
  induction m as [ | m0 IHm0].
  *
    exfalso. omega.
  *
    destruct m0. replace D with (k^n). exact (dist_iter_fun_aux_1 x hk Hf _ eps0 Hxfx).
    unfold D. field_simplify. reflexivity.
    exact (k_le_one_ne_one hk).
    rewrite Nat.add_succ_r.
    assert (S m0 > 0)%nat by omega. unfold D ; rewrite (geom_sum hk m0 n). 
    rewrite (Rmult_plus_distr_r). eapply (ball_triangle _ (iter_fun (n+ S m0) f x) _ _ _).
    (* `intuition` here simplifies the context*)
    exact (IHm0 H). assert (Heq : (S (n + S m0))%nat = (n + S m0 + 1)%nat) by ring.
    rewrite Heq. exact (dist_iter_fun_aux_1 x hk Hf _ eps0 Hxfx).
Qed.


Lemma dist_iter_fun {f : V -> V} {k eps : R} (x : V) (m n : nat) (hk : 0 < k < 1) (Hf : is_lipschitz f k):
  eps > 0 -> ball x eps (f x) -> let D:= k^n /(1-k) in ball (iter_fun n f x) (D*eps) (iter_fun (n+m) f x).
Proof.  
  intros Heps Hxfx D.
  case_eq m.
  *
    intro Heq. assert ((n+0 = n)%nat) by omega. rewrite H.
    enough (HDeps : D*eps > 0).
    apply (ball_center (iter_fun n f x) (mkposreal _ HDeps)).
    refine (Rmult_gt_0_compat _ _ _ Heps). unfold D.
    refine (Rdiv_lt_0_compat _ _ _ _). apply Rpow_gt_0 ; firstorder.
    apply Rlt_Rminus ; firstorder.
  *
    intros n0 Hn0.
    eapply ball_le.
    enough (k^n * (k^m - 1)/(k-1) * eps <= D*eps). apply H.
    unfold D. apply Rmult_le_compat_r ; try (left ; assumption).
    unfold Rdiv. rewrite Rmult_assoc. apply Rmult_le_compat_l.
    left. apply (Rpow_gt_0); firstorder.
    enough ((k ^ m - 1) * / (k - 1)  = (1 - k ^ m ) * / (1 - k)). rewrite H.
    rewrite <- Rmult_1_l.
    apply Rmult_le_compat_r.
    exact (Rinv_nonneg hk). exact (Rminus_pow_le_one m hk).
    field_simplify_eq. ring.
    split.
    assert (-(k-1) = 1 - k) by ring. rewrite <- H.
    exact (Ropp_neq_0_compat (k-1) (k_le_one_ne_one hk)).
    exact (k_le_one_ne_one hk).
   rewrite <- Hn0. refine (dist_iter_fun_aux_2 _ hk Hf _ _ _ Heps Hxfx). 
    rewrite Hn0. omega.
Qed.        
