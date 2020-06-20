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

Search comp.

Fixpoint iter_fun (n : nat) (f : V -> V) (v : V) :=
  match n with
  | 0 => v
  | S k => f (iter_fun k f v)
  end.

Search pow.

Lemma Rpow_gt_0 (n0 : nat) {k : R} (hk : k > 0) : k^n0 > 0.
Proof.
  induction n0 as [| n0 iH0].
  simpl. firstorder. 
  simpl. exact (Rmult_gt_0_compat _ _ hk iH0).
Qed.

Lemma dist_iter_fun_aux_1 {f : V -> V}{k eps : R} (x : V) (hk : 0 < k < 1) (Hf : is_lipschitz f k) : forall (n : nat) , (eps > 0) -> 
      ball x eps (f x) -> ball (iter_fun n f x) ((k^n)*eps) (iter_fun (n+1) f x).
Proof.
  intros n Heps H.
  destruct Hf as [Hk Hp].
  
    induction n as [| n0 iH].
    simpl. assert (1*eps = eps) by ring. now rewrite H0.
    simpl. 
    specialize (Hp (iter_fun n0 f x) (iter_fun (n0+1) f x) ((k^n0 * eps))).
    assert (k * k^n0 * eps = k*(k^n0 * eps)) by ring. rewrite H0. apply Hp.
    apply (Rmult_gt_0_compat _ _). exact (Rpow_gt_0 _ Hk).
    assumption.
    exact iH.
Qed.

Search (_ <> 0).
Search ((_ - _ = 0)).
Check Rminus_diag_uniq.
Search "irrefl".

Lemma dist_iter_fun_aux_2 {f : V -> V}{k eps : R} (x : V) (hk : 0 < k < 1)(Hf : is_lipschitz f k) :
  forall (m  n : nat), (m > 0)%nat -> (eps > 0) ->
                let D := k^n * (k^m - 1)/(k-1) in
                ball x eps (f x) -> ball (iter_fun n f x) (D*eps) (iter_fun (n+m) f x).
Proof.
  intros m n Hm0 eps0 D Hxfx.
  induction m as [ | m0 IHm0].
  - exfalso. omega.
  - destruct m0. replace D with (k^n). exact (dist_iter_fun_aux_1 x hk Hf _ eps0 Hxfx).
    unfold D. field_simplify. reflexivity.
    intro notr.
    assert (k=1) by exact (Rminus_diag_uniq _ _ notr). rewrite H in hk.
    destruct hk. apply (Rlt_irrefl _ H1).
    rewrite Nat.add_succ_r. simpl.
    assert (S m0 > 0)%nat by omega. intuition.
Admitted.
