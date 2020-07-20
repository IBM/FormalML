Require Import mdp pmf_monad Reals Sums.
Require Import Coquelicot.Hierarchy Coquelicot.Series Coquelicot.Lim_seq Coquelicot.Rbar.
Require Import Omega. 


(*
****************************************************************************************
This file tries to prove a stochastic convergence result of Dvoretzky. The proof follows
section 8 of https://projecteuclid.org/download/pdf_1/euclid.bsmsp/1200501645. 
Dvoretzky's general theorem is what is used to prove convergence of Robbins-Monro and 
Kiefer-Wolfowitz. 
We formalize the simpler theorem in hopes that it might be useful for other iteration 
schemes.
****************************************************************************************
*)

Section inf_prod.

Fixpoint part_prod (a : nat -> posreal) (n : nat) : R :=
  match n with
  | 0 => a 0%nat
  | S k => a (S k) * (part_prod a k)
  end.

Lemma part_prod_pos (a : nat -> posreal) (N : nat) : 0 < part_prod a N.
Proof. 
  induction N.
  - simpl. apply cond_pos.
  - simpl. apply Rmult_lt_0_compat. apply cond_pos. apply IHN. 
Qed. 
    
Lemma sum_n_prod (a : nat -> posreal) (N : nat) : sum_n (fun n => ln (a n)) N = ln (part_prod (fun n => a n) N).
Proof.
  induction N. 
  - simpl. unfold sum_n. now rewrite sum_n_n. 
  - simpl. unfold sum_n. rewrite sum_n_Sm. rewrite ln_mult. rewrite <-IHN. 
    unfold sum_n. apply Rplus_comm.
    apply cond_pos. apply part_prod_pos. 
    omega. 
Qed.

Definition infinite_product (a : nat -> posreal) := Lim_seq (fun n => part_prod a n). 


Lemma ex_product_iff_ex_log_sum (a : nat -> posreal) : ex_lim_seq(fun n => part_prod a n) <-> ex_series (fun N => sum_n (fun n => ln (a n)) N).
Proof.
  (*Use infinite_sum_is_lim_seq. *)
  split. 
  - intros H. destruct H as [l Hl].
    apply ex_series_Reals_1.
    exists (ln (real l)).
    
Admitted.
    
End inf_prod. 

Section iter.
Context {A : Type}.
Context (p : Pmf A). 
Context (X Y : nat -> A -> R).
Context (F : nat -> R).
Context (T : nat -> R -> R). 

Fixpoint iter_scheme (n : nat) :=
  match n with
  | 0 => (fun a => Y 0 a) 
  | S k => (fun a => T k (iter_scheme k a) + Y k a)
  end.

Definition variance (p : Pmf A) (f : A -> R) :=
  expt_value p (fun a => (f a - (expt_value p f))^2). 

Lemma aux1 (hY : forall n, expt_value p (Y n) = 0) :
  forall n, expt_value p (fun a => (Y n a)*(T n (iter_scheme n a))) = 0.
Proof.
Admitted.


Lemma aux2 (k : nat) : forall a,  (iter_scheme (S k) a)^2 = (T k (iter_scheme k a))^2 + (Y k a)^2 + 2*(Y k a)*(T k (iter_scheme k a)). 
Proof.
  intros a.
  simpl. ring.
Qed.


End iter.
