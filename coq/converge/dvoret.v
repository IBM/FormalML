Require Import Reals Sums pmf_monad.
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

    
End inf_prod. 

