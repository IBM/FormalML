Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy Coquelicot.SF_seq.
Require Import pmf_monad mdp Permutation fixed_point Finite LibUtils. 
Require Import Sums Coq.Reals.ROrderedType.
Require Import micromega.Lra.
Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Equivalence RelationClasses EquivDec Morphisms.
Require Import ExtLib.Structures.Monad.

(*
****************************************************************************************
In this file we only consider a finite list of policies.  
****************************************************************************************
*)

Import ListNotations.


Section ltv_fin.
Open Scope R_scope. 
Context (M : MDP) (γ : R).
Context (hγ : (0 <= γ < 1)%R).

Arguments t {_}.
Arguments reward {_}.

Check step_expt_reward.

Definition kliesli_iter_left (Π : list(dec_rule M)) (init : M.(state)) : Pmf M.(state):=
  fold_left (fun p π => Pmf_bind p (fun s => t s (π s))) Π (ret init).

Definition kliesli_iter_left_vector (init : Pmf M.(state)) (Π : list(dec_rule M))  : Pmf M.(state):=
  fold_left (fun p π => Pmf_bind p (fun s => t s (π s))) Π init.


Lemma ff_left {A B: Type} (f: A -> B -> A) (π0: B) (πs: list B) (s: A):  fold_left f πs (f s π0) = fold_left f (π0::πs) s.
Proof.
  simpl. reflexivity.
Qed.


Lemma kliesli_iter_left_cons0 π πs: forall sv,
    kliesli_iter_left_vector  (Pmf_bind sv (fun s0 => t s0 (π s0))) πs
    = kliesli_iter_left_vector sv (π :: πs).
Proof.
  intros. 
  unfold kliesli_iter_left_vector. rewrite <- ff_left. reflexivity.
Qed.

Lemma Pmf_unity {A} (p: Pmf A): Pmf_bind p (fun s0: A => Pmf_pure s0) = p.
Proof.
  rewrite Pmf_ret_of_bind.
  reflexivity.
Qed.

Definition expt_reward_vector (sv : Pmf M.(state)) (Π : list(dec_rule M))  (σ : dec_rule M)
  : R :=
  expt_value (kliesli_iter_left_vector sv Π ) (step_expt_reward σ).


Definition ltv_gen (sv: Pmf M.(state)) (Π : list(dec_rule M)) :=
    match Π with
    | nil => 0
    | π :: Π' => sum_f_R0' (fun n =>
                            match nth_error Π n with
                            | Some σ => γ^n*expt_reward_vector sv (firstn n Π) σ
                            | None => 0
                            end) (length Π)
    end.

Lemma ltv_gen_cons_term1 sv π: expt_reward_vector sv [] π = expt_value sv (fun s : state M => expt_value (t s (π s)) (reward s (π s))).
Proof.
  unfold expt_reward_vector.
  unfold kliesli_iter_left_vector.
  unfold fold_left.
  unfold step_expt_reward.
  reflexivity.
Qed.


Lemma expt_reward_cons4 π πs σ vs:
  expt_reward_vector vs (π :: πs) σ =
  expt_reward_vector (Pmf_bind vs (fun s0 => t s0 (π s0))) πs σ.
Proof.
  unfold expt_reward_vector. rewrite kliesli_iter_left_cons0.
  reflexivity.
Qed.

Theorem ltv_gen_cons (π: dec_rule M) (πs: list(dec_rule M)) (sv: Pmf M.(state)):
  ltv_gen sv (π :: πs) = expt_value sv (step_expt_reward π) +
                         γ*(ltv_gen (Pmf_bind (sv) (fun s0 => (t s0 (π s0)))) πs).
Proof.
  intros.
  unfold step_expt_reward.
  unfold ltv_gen.
  assert (Hl: length (π :: πs) = S(length (πs))) by reflexivity.
  
  rewrite Hl.
  rewrite (sum_f_R0'_split _ _ 1) by lia.
  simpl.
  assert (HH: 0 + 1 * expt_reward_vector sv [] π =  expt_reward_vector sv [] π).
  { rewrite Rplus_comm.
    rewrite Rplus_0_r.
    rewrite Rmult_comm.
    rewrite Rmult_1_r.
    reflexivity.
  }
  rewrite HH.
  rewrite <- ltv_gen_cons_term1.
  apply Rplus_eq_compat_l.
  assert (HH1: (length πs = length πs - 0)%nat) by lia.
  rewrite <- HH1.
  
  destruct πs.
  -  simpl. ring_simplify. reflexivity.
  -  rewrite <- sum_f_R0'_mult_const.
     apply sum_f_R0'_ext.
     intros.
     replace (x + 1)%nat with (S x) by lia.
     simpl.
     apply nth_error_Some in H.
     match_destr; [| congruence].

     rewrite <- Rmult_assoc.
     f_equal.

Qed.

  


          

          

          
            
        

          

           
           
           
        

        
        
        
        
        
        
    

    
    

      
    
    
      


  
  


