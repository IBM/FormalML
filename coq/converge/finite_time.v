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
Import MonadBaseNotation. 

Section ltv_fin.
Open Scope R_scope. 
Context (M : MDP) (γ : R).
Context (hγ : (0 <= γ < 1)%R).

Arguments t {_}.
Arguments reward {_}.

Check step_expt_reward.

Definition kliesli_iter_left (Π : list(dec_rule M)) (init : M.(state)) : Pmf M.(state):=
  fold_left (fun p π => Pmf_bind p (fun s => t s (π s))) Π (ret init).

Definition kliesli_iter_right (Π : list(dec_rule M)) (init : M.(state)) : Pmf M.(state):=
  fold_right (fun π p => Pmf_bind p (fun s => t s (π s))) (ret init) Π.

Definition expt_reward (Π : list(dec_rule M)) (init : M.(state)) (σ : dec_rule M)
  : R :=
  expt_value (kliesli_iter_left Π init) (step_expt_reward σ).

(*  match (rev Π) with
  | nil => 0
  | π :: Π' =>  expt_value (kliesli_iter_right Π' init) (step_expt_reward π)
  end.
*)


Theorem expt_reward_1 π :
  forall s (σ : dec_rule M), expt_reward [π] s σ = expt_value (t s (π s)) (step_expt_reward σ).
Proof.
intros.   
unfold expt_reward.
unfold kliesli_iter_left.
simpl. rewrite expt_value_bind.
now rewrite expt_value_pure.
Qed.

Theorem expt_reward_2 (π0 π1 : dec_rule M) :
  forall s, expt_reward (π0 :: π1 :: nil) s = expt_value (t s (π0 s)) (step_expt_reward π1).
Proof.
  intros.
  unfold expt_reward.
  simpl.
  rewrite expt_value_bind.
  rewrite expt_value_pure.
  reflexivity.
Qed.

Theorem expt_reward_3 (π0 π1 π2 : dec_rule M) :
  forall s, expt_reward (π0 :: π1 :: π2 :: nil) s =
       expt_value (t s (π0 s)) (expt_reward (π1 :: π2 :: nil)).
Proof.
  intros.
  unfold expt_reward.
  simpl. rewrite expt_value_bind.
  rewrite expt_value_bind.
  rewrite expt_value_pure.
  f_equal.
  apply functional_extensionality.
  intros.
  rewrite expt_value_bind.
  rewrite expt_value_pure.
  reflexivity.
Qed.

Definition ltv_gen (Π : list(dec_rule M)) :=
  fun s : M.(state) =>  sum_f_R0' (fun n => γ^n*expt_reward (firstn (S n) Π) s)(length Π).

Lemma ltv_gen_1 π : forall s, ltv_gen [π] s = step_expt_reward π s.
Proof.
  intros.
  unfold ltv_gen.
  simpl. rewrite expt_reward_1.
  lra.
Qed. 

Lemma ltv_gen_nil : forall s, ltv_gen nil s = 0.
Proof.
  intros s. 
  (* Why won't simpl beta reduce here?*)
  cbn ; lra.
Qed.

Lemma expt_value_sum_f_R0' {A : Type} (p :Pmf A) f N :
  expt_value p (fun a => sum_f_R0' (fun n => f n a) N) =
  sum_f_R0' (fun n => expt_value p (f n)) N.
Proof.
  induction N.
  - simpl. now rewrite expt_value_zero.
  - simpl. rewrite expt_value_add. rewrite IHN.
    reflexivity.
Qed.


Lemma expt_value_sum_f_R0'_const_mul {A : Type} (p :Pmf A) (c : R) f N :
  expt_value p (fun a => c*sum_f_R0' (fun n => f n a) N) =
  c*sum_f_R0' (fun n => expt_value p (f n)) N.
Proof.
  induction N.
  - simpl. rewrite expt_value_const_mul. now rewrite expt_value_zero.
  - simpl. rewrite Rmult_plus_distr_l.
    rewrite <-sum_f_R0'_mult_const.
    rewrite expt_value_const_mul.
    rewrite expt_value_add.
    rewrite Rmult_plus_distr_l.
    f_equal. rewrite <-expt_value_const_mul.
    rewrite IHN. rewrite sum_f_R0'_mult_const.
    reflexivity.
Qed.

Lemma ltv_gen_2 π π1 : forall s,
    ltv_gen (π :: [π1]) s = (step_expt_reward π s) +
                         γ*expt_value (t s (π s)) (ltv_gen [π1]).
Proof.
  intros.
  unfold ltv_gen.
  simpl. rewrite expt_reward_1.
  f_equal. lra.
  f_equal. lra.
  rewrite expt_reward_2.
  f_equal. cbn. apply functional_extensionality.
  intro s0. ring.
Qed.

Lemma expt_reward_cons π πs:
  forall s, expt_reward (π :: πs) s = expt_value (t s (π s)) (expt_reward πs).
Proof.
  intros.
  Print step_expt_reward.
  unfold expt_reward. simpl.
  induction πs.
  - rewrite expt_reward_1. unfold expt_reward.
    simpl.
    Admitted.
            
  
Lemma ltv_gen_cons_aux π (x : nat) (d : dec_rule M) πs :
 forall s,  expt_reward (π :: firstn (S x) (d :: πs)) s =
   expt_value (t s (π s)) (fun a : state M => expt_reward (d :: firstn x πs) a).
Proof.
  intros.
  rewrite firstn_cons.
  rewrite expt_reward_cons. reflexivity.
  unfold expt_reward. 
  induction πs.
  -- unfold expt_reward. simpl.
     

    
 Lemma ltv_gen_cons π πs : forall s,
    ltv_gen (π :: πs) s = (step_expt_reward π s) +
                         γ*expt_value (t s (π s)) (ltv_gen πs).
Proof.
  intros s.
  unfold step_expt_reward.
  unfold ltv_gen.
  assert (Hl : length (π :: πs) = S(length (πs))) by reflexivity.
  rewrite Hl.
  rewrite (sum_f_R0'_split _ _ 1).
  simpl. rewrite expt_reward_1.
  f_equal. unfold step_expt_reward ; lra.
  rewrite <-expt_value_const_mul.
  rewrite expt_value_sum_f_R0'_const_mul.
  rewrite <-sum_f_R0'_mult_const.
  assert (Hl' : (length πs = length πs - 0)%nat) by lia.
  rewrite <-Hl'.
  apply sum_f_R0'_ext.
  intros. rewrite expt_value_const_mul.
  rewrite <-Rmult_assoc.
  f_equal. rewrite pow_add. admit.
  destruct πs.
  - simpl in H. firstorder.
  - unfold expt_reward. simpl.

  
Section ltv_gen.

Open Scope R_scope. 
Context {M : MDP} (γ : R).
Context (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Lemma const_stream_eq {A} (a : A) : forall n : nat, a = Str_nth n (const a).
Proof.
  unfold Str_nth ; induction n ; trivial.
Qed.

Lemma str_nth_cons_zero {A} (a : A) (π : Stream A) : Str_nth 0 (Cons a π) = a.
Proof.
  now unfold Str_nth ; simpl. 
Qed.


Lemma str_nth_cons_one {A} (a : A) (π : Stream A) : Str_nth 1 (Cons a π) = hd π.
Proof.
  now unfold Str_nth ; simpl. 
Qed.

Definition ltv_gen (π : Stream (dec_rule M)) : M.(state) -> R :=
  fun s => Series (fun n => γ^n * expt_value (bind_stoch_iter_str π n s)
                                       (fun s => step_expt_reward (hd π) s)).

(* Fix this proof to remove funext axiom. *)
Theorem ltv_gen_ltv : forall s : M.(state), forall σ : dec_rule M, ltv γ σ s = ltv_gen (const σ) s.
Proof. 
  intros s σ.
  apply Series_ext. unfold bind_stoch_iter_str. simpl.
  intro n. f_equal. unfold expt_reward.
  assert (forall n, forall s,  t s (Str_nth n (const σ) s)  = t s (σ s)).
  intros n0 s0. f_equal. now erewrite <-const_stream_eq. 
  f_equal. unfold bind_stoch_iter. simpl. f_equal. apply functional_extensionality.
  intro x. f_equal. apply functional_extensionality. intros x0 ; eauto.
Qed.

Lemma Str_nth_succ_cons {A} (n : nat) (d : A) (π : Stream A) :
  Str_nth (S n) (Cons d π) = Str_nth n π.
Proof.
  induction n.
  - unfold Str_nth. simpl. reflexivity.
  - unfold Str_nth. simpl. reflexivity.
Qed.

Lemma Str_nth_hd_tl {A} (n : nat) (π : Stream A) :
  Str_nth (S n) π = Str_nth n (tl π).
Proof.
  induction n ; unfold Str_nth ; trivial. 
Qed.

Lemma Pmf_bind_comm_stoch_bind_str (n : nat) (π : Stream (dec_rule M)) (init : state M):
  Pmf_bind (bind_stoch_iter_str π n init) (fun a : state M => t a (Str_nth n π a)) =
  Pmf_bind (t init (Str_nth n π init)) (fun a : state M => bind_stoch_iter_str π n a).
Proof.
  revert π. 
  induction n. 
  * unfold bind_stoch_iter_str. simpl. intros π. rewrite Pmf_bind_of_ret.
    now rewrite Pmf_ret_of_bind.
  * unfold bind_stoch_iter_str in *. simpl. intro π. rewrite Str_nth_hd_tl. 
    setoid_rewrite (IHn (tl π)).
    now rewrite Pmf_bind_of_bind.
Qed.


Definition expt_ltv_gen (π : Stream (dec_rule M)) (p : Pmf M.(state)) : R :=
  expt_value p (ltv_gen π).

(* Expected reward at time 0 is equal to the reward for a nonstationary policy. *)

Lemma expt_reward0_eq_reward_gen (π : Stream(dec_rule M)) : forall init : M.(state), expt_reward (hd π) init 0 = (step_expt_reward (hd π) init).
Proof.
  intros init.
  unfold expt_reward. unfold bind_stoch_iter. simpl.
  now rewrite expt_value_pure.
Qed.


Lemma expt_reward_gen_succ (n : nat) (π : Stream (dec_rule M)) (init: state M) :
  expt_reward (Str_nth (S n) π) init (S n) = expt_value (t init (Str_nth n (tl π) init)) (fun s => expt_reward (Str_nth n (tl π)) s n).
Proof.
  rewrite expt_reward_succ.
  rewrite <-expt_value_bind. rewrite Pmf_bind_comm_stoch_bind. 
  rewrite Str_nth_hd_tl.
  rewrite expt_value_bind.
  unfold expt_reward. reflexivity.
Qed.

End ltv_gen. 
