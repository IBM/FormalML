
Require Import Reals Coq.Lists.List.
Require Import pmf_monad.
Require Import domfct.
Require Import Sums.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.


Section extra.
Open Scope list_scope.

Import ListNotations.
(* Applies a function to an initial argument n times *)
Fixpoint applyn {A} (init : A) (g : A -> A) (n : nat) : A :=
  match n with
  | 0 => init
  | S k => g (applyn init g k)
  end.


Fixpoint Rmax_list (l : list R) : R :=
  match l with
  | nil => 0
  | (x :: xs) => Rmax x (Rmax_list xs)
  end.
  
(*
Context {M:Type->Type}.
Context {Mm:Monad M}.
Context {A:Type}.
Context (unit:A) (f:A->M A).
*)

End extra.

Definition bind_iter {M:Type->Type} {Mm:Monad M} {A:Type} (unit:A) (f : A -> M A) :=
  applyn (ret unit) (fun y => bind y f).

Section MDPs.

Open Scope monad_scope.
Open Scope R_scope.

Record MDP := mkMDP {
 (* State and action spaces. *)
 state : Type;
 act  : Type;
 (* Probabilistic transition structure. 
    t(s,a,s') is the probability that the next state is s' given that you take action a in state s.
    One can also consider to to be an act-indexed collection of Kliesli arrows of Pmf. 
 *)
 t :>  state -> act -> Pmf state;
 (* Reward when you are at state s. *)
 reward : state -> R                                
}.

Arguments outcomes {_}.

Definition policy (M : MDP) := M.(state) -> M.(act).

Context {M : MDP}.
Context (σ : policy M).

(* Construction of a Kliesli arrow out of a policy. 
   This can be interpreted as a |S| × |S| stochastic matrix. *)

Definition stoch_mx : M.(state) -> Pmf M.(state) := fun s => t _ s (σ s).

Definition bind_stoch_iter (n : nat) (init : M.(state)):= bind_iter init (stoch_mx) n.

Definition expt_reward (init : M.(state)) (n : nat) : R :=
 list_sum (seq.map (fun y : nonnegreal * state _ => reward _ (snd y) * (fst y)) (bind_stoch_iter n init).(outcomes)).

  
(* Expected reward at time 0 is equal to the reward. *)
Lemma expt_reward0_eq_reward : forall init : M.(state), expt_reward init 0 = reward _ init.
Proof.
  intros init.
  unfold expt_reward ; simpl.
  lra.
Qed.


End MDPs.

Section egs.

(* This defines a "unit reward" MDP.*)
Definition unitMDP {st0 act0 : Type} (t0 : st0 -> act0 -> Pmf st0) : MDP :=
{|
    state := st0;
    act := act0;
    t := t0;
    reward := fun s => R1
|}.

Check Rmult_1_l.
(* The expected reward for an arbitrary initial state and arbitrary policy is unity for a unit MDP. *)
Lemma expt_reward_unitMDP {t0 : R -> R -> Pmf R} :
  let M0 := unitMDP t0 in
  forall (σ0 : policy M0) (init0 : M0.(state)) (n:nat), expt_reward σ0 init0 n = R1. 
Proof.
  intros M0 σ0 init0 n. unfold expt_reward.
  simpl. rewrite <- (sum1_compat (bind_stoch_iter σ0 n init0)).
  f_equal. apply map_ext. rewrite sum1_compat.
  intros a. now rewrite Rmult_1_l.
Qed. 

End egs.

Section ltv.

Open Scope R_scope. 
Context {M : MDP} {γ : R}.
Context (σ : policy M) (init : M.(state)) (hγ : (0 <= γ < 1)%R).

Definition ltv_part (n : nat) := sum_f_R0 (expt_reward σ init) n. 
Definition ltv_part' (n : nat) := sum_f_R0' (expt_reward σ init) n. 

Lemma ltv_part0_eq_reward : ltv_part 0 = reward _ init.
Proof.
  simpl ; apply expt_reward0_eq_reward. 
Qed.

End ltv.

  



        
