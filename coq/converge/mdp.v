
Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy.
Require Import pmf_monad.
Require Import domfct.
Require Import Sums.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.


Section extra.
Open Scope list_scope.
Open Scope R_scope.

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

Lemma list_sum_mult_const (c : R) (l : list R) :
  list_sum (map (fun z => c*z) l) = c*list_sum (map (fun z => z) l).
Proof. 
  induction l.
  simpl; lra.
  simpl in *. rewrite IHl. 
  lra. 
Qed.   

Lemma list_sum_const_mult_le {x y : R} (l : list R) (hl : list_sum l = R1) (hxy : x <= y) :
  list_sum (map (fun z => x*z) l) <= y.
Proof.
  rewrite list_sum_mult_const. rewrite map_id. 
  rewrite hl. lra. 
Qed. 

Lemma list_sum_fun_mult_le {x y D : R} {f g : R -> R}(l : list R)(hf : forall z, f z <= D) (hg : forall z , 0 <= g z) :
  list_sum (map (fun z => (f z)*(g z)) l) <= D*list_sum (map (fun z => g z) l).
Proof.
  induction l.
  simpl. lra.
  simpl. rewrite Rmult_plus_distr_l.
  assert (f a * g a <= D * g a). apply Rmult_le_compat_r. exact (hg a). exact (hf a).
  exact (Rplus_le_compat _ _ _ _ H IHl).   
Qed. 

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
 list_sum (map (fun y : nonnegreal * state _ => reward _ (snd y) * (fst y)) (bind_stoch_iter n init).(outcomes)).

  
(* Expected reward at time 0 is equal to the reward. *)
Lemma expt_reward0_eq_reward : forall init : M.(state), expt_reward init 0 = reward _ init.
Proof.
  intros init.
  unfold expt_reward ; simpl.
  lra.
Qed.

(* Bounded rewards imply bounded expected rewards for all iterations and all states. *)
Lemma expt_reward_le_max (init : M.(state)) :
  (exists D, forall s : M.(state), reward _ s <= D)  ->
  (exists D:R, forall n:nat, expt_reward init n <= D). 
Proof. 
  intros (D,H). 
  exists D. unfold expt_reward. intros n. 
  generalize (bind_stoch_iter n init) as l.
  intros l.
  rewrite <- Rmult_1_r.
  change (D*1) with (D*R1). 
  rewrite <- (sum1_compat l). 
  induction l.(outcomes). 
  * simpl; lra.
  * simpl in *. rewrite Rmult_plus_distr_l.
    assert (reward M (snd a) * fst a  <=  D * fst a). apply Rmult_le_compat_r. apply cond_nonneg.
    apply H. 
    now apply Rplus_le_compat. 
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

Definition ltv_part (N : nat) := sum_f_R0 (fun n => γ^n * (expt_reward σ init n)) N. 
Definition ltv_part' (N : nat) := sum_f_R0' (fun n => γ^n * (expt_reward σ init n)) N. 

Lemma ltv_part0_eq_reward : ltv_part 0 = reward _ init.
Proof.
  unfold ltv_part;simpl.
  rewrite expt_reward0_eq_reward. lra.
Qed.

Check sum_n_m.
Lemma ltv_part_le (N : nat) :  (exists D, forall s : M.(state), reward _ s <= D) -> exists D : R , (ltv_part N) <= sum_f_R0 (fun n => γ^n * D) N.
Proof.
  intros Hd.
  destruct (expt_reward_le_max σ init Hd) as [D HD]. 
  exists D. unfold ltv_part.  apply sum_Rle. 
  intros n0 Hn0. 
  apply Rmult_le_compat_l.
  apply pow_le ; firstorder.
  apply HD. 
Qed. 


Lemma sum_geom (D : R) : infinite_sum (fun n => D*γ^n) (D/(1 - γ)).
Proof.
  rewrite infinite_sum_infinite_sum'.
  apply infinite_sum'_mult_const.
  rewrite <- infinite_sum_infinite_sum'.
  apply is_series_Reals. apply is_series_geom.
  rewrite Rabs_pos_eq. lra. lra. 
Qed.


Lemma ltv : exists D, infinite_sum ltv_part D. 
Proof.
  
Admitted. 
End ltv.

  



        
