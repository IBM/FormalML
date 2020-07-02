
Require Import Reals.
Require Import pmf_monad.
Require Import domfct.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.


Section MDPs.

Open Scope monad_scope.


Record MDP := mkMDP {
 (* State and action spaces. *)
 state : Type;
 act  : Type;
 (* Probabilistic transition structure. 
    t(s,a,s') is the probability that the next state is s' given that you take action a in state s. *)
 t : state -> act -> Pmf state;
 (* Reward when you are at state s. *)
 reward : state -> R                                
}.

Definition policy (M : MDP) := M.(state) -> M.(act).

(* Let's make a Kliesli arrow out of a policy. This can be interpreted as a |S| × |S| stochastic matrix. *)

Definition stoch_mx {M : MDP} (σ : policy M): M.(state) -> Pmf M.(state) := fun s => M.(t) s (σ s).

Variable (M : MDP).
Variable (s : M.(state)).
Variable (σ : policy M).
Check (Pmf_pure s >>= (stoch_mx σ)). 
Check (Pmf_pure s >>= (stoch_mx σ)) >>= (stoch_mx σ). 
Check Pmf_bind.


Fixpoint bind_iter {M : MDP} (σ : policy M) (n : nat) (s : M.(state)) : Pmf M.(state) :=
  match n with
  | 0 => Pmf_pure s
  | S k => Pmf_bind (stoch_mx σ) (bind_iter σ k s) (* can't use bind notation here why?? *)
  end.


End MDPs.
