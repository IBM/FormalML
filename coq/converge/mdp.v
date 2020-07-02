
Require Import Reals.
Require Import pmf_monad.
Require Import domfct.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.


Section m.
Open Scope monad_scope.

(* Applies a function to an initial argument n times *)
Fixpoint applyn {A} init g (n : nat) : A :=
  match n with
  | 0 => init
  | S k => g (applyn init g k)
  end.


Context {M:Type->Type}.
Context {Mm:Monad M}.
Context {A:Type}.
Context (unit:A) (f:A->M A).

End m.

Definition bind_iter {M:Type->Type} {Mm:Monad M} {A:Type} (unit:A) f := applyn (ret unit) (fun y => bind y f).

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

Definition bind_stoch_iter {M : MDP} (s : M.(state)) (σ : policy M) := bind_iter s (stoch_mx σ).

End MDPs.
