Require Import List.
Require Import mdp qvalues pmf_monad Finite.
Require Import Reals RealAdd CoquelicotAdd.
Require Import utils.Utils.
Require Import Lra Lia PushNeg.
Require Import RandomVariableL2 infprod Dvoretzky Expectation.
Require Import RandomVariableFinite RbarExpectation.
Require Import Classical.
Require Import SigmaAlgebras ProbSpace.

Open Scope R_scope.

Section MDP.
  Context (M : MDP) (γ : R).

  Arguments reward {_}.
  Arguments outcomes {_}.
  Arguments t {_}.

  (*Record MDP : Type := mkMDP
  { state : Type;
    act : state -> Type;
    st_eqdec : EquivDec.EqDec state eq;
    fs : Finite state;
    fa : forall s : state, Finite (act s);
    ne : mdp.NonEmpty state;
    na : forall s : state, mdp.NonEmpty (act s);
    t : forall s : state, act s -> pmf_monad.Pmf state;
    reward : forall s : state, act s -> state -> R }*)

  (*
    How do we port this over to the new version?
    1. We will need a new definition of MDPs accounting for the RandomVariable
       and ProbSpace structure.
    2.
  *)

  Definition bellmanQ' : Rfct(sigT M.(act)) -> M.(state) -> Rfct(sigT M.(act))
  := fun W => fun s' sa => let (s,a) := sa in
                  reward s a s' + γ*Max_{act_list s'}(fun a => W (existT _ s' a)).

  (* How do we port this over to the new version?*)
