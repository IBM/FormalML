Require Import Reals.
Require Import pmf_monad.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.


Section MDPs.

Open Scope monad_scope.

Record MDP := mkMDP {
 state : Type;
 act  : Type;                                   
 t : state -> act -> Pmf state;
 reward : state -> R                                
}.



End MDPs.
