Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Arith.
Require Import String.
Require Import Vector.

Module NN.

Section DefinedFunctions.

(* Terms are defined functions with free variables. *)
Inductive DefinedFunction : Type :=
  | Number (x : R)
  | Var (name : string)
  | Plus (l r : DefinedFunction)
  | Minus (l r : DefinedFunction)
  | Times (l r : DefinedFunction)
  | Divide (l r : DefinedFunction)
  | Exp (e : DefinedFunction)
  | Log (e : DefinedFunction)
  | Abs (e : DefinedFunction)
  | Max (l r : DefinedFunction).

(* Replaces all varriables in e with new terms. *)
Fixpoint DF_apply (e: DefinedFunction) (args: string -> DefinedFunction) :=
  match e with
  | Number x => Number x
  | Var name => args name
  | Plus l r => Plus (DF_apply l args) (DF_apply r args)
  | Times l r => Times (DF_apply l args) (DF_apply r args)
  | Minus l r => Minus (DF_apply l args) (DF_apply r args)
  | Divide l r => Divide (DF_apply l args) (DF_apply r args)
  | Max l r => Max (DF_apply l args) (DF_apply r args)
  | Exp e => Exp (DF_apply e args)
  | Log e => Log (DF_apply e args)
  | Abs e => Abs (DF_apply e args)
  end.

End DefinedFunctions.

Section Vectors.
(* I'm using Coq.Vectors.Vector. *)

(* The type of real-valued vectors
 * TODO surely there's a vector space library for Coq? *)
Definition rvector : nat -> Set := t R.

(* A norm on real-valued vectors
 * TODO define a proper norm, or find a real vector space library. *)
Fixpoint norm (n: nat) (vector: rvector n) := R0.

End Vectors.

Section SeriesDivergence.

Definition converges (s: nat -> R) :=
  exists sum:R, infinite_sum s sum.

Definition diverges (s: nat -> R) : Prop :=
  ~(converges s).

Definition diverges_right (s: nat -> R) : Prop :=
  forall m: R,
    exists N: nat,
      forall n: nat, 
        n >= N -> Rgt (s n) m.

Definition diverges_left (s: nat -> R) : Prop :=
  forall m: R,
    exists N: nat,
      forall n:nat, 
        n >= N -> Rlt (s n) m.

End SeriesDivergence.

Section AssumptionC.

Local Open Scope R_scope.
Definition Assumption_C_1 (ak : nat -> R) : Prop :=
  let 
    ak_squared (n : nat) := (ak n)^2
  in
    (forall n, ak n >= 0) /\
    diverges_right ak /\
    converges ak_squared.

(* note: classical sup = LEM, and isn't needed anyway as long as we can specialize the definition of the stochastic subgradients a little bit to be a sequence indexable by nat *)
Definition Assumption_C_2 (d: nat) (x: nat -> rvector d) : Prop :=
  exists M : R,
    forall k: nat, (norm d (x k)) < M.

(* TODO *)
Definition Assumption_C_3 := 1=1.

Definition Assumption_C (d: nat) (alpha: nat -> R) (x : nat -> rvector d) : Prop :=
  Assumption_C_1 alpha /\ Assumption_C_2 d x /\ Assumption_C_3.

Local Close Scope R_scope.

End AssumptionC.

End NN.
