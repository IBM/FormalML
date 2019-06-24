Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Arith.
Require Import String.

Module NN.

Section DefinedFunctions.

(* Terms are defined functions with free variables. *)
Inductive Term : Type :=
  | Number (x : R)
  | Var (name : string)
  | Plus (l r : Term)
  | Minus (l r : Term)
  | Times (l r : Term)
  | Divide (l r : Term)
  | Exp (e : Term)
  | Log (e : Term)
  | Abs (e : Term)
  | Max (l r : Term).

(* DefinedFunctions are either base terms or applications of base terms to a list of arguments *)
Inductive DefinedFunction : Type :=
  | BaseTerm (e: Term)
  | App (e: Term) (args: string -> DefinedFunction).

(* Replaces all varriables in e with new terms. *)
Fixpoint DF_apply (e: Term) (args: string -> Term) :=
  match e with
  | Number x => Number x
  | Var name => args name
  | Plus l r => Plus (DF_apply l args) (DF_apply r args)
  | Times l r => Plus (DF_apply l args) (DF_apply r args)
  | Minus l r => Plus (DF_apply l args) (DF_apply r args)
  | Divide l r => Plus (DF_apply l args) (DF_apply r args)
  | Max l r => Plus (DF_apply l args) (DF_apply r args)
  | Exp e => Exp (DF_apply e args)
  | Log e => Exp (DF_apply e args)
  | Abs e => Exp (DF_apply e args)
  end.

End DefinedFunctions.

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
Definition Assumption_C_2 (x: nat -> R) : Prop :=
  exists M : R,
    forall k: nat, Rabs (x k) < M.

(* TODO *)
Definition Assumption_C_3 := 1=1.

Definition Assumption_C (alpha: nat -> R) (x : nat -> R) : Prop :=
  Assumption_C_1 alpha /\ Assumption_C_2 x /\ Assumption_C_3.

Local Close Scope R_scope.

End AssumptionC.

End NN.
