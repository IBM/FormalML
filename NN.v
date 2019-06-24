Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Arith.
Require Import String.

Module NN.

(* A subset of defined functions *)
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

Section SeriesDivergence.

Definition converges (s: nat -> R) :=
  exists sum:R, infinite_sum s sum.

Definition diverges (s: nat -> R) : Prop :=
  ~(converges s).

Definition diverges_right (s: nat -> R) : Prop :=
  forall m: R,
    exists N: nat,
      forall n: nat, 
        n >= N -> Rlt (s n) m.

Definition diverges_left (s: nat -> R) : Prop :=
  forall m: R,
    exists N: nat,
      forall n:nat, 
        n >= N -> Rgt (s n) m.

End SeriesDivergence.

Local Open Scope R_scope.
Definition Assumption_C_1 (ak : nat -> R) : Prop :=
  let 
    ak_squared (n : nat) := (ak n)^2
  in
    (forall n, ak n >= 0) /\
    diverges_right ak /\
    converges ak_squared.
Local Close Scope R_scope.

End NN.
