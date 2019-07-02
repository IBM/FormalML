Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Arith.
Require Import String.
Require Import Vector.

Require Import AxiomaticNormedRealVectorSpace.

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
  | Abs (e : DefinedFunction).


(* Replaces all varriables in e with new terms. *)


Local Open Scope R_scope.
Definition R2 := 2.
Local Close Scope R_scope.

(* max(a,b) == (abs(b-a) + b + a)/2
  * note: might be easier to just have a Max branch on the DF function:
  *   | Max (l r : DefinedFunction).
  *)
Definition Max (a b : DefinedFunction) :=
  Divide (Plus (Plus (Abs (Minus b a)) b) a) (Number R2).

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
Definition Assumption_C_2 (s: Set) (x: nat -> rvector s) : Prop :=
  exists M : R,
    forall k: nat, norm s (x k) < M.

(* TODO *)
Definition Assumption_C_3 := 1=1.

Definition Assumption_C (s: Set) (alpha: nat -> R) (x : nat -> rvector s) : Prop :=
  Assumption_C_1 alpha /\ Assumption_C_2 s x /\ Assumption_C_3.

Local Close Scope R_scope.

End AssumptionC.

End NN.
