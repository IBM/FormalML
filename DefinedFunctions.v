Require Import Rbase.
Require Import String.
Require Import List.

Module DefinedFunctions.

Section Definitions.

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

End Definitions.

Section FreeVariablesExample.

(* helper function for free_variables. *)
Fixpoint concat (l1 l2 : list string) :=
  match l1 with
  | nil => l2
  | cons hd tl => cons hd (concat tl l2)
  end.

Fixpoint unique (l : list string) :=
  match l with
  | nil => l
  | cons hd tl => if (in_dec string_dec hd tl) then (unique tl) else cons hd (unique tl)
  end.

(* An example of a recursively defined function over an inductive data type.
 * computes the set of all variables occurring in a defined function.
 * note: may containing names more than once. *)
Fixpoint free_variables (f : DefinedFunction) := unique
  match f with
  | Number x => nil
  | Var name => cons name nil
  | Plus l r => concat (free_variables l) (free_variables r)
  | Minus l r => concat (free_variables l) (free_variables r)
  | Times l r => concat (free_variables l) (free_variables r)
  | Divide l r => concat (free_variables l) (free_variables r)
  | Max l r => concat (free_variables l) (free_variables r)
  | Abs e => free_variables e
  | Log e => free_variables e
  | Exp e => free_variables e
  end.

End FreeVariablesExample.

End DefinedFunctions.

