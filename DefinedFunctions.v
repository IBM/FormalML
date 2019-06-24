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

(*
Explanation:
in_dec is the decision procedure for deciding whether an element is in a List.
It takes 3 arguments:
  1. a decision procedure for determining if two members the parameterizing type are equal.
     For strings, this is string_dec (defined in Coq.Strings.String).
  2. the element to search for
  3. the list to search in.

Notice that when you define this function, Coq will print "concat is recursively defined (descreasing on the 1st argument)"
The part about "decreasing on the 1st argument" is important -- your recursive
definitions must always descrease. So, for example, the following definition
will not work:

Fixpoint loop (l : list string) := (loop l)
*)
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



(* We need ot open the string scope in order to use "a" as a string. *)
Open Scope string_scope.
Theorem ex1 : (free_variables (Plus (Var "a") (Var "b"))) = "a"::"b"::nil.
Proof.
(* Reflexivity doesn't need syntactically identical things on either side of =. 
 * It suffices that the left-hand side beta-reduced to the right-hand side. *)
reflexivity.
Qed.

Close Scope string_scope.

End FreeVariablesExample.

End DefinedFunctions.

