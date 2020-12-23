(* Configuration of the extraction *)

Require Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt ExtrOcamlNatInt.
Extraction Blacklist String List.

Require Import Reals.
Require LibUtilsCoqLibAdd.
Require String.
Require mdp_turtle mdp.
Local Open Scope list.

Module API.

  Definition MDP : Type := mdp.MDP.
  Definition Grid (m n :nat) : Type := mdp_turtle.turtle_grid m n.

  Definition turtle_color := mdp_turtle.turtle_color.
  
  Definition turtle_white := mdp_turtle.turtle_white.
  Definition turtle_green:= mdp_turtle.turtle_green.
  Definition turtle_star := mdp_turtle.turtle_star.
  Definition turtle_red := mdp_turtle.turtle_red.
  
  Definition turtle_mdp (m n:nat) {g:Grid (S m) (S n)} : MDP := mdp_turtle.turtle_mdp g.

  Definition inner_length {A} (g:list (list A))
    := match g with
       | nil => 0
       | x::_ => length x
       end.
      
  Definition make_grid (g:list (list turtle_color)) : option (Grid (length g) (inner_length g)).
  Admitted.

  Definition CeRtL_mdp : MDP :=  mdp_turtle.CeRtL_mdp.

  Definition show_grid (m n:nat) {g:Grid m n} : String.string
    := LibUtilsCoqLibAdd.toString (ToString:=mdp_turtle.turtle_grid_tostring) g.

  Definition CeRtL_run_optimal (γ : R) (approx_iters:nat) (steps:nat) : String.string := mdp_turtle.CeRtL_run_optimal γ approx_iters steps.

End API.

(* Workaround for https://github.com/coq/coq/issues/13288 , suggested by a comment on the issue.  
 Coq extraction currently creates a clash between the extracted Decimal.int and the 
 ocaml int type.
*)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction "extracted/TurtleExtracted" API.
