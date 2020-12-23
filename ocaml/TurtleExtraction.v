(* Configuration of the extraction *)

Require Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt ExtrOcamlNatInt.
Extraction Blacklist String List.

Require Import mdp_turtle.
Local Open Scope list.

Module API.


End API.

(* Workaround for https://github.com/coq/coq/issues/13288 , suggested by a comment on the issue.  
 Coq extraction currently creates a clash between the extracted Decimal.int and the 
 ocaml int type.
*)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extraction "extracted/TurtleExtracted" API.
