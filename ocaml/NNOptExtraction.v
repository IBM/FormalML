(* Configuration of the extraction *)

Require Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt ExtrOcamlZInt.
Extraction Blacklist String List.

Require Import FloatishIEEE.
Require Import ExtrFloatishIEEE.

(* Require Import ExtrR. *)
(* Our stuff modules *)

Require Gen_NN.
Require Import DefinedFunctions.
Require Import FloatishDef.
Require Import String.
Local Open Scope string.
Local Open Scope list.

Existing Instance floatish_IEEE.

Example test :=
  mk_env_entry (Name "f", DTfloat) (FfromZ 1) ::
               mk_env_entry (Name "v", DTVector 3) (ConstVector 3 (FfromZ 2)) :: 
               mk_env_entry (Name "m", DTMatrix 2 3) (ConstMatrix 2 3 (FfromZ 3)) :: nil.
Module API.
  Example opt := @Gen_NN.opt floatish_IEEE.
  Example test_env := test.
End API.

Extraction "NnoptExtracted" API.

