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
Require Import BinInt.
Require Import String.
Local Open Scope list.

Existing Instance floatish_IEEE.

Example test :=
  mk_env_entry (Name "f", DTfloat) (FfromZ 1)%Z ::
               mk_env_entry (Name "v", DTVector 3) (ConstVector 3 ((FfromZ (-2)))%Z) :: 
               mk_env_entry (Name "m", DTMatrix 2 3) (ConstMatrix 2 3 (FfromZ 3))%Z :: nil.
Module API.
  Example opt := @Gen_NN.opt floatish_IEEE.
  Example test_env := test.

  Example discard_first {A} (l:list (list A)) : list (list A) := List.map (@List.tl A) l.
  
  End API.

Extraction "NnoptExtracted" API.

