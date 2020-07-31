(* Configuration of the extraction *)

Require Extraction.
Extraction Language OCaml.
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt ExtrOcamlNatInt.
Extraction Blacklist String List.

Require Import FloatishIEEE.
Require Import ExtrFloatishIEEE.

(* Require Import ExtrR. *)
(* Our stuff modules *)

Require Import Utils.
Require Gen_NN.
Require Import DefinedFunctions.
Require Import FloatishDef.
Require Import BinInt.
Require Import String.
Require Import Streams.
Local Open Scope list.

Existing Instance floatish_IEEE.

Example test :=
  mk_env_entry (Name "f", DTfloat) (FfromZ 1)%Z ::
               mk_env_entry (Name "v", DTVector 3) (ConstVector 3 ((FfromZ (-2)))%Z) :: 
               mk_env_entry (Name "m", DTMatrix 2 3) (ConstMatrix 2 3 (FfromZ 3))%Z :: nil.
Module API.
  Example opt := @Gen_NN.opt floatish_IEEE.
  Example opt2 := @Gen_NN.opt2 floatish_IEEE.
  Example test_update := @Gen_NN.test_update floatish_IEEE.
  Example testopt := @Gen_NN.testopt floatish_IEEE.
  Example testreeopt := @Gen_NN.testreeopt floatish_IEEE.  
  Example gradenv := @Gen_NN.gradenv floatish_IEEE.
  Example gradenv_tree := @Gen_NN.gradenv_tree floatish_IEEE.
  Example test_env := test.

  Example discard_first {A} (l:list (list A)) : list (list A) := List.map (@List.tl A) l.
  Definition normalizeIntData := Gen_NN.normalizeIntData.
  Definition init_env2 := Gen_NN.init_env2.
  CoFixpoint mkIndexedStream {A} (i : nat) (ran : nat -> A) : Stream A :=
    Cons (ran i) (mkIndexedStream (S i) ran).
  Definition streamtake := Gen_NN.streamtake.
  Definition df_env := DefinedFunctions.df_env.
  Definition eval_wisconsin_batch (nsamp:nat) 
             (env:df_env) (data : Matrix float nsamp 10) : list float  := 
    match Gen_NN.eval_wisconsin_batch nsamp env data with
    | Some val => val :: nil
    | _ => nil                      
    end.

  Definition wisconsin_test := Gen_NN.wisconsin_test.
  Definition wisconsin_test_env := Gen_NN.wisconsin_test_env.  
  Definition wisconsin_gradenv_tree := Gen_NN.wisconsin_gradenv_tree.
  Definition wisconsin_gradenv := Gen_NN.wisconsin_gradenv.
  Definition nn_test := Gen_NN.NN_test.
  Definition nn_test_val := Gen_NN.NN_test_val.  
  Definition nn_test_env := Gen_NN.NN_test_env.  
  Definition nn_test_gradenv_tree := Gen_NN.NN_test_gradenv_tree.
  Definition nn_test_gradenv := Gen_NN.NN_test_gradenv.
  
  End API.

Extraction "extracted/NnoptExtracted" API.

