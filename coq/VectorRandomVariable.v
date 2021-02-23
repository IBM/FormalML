Require Import Reals.

Require Import Lra Lia.
Require Import List Permutation.
Require Import Morphisms EquivDec Program.
Require Import Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq.
Require Import Classical_Prop.
Require Import Classical.

Require Import Utils.
Require Import DVector.
Require Import NumberIso.
Require Import SigmaAlgebras.
Require Export FunctionsToReal ProbSpace BorelSigmaAlgebra.
Require Export RandomVariable.
Require Export Isomorphism.
Require Import FunctionalExtensionality.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Section VectorRandomVariables.
  
  Context {Ts:Type} {Td:Type}.


  Definition fun_to_vector_to_vector_of_funs
             {n:nat}
             (f: Ts -> vector Td n)
    : vector (Ts->Td) n
    := vector_create 0 n (fun m _ pf => fun x => vector_nth m pf (f x)).

  Definition vector_of_funs_to_fun_to_vector
             {n:nat}
             (fs:vector (Ts->Td) n)
    : Ts -> vector Td n
    := fun x => vector_create 0 n (fun m _ pf => vector_nth m pf fs x).
  
  Program Global Instance vector_iso n : Isomorphism (Ts -> vector Td n) (vector (Ts->Td) n)
    := {
    iso_f := fun_to_vector_to_vector_of_funs
    ; iso_b := vector_of_funs_to_fun_to_vector
      }.
  Next Obligation.
    unfold fun_to_vector_to_vector_of_funs, vector_of_funs_to_fun_to_vector.
    apply vector_nth_eq; intros.
    rewrite vector_nth_create'; simpl.
    apply functional_extensionality; intros.
    now rewrite vector_nth_create'.
  Qed.
  Next Obligation.
    unfold fun_to_vector_to_vector_of_funs, vector_of_funs_to_fun_to_vector.
    apply functional_extensionality; intros.
    erewrite vector_create_ext.
    2: {
      intros.
      rewrite vector_nth_create'.
      reflexivity.
    }
    now rewrite (vector_create_nth).
  Qed.

End VectorRandomVariables.

Require Import Expectation.

Lemma listo_to_olist_length {A:Type} (l:list (option A)) (r:list A)
  : listo_to_olist l = Some r ->
    length l = length r.
Proof.
  revert r.
  induction l; simpl; intros.
  - now invcs H; simpl.
  - destruct a; try discriminate.
    match_option_in H; try discriminate.
    invcs H.
    simpl.
    now rewrite (IHl _ eqq).
Qed.

Program Definition vectoro_to_ovector {A} {n} (v:vector (option A) n) : option (vector A n)
  := match listo_to_olist v with
     | None => None
     | Some x => Some x
     end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply listo_to_olist_length in Heq_anonymous.
  now rewrite vector_length in Heq_anonymous.
Qed.

Section vector_ops.
Context 
  {Ts:Type}
  {dom: SigmaAlgebra Ts}
  {prts: ProbSpace dom}.

Definition vector_Expectation {n} (rv_X : Ts -> vector R n) : option (vector Rbar n)
  := vectoro_to_ovector (vector_map Expectation (iso_f rv_X)).
Print SimpleRandomVariable.


Definition vector_SimpleExpectation {n} (rv_X : Ts -> vector R n)
           (simp : forall (x:Ts->R), In x  (` (iso_f rv_X)) -> SimpleRandomVariable x)
 : vector R n
  := vector_map_onto (iso_f rv_X) (fun x pf => SimpleExpectation x (srv:=simp x pf)).

End vector_ops.
