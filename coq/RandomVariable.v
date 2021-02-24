Require Export Program.Basics.
Require Import List Morphisms.

Require Export LibUtils BasicUtils ProbSpace.

Import ListNotations.

(* A random variable is a mapping from a pobability space to a sigma algebra. *)
Class RandomVariable {Ts:Type} {Td:Type}
      (dom: SigmaAlgebra Ts)
      (cod: SigmaAlgebra Td)
      (rv_X: Ts -> Td)
  :=
    (* for every element B in the sigma algebra, 
       the preimage of rv_X on B is an event in the probability space *)
    rv_preimage: forall (B: event Td), sa_sigma B -> sa_sigma (event_preimage rv_X B).

Global Instance RandomVariable_proper {Ts:Type} {Td:Type}
       (dom: SigmaAlgebra Ts)
       (cod: SigmaAlgebra Td) : Proper (rv_eq ==> iff) (RandomVariable dom cod).
Proof.
  intros x y eqq.
  unfold RandomVariable.
  split; intros.
  - rewrite <- eqq; auto.
  - rewrite eqq; auto.
Qed.

Section Const.
  Context {Ts Td:Type}.

  Class ConstantRandomVariable
        (rv_X:Ts -> Td)
    := { 
    srv_val : Td;
    srv_val_complete : forall x, rv_X x = srv_val
      }.
  
  Global Program Instance crvconst c : ConstantRandomVariable (const c)
    := { srv_val := c }.


  Context (dom: SigmaAlgebra Ts)
          (cod: SigmaAlgebra Td).

  Global Instance rvconst c : RandomVariable dom cod (const c).
    Proof.
      red; intros.
      destruct (sa_dec H c).
      - assert (event_equiv (fun _ : Ts => B c)
                            (fun _ : Ts => True)).
        red; intros.
        intuition.
        rewrite H1.
        apply sa_all.
      - assert (event_equiv (fun _ : Ts => B c)
                            event_none).
        red; intros.
        intuition.
        rewrite H1.
        apply sa_none.
    Qed.

End Const.

Section Simple.
  Context {Ts:Type} {Td:Type}.

  Class SimpleRandomVariable
        (rv_X:Ts->Td)
    := { 
    srv_vals : list Td ;
    srv_vals_complete : forall x, In (rv_X x) srv_vals;
      }.

  Lemma SimpleRandomVariable_ext (x y:Ts->Td) :
    rv_eq x y ->
    SimpleRandomVariable x ->
    SimpleRandomVariable y.
  Proof.
    repeat red; intros.
    invcs X.
    exists srv_vals0.
    intros.
    now rewrite <- H.
  Qed.

  Global Program Instance srv_crv (rv_X:Ts->Td) {crv:ConstantRandomVariable rv_X} :
    SimpleRandomVariable rv_X
    := {
    srv_vals := [srv_val]
      }.
  Next Obligation.
    left.
    rewrite (@srv_val_complete _ _ _ crv).
    reflexivity.
  Qed.

  Definition srvconst c : SimpleRandomVariable (const c)
    := srv_crv (const c).

  Program Instance nodup_simple_random_variable (dec:forall (x y:Td), {x = y} + {x <> y})
          {rv_X:Ts->Td}
          (srv:SimpleRandomVariable rv_X) : SimpleRandomVariable rv_X
    := { srv_vals := nodup dec srv_vals }.
  Next Obligation.
    apply nodup_In.
    apply srv_vals_complete.
  Qed.

  Lemma nodup_simple_random_variable_NoDup
        (dec:forall (x y:Td), {x = y} + {x <> y})
        {rv_X}
        (srv:SimpleRandomVariable rv_X) :
    NoDup (srv_vals (SimpleRandomVariable:=nodup_simple_random_variable dec srv)).
  Proof.
    simpl.
    apply NoDup_nodup.
  Qed.
  
End Simple.
