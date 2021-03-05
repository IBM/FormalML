Require Export Program.Basics.
Require Import List Morphisms.

Require Export LibUtils BasicUtils ProbSpace.
Require Classical.

Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

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

  Global Program Instance srv_fun (rv_X : Ts -> Td) (f : Td -> Td)
          (srv:SimpleRandomVariable rv_X) : 
    SimpleRandomVariable (fun v => f (rv_X v)) :=
    {srv_vals := map f srv_vals}.
  Next Obligation.
    destruct srv.
    now apply in_map.
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


Lemma srv_singleton_rv (rv_X : Ts -> Td)
        (srv:SimpleRandomVariable rv_X) 
        (dom: SigmaAlgebra Ts)
        (cod: SigmaAlgebra Td) :
    (forall (c : Td), In c srv_vals -> sa_sigma (event_preimage rv_X (event_singleton c))) ->
    RandomVariable dom cod rv_X.
Proof.
  intros Fs.
  intros x sa_x.
  unfold event_preimage in *.
  unfold event_singleton in *.

  destruct srv.
  assert (exists ld, incl ld srv_vals0 /\
                (forall d: Td, In d ld -> x d) /\
                (forall d: Td, In d srv_vals0 -> x d -> In d ld)).
  {
    clear srv_vals_complete0 Fs.
    induction srv_vals0.
    - exists nil.
      split.
      + intros ?; trivial.
      + split.
        * simpl; tauto.
        * intros ??.
          auto.
    - destruct IHsrv_vals0 as [ld [ldincl [In1 In2]]].
      destruct (Classical_Prop.classic (x a)).
      + exists (a::ld).
        split; [| split].
        * red; simpl; intros ? [?|?]; eauto.
        * simpl; intros ? [?|?].
          -- congruence.
          -- eauto.
        * intros ? [?|?]; simpl; eauto.
      + exists ld.
        split; [| split].
        * red; simpl; eauto.
        * eauto.
        * simpl; intros ? [?|?] ?.
          -- congruence.
          -- eauto.
  } 
  destruct H as [ld [ld_incl ld_iff]].
  apply sa_proper with (x0:=list_union (map (fun d omega => rv_X omega = d) ld)).
  - intros e.
    split; intros HH.
    + destruct HH as [? [??]].
      apply in_map_iff in H.
      destruct H as [? [??]]; subst.
      now apply ld_iff.
    + red; simpl.
      apply ld_iff in HH.
      eexists; split.
      * apply in_map_iff; simpl.
        eexists; split; [reflexivity |]; eauto.
      * reflexivity.
      * eauto.
  - apply sa_list_union; intros.
    apply in_map_iff in H.
    destruct H as [? [??]]; subst.
    apply Fs.
    now apply ld_incl.
Qed.

Instance rv_fun_simple {dom: SigmaAlgebra Ts}
         {cod: SigmaAlgebra Td}
         (x : Ts -> Td) (f : Td -> Td)
         {rvx : RandomVariable dom cod x}
         {srvx : SimpleRandomVariable x} :
      (forall (c : Td), In c srv_vals -> sa_sigma (event_preimage x (event_singleton c))) ->
     RandomVariable dom cod (fun u => f (x u)).    
Proof.
  intros Hsingleton.
    generalize (srv_fun x f srvx); intros.
    apply srv_singleton_rv with (srv:=X); trivial.
    destruct X.
    destruct srvx.
    intros c cinn.
    simpl in cinn.
    unfold event_preimage, event_singleton.
    assert (event_equiv (fun omega : Ts => f (x omega) = c)
                        (list_union
                           (map (fun sval =>
                                   (fun omega =>
                                      (x omega = sval) /\ (f sval = c)))
                                srv_vals1))).
    { 
      intro v.
      unfold list_union.
      split; intros.
      - specialize (srv_vals_complete0 v).
        eexists.
        rewrite in_map_iff.
        split.
        + exists (x v).
          split.
          * reflexivity.
          * easy.
        + simpl.
          easy.
      - destruct H.
        rewrite in_map_iff in H.
        destruct H as [[c0 [? ?]] ?].
        rewrite <- H in H1.
        destruct H1.
        now rewrite <- H1 in H2.
    }
    rewrite H.
    apply sa_list_union.
    intros.
    rewrite in_map_iff in H0.
    destruct H0.
    destruct H0.
    rewrite <- H0.
    assert (event_equiv (fun omega : Ts => x omega = x1 /\ f x1 = c)
                        (event_inter (fun omega => x omega = x1)
                                     (fun _ => f x1 = c))).
    {
      intro u.
      now unfold event_inter.
    }
    rewrite H2.
    apply sa_inter.
    - now apply Hsingleton.
    - apply sa_sigma_const.
      apply Classical_Prop.classic.
  Qed.

End Simple.
