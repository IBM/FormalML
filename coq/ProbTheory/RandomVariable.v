Require Export Program.Basics.
Require Import List Morphisms Lia.

Require Export LibUtils BasicUtils ProbSpace SigmaAlgebras.
Require Classical.
Require Import ClassicalDescription.


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
    rv_preimage_sa: forall (B: event cod), sa_sigma (event_preimage rv_X B).

Definition rv_preimage
           {Ts:Type}
           {Td:Type}
           {dom: SigmaAlgebra Ts}
           {cod: SigmaAlgebra Td}
           (rv_X: Ts -> Td)
           {rv:RandomVariable dom cod rv_X} :
  event cod -> event dom
  := fun b => exist _ _ (rv_preimage_sa b).

Global Instance RandomVariable_proper {Ts:Type} {Td:Type}
  : Proper (sa_equiv ==> sa_equiv ==> rv_eq ==> iff) (@RandomVariable Ts Td).
Proof.
  unfold RandomVariable.
  split; intros.
  - rewrite <- H1.
    apply H.
    destruct B.
    destruct (H0 x2) as [_ HH].
    apply (H2 (exist _ x2 (HH s))).
  - rewrite H1.
    apply H.
    destruct B.
    destruct (H0 x2) as [HH _].
    apply (H2 (exist _ x2 (HH s))).
Qed.

Instance RandomVariable_proper_le {Ts Td : Type} :
  Proper (sa_sub ==> sa_sub --> rv_eq ==> impl) (@RandomVariable Ts Td).
Proof.
  unfold RandomVariable.
  intros ???????????.
  rewrite <- H1.
  apply H.
  destruct B.
  apply (H2 (exist _ x2 (H0 _ s))).
Qed.

Global Instance rv_preimage_proper
       {Ts:Type}
       {Td:Type}
       {dom: SigmaAlgebra Ts}
       {cod: SigmaAlgebra Td}
       (rv_X: Ts -> Td)
       {rv:RandomVariable dom cod rv_X} :
  Proper (event_equiv ==> event_equiv) (@rv_preimage Ts Td dom cod rv_X rv).
Proof.
  intros x y eqq.
  now apply event_preimage_proper.
Qed.  


Class HasPreimageSingleton {Td} (σ:SigmaAlgebra Td)
  := sa_preimage_singleton :
       forall {Ts} {σs:SigmaAlgebra Ts} (rv_X:Ts->Td) {rv : RandomVariable σs σ rv_X} c,
         sa_sigma (pre_event_preimage rv_X (pre_event_singleton c)).

Definition preimage_singleton {Ts Td} {σs:SigmaAlgebra Ts} {σd:SigmaAlgebra Td} {has_pre:HasPreimageSingleton σd}
           (rv_X:Ts->Td) 
           {rv : RandomVariable σs σd rv_X}
           (c:Td) : event σs
  := exist _ _ (sa_preimage_singleton rv_X c).

Section Const.
  Context {Ts Td:Type}.

  Class ConstantRangeFunction
        (rv_X:Ts -> Td)
    := { 
    frf_val : Td;
    frf_val_complete : forall x, rv_X x = frf_val
      }.
  
  Global Program Instance crvconst c : ConstantRangeFunction (const c)
    := { frf_val := c }.

  Global Instance discrete_sa_rv
         {cod:SigmaAlgebra Td} (rv_X: Ts -> Td) 
    : RandomVariable (discrete_sa Ts) cod rv_X.
  Proof.
    exact (fun _ => I).
  Qed.

  Context (dom: SigmaAlgebra Ts)
          (cod: SigmaAlgebra Td).
  
  Global Instance rvconst c : RandomVariable dom cod (const c).
    Proof.
      red; intros.
      destruct (sa_dec B c).
      - assert (pre_event_equiv (fun _ : Ts => B c)
                            (fun _ : Ts => True))
          by (red; intuition).
        rewrite H0.
        apply sa_all.
      - assert (pre_event_equiv (fun _ : Ts => B c)
                            event_none)
        by (red; intuition).
        rewrite H0.
        apply sa_none.
    Qed.

End Const.

Section Simple.
  Context {Ts:Type} {Td:Type}.

  Class FiniteRangeFunction
        (rv_X:Ts->Td)
    := { 
    frf_vals : list Td ;
    frf_vals_complete : forall x, In (rv_X x) frf_vals;
      }.

  Lemma FiniteRangeFunction_ext (x y:Ts->Td) :
    rv_eq x y ->
    FiniteRangeFunction x ->
    FiniteRangeFunction y.
  Proof.
    repeat red; intros.
    invcs X.
    exists frf_vals0.
    intros.
    now rewrite <- H.
    Defined.

  Global Program Instance frf_crv (rv_X:Ts->Td) {crv:ConstantRangeFunction rv_X} :
    FiniteRangeFunction rv_X
    := {
    frf_vals := [frf_val]
      }.
  Next Obligation.
    left.
    rewrite (@frf_val_complete _ _ _ crv).
    reflexivity.
  Qed.

  Global Program Instance frf_fun (rv_X : Ts -> Td) (f : Td -> Td)
          (frf:FiniteRangeFunction rv_X) : 
    FiniteRangeFunction (fun v => f (rv_X v)) :=
    {frf_vals := map f frf_vals}.
  Next Obligation.
    destruct frf.
    now apply in_map.
  Qed.

  Definition frfconst c : FiniteRangeFunction (const c)
    := frf_crv (const c).

  Program Instance nodup_simple_random_variable (dec:forall (x y:Td), {x = y} + {x <> y})
          {rv_X:Ts->Td}
          (frf:FiniteRangeFunction rv_X) : FiniteRangeFunction rv_X
    := { frf_vals := nodup dec frf_vals }.
  Next Obligation.
    apply nodup_In.
    apply frf_vals_complete.
  Qed.

  Lemma nodup_simple_random_variable_NoDup
        (dec:forall (x y:Td), {x = y} + {x <> y})
        {rv_X}
        (frf:FiniteRangeFunction rv_X) :
    NoDup (frf_vals (FiniteRangeFunction:=nodup_simple_random_variable dec frf)).
  Proof.
    simpl.
    apply NoDup_nodup.
  Qed.


Lemma frf_singleton_rv (rv_X : Ts -> Td)
        (frf:FiniteRangeFunction rv_X) 
        (dom: SigmaAlgebra Ts)
        (cod: SigmaAlgebra Td) :
    (forall (c : Td), In c frf_vals -> sa_sigma (pre_event_preimage rv_X (pre_event_singleton c))) ->
    RandomVariable dom cod rv_X.
Proof.
  intros Fs.
  intros x.
  unfold event_preimage, pre_event_preimage in *.
  unfold pre_event_singleton in *.

  destruct frf.
  assert (exists ld, incl ld frf_vals0 /\
                (forall d: Td, In d ld -> x d) /\
                (forall d: Td, In d frf_vals0 -> x d -> In d ld)).
  {
    clear frf_vals_complete0 Fs.
    induction frf_vals0.
    - exists nil.
      split.
      + intros ?; trivial.
      + split.
        * simpl; tauto.
        * intros ??.
          auto.
    - destruct IHfrf_vals0 as [ld [ldincl [In1 In2]]].
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
  apply sa_proper with (x0:=pre_list_union (map (fun d omega => rv_X omega = d) ld)).
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
  - apply sa_pre_list_union; intros.
    apply in_map_iff in H.
    destruct H as [? [??]]; subst.
    apply Fs.
    now apply ld_incl.
Qed.

Instance rv_fun_simple {dom: SigmaAlgebra Ts}
         {cod: SigmaAlgebra Td}
         (x : Ts -> Td) (f : Td -> Td)
         {rvx : RandomVariable dom cod x}
         {frfx : FiniteRangeFunction x} :
      (forall (c : Td), In c frf_vals -> sa_sigma (pre_event_preimage x (pre_event_singleton c))) ->
     RandomVariable dom cod (fun u => f (x u)).    
Proof.
  intros Hsingleton.
    generalize (frf_fun x f frfx); intros.
    apply frf_singleton_rv with (frf:=X); trivial.
    destruct X.
    destruct frfx.
    intros c cinn.
    simpl in cinn.
    unfold pre_event_preimage, pre_event_singleton.
    assert (pre_event_equiv (fun omega : Ts => f (x omega) = c)
                        (pre_list_union
                           (map (fun sval =>
                                   (fun omega =>
                                      (x omega = sval) /\ (f sval = c)))
                                frf_vals1))).
    { 
      intro v.
      unfold pre_list_union.
      split; intros.
      - specialize (frf_vals_complete0 v).
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
    apply sa_pre_list_union.
    intros.
    rewrite in_map_iff in H0.
    destruct H0.
    destruct H0.
    rewrite <- H0.
    assert (pre_event_equiv (fun omega : Ts => x omega = x1 /\ f x1 = c)
                        (pre_event_inter (fun omega => x omega = x1)
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

Require Import Finite ListAdd SigmaAlgebras EquivDec Eqdep_dec.

Section Finite.
  Context {Ts:Type}{Td:Type}.

  Program Instance Finite_FiniteRangeFunction {fin:Finite Ts}  (rv_X:Ts->Td)
    : FiniteRangeFunction rv_X
    := {| 
    frf_vals := map rv_X elms
      |}.
  Next Obligation.
    generalize (finite x); intros.
    apply in_map_iff; eauto.
  Qed.

  Lemma Finite_finitsubset1 {A:Type} {decA:EqDec A eq} (x:A) (l:list A) :
    { pfs : list (In x l) | forall pf, In pf pfs} .
  Proof.
    induction l; simpl.
    - exists nil.
      tauto.
    - destruct IHl as [ll pfs].
      
      destruct (a == x).
      + exists ((or_introl e) :: (map (@or_intror _ _) ll)).
        intros [?|?].
        * left.
          f_equal.
          apply eq_proofs_unicity; intros.
          destruct (decA x0 y); tauto.
        * right.
          apply in_map.
          apply pfs.
      +  exists (map (@or_intror _ _) ll).
         intros [?|?].
         * congruence.
         * apply in_map.
           apply pfs.
  Defined.

  Definition Finite_finitsubset2 {A:Type} {decA:EqDec A eq} (x:A) (l:list A) :
    list {x : A | In x l}.
  Proof.
    destruct (Finite_finitsubset1 x l).
    exact (map (fun y => exist _ x y) x0).
  Defined.
  
  Program Instance Finite_finitesubset_dec {A:Type} {decA:EqDec A eq} (l:list A)
    : Finite {x : A | In x l}.
  Next Obligation.
    exact (flat_map (fun x => Finite_finitsubset2 x l) l).
  Defined.
  Next Obligation.
    unfold Finite_finitesubset_dec_obligation_1.
    apply in_flat_map.
    exists x.
    split; trivial.
    unfold Finite_finitsubset2.
    destruct (Finite_finitsubset1 x l).
    apply in_map.
    apply i.
  Qed.

  Definition finitesubset_sa {A} (l:list A) : SigmaAlgebra {x : A | In x l}
    := discrete_sa {x : A | In x l}.
  
End Finite.

Section Event_restricted.
  Context {Ts:Type} {Td:Type} {σ:SigmaAlgebra Ts} {cod : SigmaAlgebra Td}.

  Global Program Instance Restricted_FiniteRangeFunction (e:event σ) (f : Ts -> Td)
    (frf: FiniteRangeFunction f) :
    FiniteRangeFunction (event_restricted_function e f) :=
    { frf_vals := frf_vals }.
  Next Obligation.
    destruct frf.
    apply frf_vals_complete0.
  Qed.

  Global Program Instance Restricted_RandomVariable (e:event σ) (f : Ts -> Td)
          (rv : RandomVariable σ cod f) :
    RandomVariable (event_restricted_sigma e) cod (event_restricted_function e f).
  Next Obligation.
    red in rv.
    unfold event_preimage in *.
    unfold event_restricted_function.
    assert (HH:sa_sigma
                (fun a : Ts =>
                   e a /\ proj1_sig B (f a))).
    - apply sa_inter.
      + destruct e; auto.
      + apply rv.
    - eapply sa_proper; try eapply HH.
      intros x.
      split.
      + intros [?[??]]; subst.
        destruct x0; simpl in *.
        tauto.
      + intros [HH2 ?].
        exists (exist _ _ HH2).
        simpl.
        tauto.
  Qed.


  Definition lift_event_restricted_domain_fun (default:Td) {P:event σ} (f:event_restricted_domain P -> Td) : Ts -> Td
    := fun x =>
         match excluded_middle_informative (P x) with
         | left pf => f (exist _ _ pf)
         | right _ => default
         end.

  Global Instance lift_event_restricted_domain_fun_rv (default:Td) {P:event σ} (f:event_restricted_domain P -> Td) :
    RandomVariable (event_restricted_sigma P) cod f ->
    RandomVariable σ cod (lift_event_restricted_domain_fun default f).
  Proof.
    intros rv.
    unfold lift_event_restricted_domain_fun.
    unfold RandomVariable in *.
    intros.
    destruct (excluded_middle_informative (B default)).
    - eapply sa_proper with
          (y:=
             (event_union (event_complement P) 
                          (event_restricted_event_lift P (exist _ (event_preimage f B) (rv B))))).
      + intros x.
        unfold event_preimage, event_complement, event_restricted_event_lift, event_union, pre_event_union; simpl.
        split; intros HH.
        * match_destr_in HH; simpl in HH.
          -- right.
             unfold event_restricted_domain.
             eexists; split; [ | eapply HH].
             reflexivity.
          -- left; trivial.
        * destruct HH.
          -- match_destr.
             unfold pre_event_complement in H.
             tauto.
          -- destruct H as [? [? ?]].
             match_destr.
             subst.
             destruct x0.
             replace e1 with e0 in H0.
             apply H0.
             apply proof_irrelevance.
      + apply sa_union.
        * apply sa_complement.
          now destruct P; simpl.
        * unfold proj1_sig; match_destr.
    - eapply sa_proper with
          (y := event_restricted_event_lift P (exist _ (event_preimage f B) (rv B))).
      + intros x.
        unfold event_preimage, event_restricted_event_lift, event_union, pre_event_union; simpl.        
        split; intros HH.
        * match_destr_in HH; simpl in HH.
          -- exists (exist P x e).
             tauto.
          -- tauto.
        * destruct HH as [? [? ?]].
          match_destr.
          -- destruct x0.
             subst.
             replace e with e0.
             apply H0.
             apply proof_irrelevance.
          -- destruct x0.
             subst.
             tauto.
      + unfold event_restricted_event_lift; simpl.
        generalize (sa_pre_event_restricted_event_lift P (exist _ (event_preimage f B) (rv B))); intros.
        apply H.
    Qed.

  Global Instance lift_event_restricted_domain_fun_frf (default:Td) {P:event σ} (f:event_restricted_domain P -> Td) :
    FiniteRangeFunction f -> 
    FiniteRangeFunction (lift_event_restricted_domain_fun default f).
  Proof.
    intros frf.
    exists (default::frf_vals).
    intros.
    unfold lift_event_restricted_domain_fun.
    match_destr.
    - right.
      apply frf_vals_complete.
    - now left.
  Qed.

 End Event_restricted.

Section pullback.

  Instance pullback_rv {Ts:Type} {Td:Type}
      (cod: SigmaAlgebra Td)
      (f: Ts -> Td) : RandomVariable (pullback_sa cod f) cod f.
  Proof.
    red; intros.
    apply pullback_sa_pullback.
    now destruct B.
  Qed.

  Lemma pullback_rv_sub
        {Ts:Type} {Td:Type}
        (dom : SigmaAlgebra Ts)
        (cod: SigmaAlgebra Td)
        (f: Ts -> Td) :
    RandomVariable dom cod f ->
    sa_sub (pullback_sa cod f) dom.
  Proof.
    intros frv x [y[say yeqq]]; simpl in *.
    apply (sa_proper _ (fun a => y (f a))).
    - intros ?.
      now rewrite yeqq.
    - specialize (frv (exist _ _ say)).
      apply frv.
  Qed.

End pullback.

Section sa_sub.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

  Instance RandomVariable_sa_sub {Td} {cod : SigmaAlgebra Td}
           x
           {rv_x:RandomVariable dom2 cod x}
  : RandomVariable dom cod x.
  Proof.
    intros e.
    specialize (rv_x e).
    now apply sub.
  Qed.

End sa_sub.


Section filtration.
    Context {Ts:Type}.

    Global Instance filtrate_sa_rv {Td} {doms: nat -> SigmaAlgebra Ts} {cod: SigmaAlgebra Td} (rv:Ts->Td) n :
      RandomVariable (doms n) cod rv ->
      RandomVariable (filtrate_sa doms (S n)) cod rv.
    Proof.
      eapply RandomVariable_proper_le; try reflexivity.
      apply filtrate_sa_sub.
    Qed.
    
End filtration.

Section filtration_history.
  Context {Ts:Type} {Td:Type} {cod: SigmaAlgebra Td}.

  Context (X : nat -> Ts -> Td).
  
  Definition filtration_history_sa : nat -> SigmaAlgebra Ts :=
    filtrate_sa (fun n => pullback_sa cod (X n)).

  Global Instance filtration_history_sa_is_filtration : IsFiltration (filtration_history_sa).
  Proof.
    typeclasses eauto.
  Qed.
  
  Global Instance filtration_history_sa_rv n :
    RandomVariable (filtration_history_sa (S n)) cod (X n).
  Proof.
    apply filtrate_sa_rv.
    apply pullback_rv.
  Qed.

  Instance filtration_history_sa_lt_rv
        (n : nat) (j:nat) (jlt: (j < n)%nat) :
    RandomVariable (filtration_history_sa n) cod (X j).
  Proof.
    eapply (RandomVariable_proper_le (filtration_history_sa (S j)))
    ; try reflexivity.
    - unfold filtration_history_sa.
      apply is_filtration_le.
      + try typeclasses eauto.
      + lia.
    - apply filtration_history_sa_rv.
  Qed.

  Lemma filtration_history_sa_sub_lt {dom:SigmaAlgebra Ts} n
        (rv:forall k, k < n -> RandomVariable dom cod (X k)) :
    sa_sub (filtration_history_sa n) dom.
  Proof.
    intros.
    unfold filtration_history_sa.
    apply filtrate_sa_sub_all; intros.
    apply pullback_rv_sub; eauto.
  Qed.    

  Lemma filtration_history_sa_sub {dom:SigmaAlgebra Ts}
    {rv:forall n, RandomVariable dom cod (X n)} :
    forall n, sa_sub (filtration_history_sa n) dom.
  Proof.
    intros.
    apply filtration_history_sa_sub_lt; auto.
  Qed.

  Definition filtration_history_limit_sa : SigmaAlgebra Ts
    := countable_union_sa (fun k => pullback_sa _ (X k)).

  Lemma filtration_history_limit_sa_le_sub n : 
    sa_sub (filtration_history_sa n) filtration_history_limit_sa.
  Proof.
    apply filtrate_sa_countable_union_sub.
  Qed.

  Global Instance filtration_history_limit_sa_rv n :
    RandomVariable (filtration_history_limit_sa) cod (X n).
  Proof.
    simpl.
    intros ?.
    eapply countable_union_sa_sub.
    apply pullback_rv.
  Qed.
  
  Lemma filtration_history_limit_sa_sub (dom:SigmaAlgebra Ts)
    {rv:forall n, RandomVariable dom cod (X n)} :
    sa_sub filtration_history_limit_sa dom.
  Proof.
    intros.
    apply countable_union_sa_sub_all; intros.
    now apply pullback_rv_sub.
  Qed.

End filtration_history.
  
