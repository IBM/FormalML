Require Export Program.Basics Program.
Require Import List Morphisms Lia.

Require Export LibUtils BasicUtils ProbSpace SigmaAlgebras Independence.
Require Classical.
Require Import ClassicalDescription EquivDec.
Require Import ClassicalChoice ChoiceFacts.
Require Import FiniteType.
Require Import Isomorphism.


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
  rv_preimage_sa: forall (B: event cod), sa_sigma _ (event_preimage rv_X B).

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
      sa_sigma _ (pre_event_preimage rv_X (pre_event_singleton c)).

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

  Global Instance rvconst' c : RandomVariable dom cod (fun _ => c).
  Proof.
    apply rvconst.
  Qed.

  Lemma rv_preimage_const c A :
    event_equiv (rv_preimage (const c) A) Ω
    \/ event_equiv (rv_preimage (const c) A) event_none.
  Proof.
    destruct (sa_pre_dec A c)
    ; [left | right]
    ; split; intros ?; repeat red; tauto.
  Qed.

End Const.

Instance id_rv {Ts} {dom:SigmaAlgebra Ts} : RandomVariable dom dom (fun x => x).
Proof.
  intros ?.
  unfold event_preimage.
  destruct B; simpl.
  apply s.
Qed.

Instance compose_rv {Ts1 Ts2 Ts3} {dom1 dom2 dom3}
         (f : Ts1 -> Ts2)
         (g : Ts2 -> Ts3)
         {rvf : RandomVariable dom1 dom2 f}
         {rvg : RandomVariable dom2 dom3 g} :
  RandomVariable dom1 dom3 (compose g f).
Proof.
  intros ?.
  apply (rvf (exist _ _ (rvg B))).
Qed.  


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
    (forall (c : Td), In c frf_vals -> sa_sigma _ (pre_event_preimage rv_X (pre_event_singleton c))) ->
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
    apply (sa_proper _ (pre_list_union (map (fun d omega => rv_X omega = d) ld))).
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
    (forall (c : Td), In c frf_vals -> sa_sigma _ (pre_event_preimage x (pre_event_singleton c))) ->
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

 Global Program Instance frf_fun2 {Ts Td1 Td2} (rv_X : Ts -> Td1) (f : Td1 -> Td2)
         (frf:FiniteRangeFunction rv_X) : 
    FiniteRangeFunction (fun v => f (rv_X v)) :=
    {frf_vals := map f frf_vals}.
  Next Obligation.
    destruct frf.
    now apply in_map.
  Qed.

  Global Program Instance FiniteRangeFunction_compose_before {A B C} (f : B -> C) (g : A -> B)
    {frf : FiniteRangeFunction f} :
    FiniteRangeFunction (f ∘ g)
    := {| frf_vals := frf_vals |}.
  Next Obligation.
    unfold compose.
    apply frf_vals_complete.
  Qed.

  Global Program Instance FiniteRangeFunction_compose_after {A B C} (f : A -> B) (g : B -> C)
    {frf : FiniteRangeFunction f} :
    FiniteRangeFunction (g ∘ f) 
    := {| frf_vals := map g frf_vals |}.
  Next Obligation.
    unfold compose.
    apply in_map.
    apply frf_vals_complete.
  Qed.

Require Import ListAdd SigmaAlgebras EquivDec Eqdep_dec.

Section Finite.
  Context {Ts:Type}{Td:Type}.

  Program Instance Finite_FiniteRangeFunction {fin:FiniteType Ts}  (rv_X:Ts->Td)
    : FiniteRangeFunction rv_X
    := {| 
      frf_vals := map rv_X fin_elms
    |}.
  Next Obligation.
    generalize (fin_finite x); intros.
    apply in_map_iff; eauto.
  Qed.

  Program Instance FiniteRange_FiniteRangeFunction {fin:FiniteType Td}  (rv_X:Ts->Td)
    : FiniteRangeFunction rv_X
    := {| 
      frf_vals := fin_elms
    |}.
  Next Obligation.
    apply fin_finite.
  Qed.

  Lemma FiniteType_finitsubset1 {A:Type} {decA:EqDec A eq} (x:A) (l:list A) :
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

  Definition FiniteType_finitsubset2 {A:Type} {decA:EqDec A eq} (x:A) (l:list A) :
    list {x : A | In x l}.
  Proof.
    destruct (FiniteType_finitsubset1 x l).
    exact (map (fun y => exist _ x y) x0).
  Defined.
  
  Program Instance FiniteType_finitesubset_dec {A:Type} {decA:EqDec A eq} (l:list A)
    : FiniteType {x : A | In x l}.
  Next Obligation.
    exact (flat_map (fun x => FiniteType_finitsubset2 x l) l).
  Defined.
  Next Obligation.
    unfold FiniteType_finitesubset_dec_obligation_1.
    apply in_flat_map.
    exists x.
    split; trivial.
    unfold FiniteType_finitsubset2.
    destruct (FiniteType_finitsubset1 x l).
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
    assert (HH:sa_sigma _
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

  Instance pullback_compose_rv {Ts1 Ts2 Ts3} {dom2 dom3}
           (f : Ts1 -> Ts2)
           (g : Ts2 -> Ts3)
           {rvg : RandomVariable dom2 dom3 g} :
    RandomVariable (pullback_sa dom2 f) dom3 (compose g f).
  Proof.
    apply compose_rv; trivial.
    typeclasses eauto.
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

  Lemma pullback_sa_compose_sub
        {Ts:Type} {Td:Type}
        (cod: SigmaAlgebra Td)
        (f: Ts -> Td) (g:Td -> Td):
    sa_sub (pullback_sa cod g) cod ->
    sa_sub (pullback_sa cod (compose g f)) (pullback_sa cod f).
  Proof.
    intros.
    rewrite pullback_sa_compose_equiv.
    apply pullback_rv_sub.
    generalize (pullback_rv cod f).
    apply RandomVariable_proper_le; try reflexivity.
    now unfold flip.
  Qed.

  Lemma pullback_sa_compose_sub_rv
        {Ts:Type} {Td:Type}
        (cod: SigmaAlgebra Td)
        (f: Ts -> Td) (g:Td -> Td)
        {rvg : RandomVariable cod cod g} :
    sa_sub (pullback_sa cod (compose g f)) (pullback_sa cod f).
  Proof.
    intros.
    apply pullback_sa_compose_sub; trivial.
    now apply pullback_rv_sub.
  Qed.

  Lemma pullback_sa_compose_isos
        {Ts:Type} {Td:Type}        
        (rv1 : Ts -> Td) (f g : Td -> Td)
        (cod: SigmaAlgebra Td)
        (rvf : RandomVariable cod cod f)
        (rvg : RandomVariable cod cod g)
        (inv:forall (rv : Ts -> Td) , rv_eq (compose g (compose f rv)) rv) :
    sa_equiv (pullback_sa cod rv1) (pullback_sa cod (compose f rv1)).
  Proof.
    apply sa_equiv_subs.
    split.
    - rewrite <- (inv rv1) at 1.
      now apply pullback_sa_compose_sub_rv.
    - now apply pullback_sa_compose_sub_rv.
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
    RandomVariable (filtrate_sa doms n) cod rv.
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
    RandomVariable (filtration_history_sa n) cod (X n).
  Proof.
    apply filtrate_sa_rv.
    apply pullback_rv.
  Qed.

  Instance filtration_history_sa_le_rv
           (n : nat) (j:nat) (jlt: (j <= n)%nat) :
    RandomVariable (filtration_history_sa n) cod (X j).
  Proof.
    eapply (RandomVariable_proper_le (filtration_history_sa j))
    ; try reflexivity.
    - unfold filtration_history_sa.
      apply is_filtration_le; trivial.
      typeclasses eauto.
    - apply filtration_history_sa_rv.
  Qed.

  Lemma filtration_history_sa_sub_le {dom:SigmaAlgebra Ts} n
        (rv:forall k, k <= n -> RandomVariable dom cod (X k)) :
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
    apply filtration_history_sa_sub_le; auto.
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

  Global Instance filtration_history_is_sub_algebra
         (dom:SigmaAlgebra Ts)
         {rv:forall n, RandomVariable dom cod (X n)} :
    IsSubAlgebras dom (filtration_history_sa).
  Proof.
    apply filtrate_sa_is_sub_algebra.
    intros ?.
    now apply pullback_rv_sub.
  Qed.

End filtration_history.

Section filtration_history_props.

  Context {Ts:Type} {Td:Type} {cod: SigmaAlgebra Td}.

  Lemma filtration_history_sa_iso_l_sub
        (rv1 : nat -> Ts -> Td) (f g : nat -> Td -> Td)
        (inv:forall n x, g n (f n x) = x)
        (g_sigma:forall k s, sa_sigma _ s -> sa_sigma _ (fun x => s (g k x))) :
    forall n, sa_sub (filtration_history_sa rv1 n) ((filtration_history_sa (fun n x => f n (rv1 n x)) n)).
  Proof.
    unfold filtration_history_sa.
    intros.
    apply filtrate_sa_sub_proper; intros k.
    eapply pullback_sa_iso_l_sub; eauto.
  Qed.

  Lemma filtration_history_sa_f_sub
        (rv1 : nat -> Ts -> Td) (f : nat -> Td -> Td)
        (f_sigma:forall k s, sa_sigma _ s -> sa_sigma _ (fun x => s (f k x))) :
    forall n, sa_sub ((filtration_history_sa (fun n x => f n (rv1 n x)) n)) (filtration_history_sa rv1 n).
  Proof.
    unfold filtration_history_sa.
    intros.
    apply filtrate_sa_sub_proper; intros k.
    eapply pullback_sa_f_sub; eauto.
  Qed.

  Lemma filtration_history_sa_isos
        (rv1 : nat -> Ts -> Td) (f g : nat -> Td -> Td)
        (inv:forall n x, g n (f n x) = x)
        (f_sigma:forall k s, sa_sigma _ s -> sa_sigma _ (fun x => s (f k x)))
        (g_sigma:forall k s, sa_sigma _ s -> sa_sigma _ (fun x => s (g k x))) :
    forall n, sa_equiv (filtration_history_sa rv1 n) ((filtration_history_sa (fun n x => f n (rv1 n x)) n)).
  Proof.
    unfold filtration_history_sa; intros.
    apply filtrate_sa_proper; intros k.
    apply (pullback_sa_isos (rv1 k) (f k) (g k)); auto.
  Qed.
  

End filtration_history_props.

Section adapted.
  Context {Ts:Type} {Td:Type} (cod: SigmaAlgebra Td).

  Class IsAdapted (X : nat -> Ts -> Td) (sas : nat -> SigmaAlgebra Ts)
    := is_adapted : forall (n:nat), RandomVariable (sas n) cod (X n).

  Global Instance filtration_history_sa_is_adapted (X : nat -> Ts -> Td) :
    IsAdapted X (filtration_history_sa X).
  Proof.
    intros n.
    apply filtration_history_sa_rv.
  Qed.

  Global Instance is_adapted_proper : Proper (pointwise_relation _ rv_eq ==> pointwise_relation _ sa_sub ==> impl) IsAdapted.
  Proof.
    intros ????????.
    generalize (H1 n).
    apply RandomVariable_proper_le; trivial.
    reflexivity.
  Qed.

  Global Instance is_adapted_eq_proper : Proper (pointwise_relation _ rv_eq ==> pointwise_relation _ sa_equiv ==> iff) IsAdapted.
  Proof.
    intros ??????.
    split; apply is_adapted_proper; trivial.
    - intros ?; apply sa_equiv_sub; trivial.
    - now symmetry.
    - intros ?; apply sa_equiv_sub; now symmetry.
  Qed.

  Lemma filtration_history_sa_is_least
        (X : nat -> Ts -> Td) sas
        {filt:IsFiltration sas}
        {adapt:IsAdapted X sas}:
    forall n, sa_sub (filtration_history_sa X n) (sas n).
  Proof.
    unfold filtration_history_sa.
    intros.
    apply filtrate_sa_sub_all; intros.
    transitivity (sas k).
    - apply pullback_rv_sub.
      apply adapt.
    - now apply is_filtration_le.
  Qed.    

End adapted.

Section prod_space.

  Context {Ts Td1 Td2}
          {dom:SigmaAlgebra Ts} {cod1:SigmaAlgebra Td1}
          {cod2:SigmaAlgebra Td2}.


  Global Instance fst_rv {T1 T2} (a:SigmaAlgebra T1) (b:SigmaAlgebra T2) :
    RandomVariable (product_sa a b)
                   a
                   fst.
  Proof.
    intros ???.
    apply H.
    red.
    exists (event_pre B).
    exists (pre_Ω).
    destruct B.
    split; trivial.
    split; [apply sa_all |].
    unfold equiv, pre_event_equiv, pre_Ω.
    tauto.
  Qed.

  Global Instance snd_rv {T1 T2} (a:SigmaAlgebra T1) (b:SigmaAlgebra T2) :
    RandomVariable (product_sa a b)
                   b
                   snd.
  Proof.
    intros ???.
    apply H.
    red.
    exists (pre_Ω).
    exists (event_pre B).
    split; [apply sa_all |].
    destruct B.
    split; trivial.
    unfold equiv, pre_event_equiv, pre_Ω.
    tauto.
  Qed.

  Global Instance product_sa_rv
         (X1:Ts->Td1) (X2:Ts->Td2) 
         {rv1:RandomVariable dom cod1 X1}
         {rv2:RandomVariable dom cod2 X2} :
    RandomVariable dom (product_sa cod1 cod2) (fun a => (X1 a, X2 a)).
  Proof.
    intros ?.
    red in rv1, rv2.
    unfold event_preimage in *.
    destruct B; simpl.
    apply generated_sa_closure in s.
    simpl in *.
    dependent induction s.
    - apply sa_all.
    - destruct H as [?[?[?[??]]]].
      eapply sa_proper.
      + intros ?.
        apply H1.
      + simpl.
        apply sa_inter.
        * apply (rv1 (exist _ _ H)).
        * apply (rv2 (exist _ _ H0)).
    - apply sa_countable_union. 
      eauto.
    - apply sa_complement; eauto.
  Qed.

  (* pair_rv = product_sa_rv *)
  (* another name for consistency *)

  Instance compose_product_rv {Ts3} {dom3}
           (f1 : Ts -> Td1)
           (f2 : Ts -> Td2)
           (g : Td1*Td2 -> Ts3)
           {rvf1 : RandomVariable dom cod1 f1}
           {rvf2 : RandomVariable dom cod2 f2}         
           {rvg : RandomVariable (product_sa cod1 cod2) dom3 g} :
    RandomVariable dom dom3 (fun x => g (f1 x, f2 x)).
  Proof.
    intros ?.
    generalize (product_sa_rv f1 f2); intros.
    apply (H (exist _ _ (rvg B))).
  Qed.


End prod_space.

  Instance prod_section_fst_rv {Ts1 Ts2 Td} 
           {dom1 : SigmaAlgebra Ts1} 
           {dom2 : SigmaAlgebra Ts2} 
           {cod : SigmaAlgebra Td} 
           (f : (Ts1 * Ts2) -> Td)
           {rv : RandomVariable (product_sa dom1 dom2) cod f} :
    forall (x : Ts1), RandomVariable dom2 cod (fun y => f (x, y)).
  Proof.
    unfold RandomVariable, event_preimage.
    intros.
    generalize (product_section_fst (sa1 := dom1) (sa2 := dom2) (exist _ _ (rv B)) x).
    apply sa_proper.
    intro z.
    destruct B; now simpl.
  Qed.

  Instance prod_section_snd_rv {Ts1 Ts2 Td} 
           {dom1 : SigmaAlgebra Ts1} 
           {dom2 : SigmaAlgebra Ts2} 
           {cod : SigmaAlgebra Td} 
           (f : (Ts1 * Ts2) -> Td)
           {rv : RandomVariable (product_sa dom1 dom2) cod f} :
    forall (y : Ts2), RandomVariable dom1 cod (fun x => f (x, y)).
  Proof.
    unfold RandomVariable, event_preimage.
    intros.
    generalize (product_section_snd (sa1 := dom1) (sa2 := dom2) (exist _ _ (rv B)) y).
    apply sa_proper.
    intro z.
    destruct B; now simpl.
  Qed.


Section pullback_prod_space.
  
  Context {Ts Td1 Td2 : Type}
          {cod1:SigmaAlgebra Td1}
          {cod2:SigmaAlgebra Td2}.

  Instance pullback_compose_product_rv {Ts3} {dom3}
           (f1 : Ts -> Td1)
           (f2 : Ts -> Td2)
           (g : Td1*Td2 -> Ts3)
           {rvg : RandomVariable (product_sa cod1 cod2) dom3 g} :
    RandomVariable (union_sa (pullback_sa cod1 f1) (pullback_sa cod2 f2))
                   dom3 (fun x => g (f1 x, f2 x)).
  Proof.
    apply compose_product_rv; trivial.
    - generalize (pullback_rv cod1 f1).
      apply RandomVariable_proper_le; try reflexivity.
      apply union_sa_sub_l.
    - generalize (pullback_rv cod2 f2).
      apply RandomVariable_proper_le; try reflexivity.
      apply union_sa_sub_r.
  Qed.  
   
End pullback_prod_space.
      
Section indep.
  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom).

  Definition independent_rvs {Td1} (cod1:SigmaAlgebra Td1) {Td2} (cod2:SigmaAlgebra Td2)
             (X1 : Ts -> Td1) (X2 : Ts -> Td2)
             {rv1:RandomVariable dom cod1 X1}
             {rv2:RandomVariable dom cod2 X2}
    := forall (A:event cod1) (B:event cod2),
      independent_events prts (rv_preimage X1 A) (rv_preimage X2 B).

  Lemma independent_rvs_symm {Td1} (cod1:SigmaAlgebra Td1) {Td2} (cod2:SigmaAlgebra Td2)
        (X1 : Ts -> Td1) (X2 : Ts -> Td2)
        {rv1:RandomVariable dom cod1 X1}
        {rv2:RandomVariable dom cod2 X2} :
    independent_rvs cod1 cod2 X1 X2 <-> independent_rvs cod2 cod1 X2 X1.
  Proof.
    split; intros ???; symmetry; apply H.
  Qed.
  
  Lemma independent_rvs_const_l {Td1} (cod1:SigmaAlgebra Td1) {Td2} (cod2:SigmaAlgebra Td2)
        (c1 : Td1) (X2 : Ts -> Td2)
        {rv2:RandomVariable dom cod2 X2} :
    independent_rvs cod1 cod2 (const c1) X2.
  Proof.
    unfold independent_rvs; intros.
    destruct (rv_preimage_const dom cod1 c1 A)
    ; rewrite H.
    - apply independent_events_all_l.
    - apply independent_events_none_l.
  Qed.

  Lemma independent_rvs_const_r {Td1} (cod1:SigmaAlgebra Td1) {Td2} (cod2:SigmaAlgebra Td2)
        (X1 : Ts -> Td1) (c2 : Td2)
        {rv1:RandomVariable dom cod1 X1} :
    independent_rvs cod1 cod2 X1 (const c2).
  Proof.
    apply independent_rvs_symm.
    apply independent_rvs_const_l.
  Qed.

  Definition independent_rv_collection
             {Idx} {Td:Idx -> Type} (cod:forall (i:Idx), SigmaAlgebra (Td i))
             (X : forall (i:Idx), Ts -> Td i)
             {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)}
    := 
    forall (l:forall i, event (cod i)),
      independent_event_collection prts (fun i => rv_preimage (X i) (l i)).
  
  Definition pairwise_independent_rv_collection
             {Idx} {Td:Idx -> Type} (cod:forall (i:Idx), SigmaAlgebra (Td i))
             (X : forall (i:Idx), Ts -> Td i)
             {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)}
    := forall i j, i <> j -> independent_rvs (cod i) (cod j) (X i) (X j).

  Definition pairwise_independent_rv_collection_alt
             {Idx} {Td:Idx -> Type} (cod:forall (i:Idx), SigmaAlgebra (Td i))
             (X : forall (i:Idx), Ts -> Td i)
             {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)}
    := forall (l:forall i, event (cod i)),
      pairwise_independent_event_collection prts (fun i => rv_preimage (X i) (l i)).

  Lemma pairwise_independent_rv_collection_as_alt 
         {Idx} {dec:EqDec Idx eq} {Td:Idx -> Type} (cod:forall (i:Idx), SigmaAlgebra (Td i))
         (X : forall (i:Idx), Ts -> Td i)
         {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)} :
    pairwise_independent_rv_collection cod X <-> pairwise_independent_rv_collection_alt cod X.
  Proof.
    split.
    - intros HH l i j ij.
      apply (HH _ _ ij).
    - intros HH i j ij A B.
      red in HH.
      assert (Hl:{l : forall i : Idx, event (cod i) |
                l i = A /\
                  l j = B}).
      {

      refine (exist _
                    (fun (k:Idx) => if k == i
                       then _
                       else if k == j
                            then _
                            else _
                    ) _).
      Unshelve.
      2: {
        rewrite e.
        exact A.
      }
      2: {
        rewrite e.
        exact B.
      }
      2: {
        exact event_none.
      }
      split.
      - match_destr; [| congruence].
        red in e.
        unfold eq_rect_r.
        symmetry.
        now rewrite <- eq_rect_eq.
      - match_destr; [congruence |].
        match_destr; [| congruence].
        unfold eq_rect_r.
        symmetry.
        now rewrite <- eq_rect_eq.
      }         
      destruct Hl as [l [??]]; subst.
      apply (HH l i j ij).
  Qed.
  
  Lemma independent_rv_collection_pairwise_independent
        {Idx:Type} {dec:EqDec Idx eq} {Td:Idx -> Type} (cod:forall (i:Idx), SigmaAlgebra (Td i))
        (X : forall (i:Idx), Ts -> Td i)
        {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)} :
    independent_rv_collection cod X -> pairwise_independent_rv_collection cod X.
  Proof.
    intros.
    apply (pairwise_independent_rv_collection_as_alt _).
    intros ????.
    specialize (H l).
    apply independent_event_collection_pairwise_independent in H.
    now apply H.
  Qed.
  
  Definition identically_distributed_rvs {Td} (cod:SigmaAlgebra Td)
             (X1 X2 : Ts -> Td)
             {rv1:RandomVariable dom cod X1}
             {rv2:RandomVariable dom cod X2}
    := forall (A:event cod),
      ps_P (rv_preimage X1 A) = ps_P (rv_preimage X2 A).

  Definition identically_distributed_rv_collection {Td} (cod:SigmaAlgebra Td)
             {Idx} (X : forall (i:Idx), Ts -> Td)
             {rv : forall (i:Idx), RandomVariable dom cod (X i)}
    := forall i j,
      identically_distributed_rvs cod (X i) (X j).

  Definition iid_rv_collection {Td} (cod:SigmaAlgebra Td)
             {Idx} (X : forall (i:Idx), Ts -> Td)
             {rv : forall (i:Idx), RandomVariable dom cod (X i)}
    := independent_rv_collection (const cod) X (rv := rv) /\
         identically_distributed_rv_collection cod X.

  Lemma rv_preimage_compose {Td1} (cod1:SigmaAlgebra Td1) {Td2} (cod2:SigmaAlgebra Td2)
        (X1 : Ts -> Td1) (X2 : Td1 -> Td2)
        {rv1:RandomVariable dom cod1 X1}
        {rv2:RandomVariable cod1 cod2 X2} e :
    rv_preimage (X2 ∘ X1) e === rv_preimage X1 (rv_preimage X2 e).
  Proof.
    intros ?; simpl.
    reflexivity.
  Qed.

  Lemma independent_rv_collection_compose
        {Idx} {Td1:Idx -> Type} (cod1:forall (i:Idx), SigmaAlgebra (Td1 i))
        (X1 : forall (i:Idx), Ts -> Td1 i)
        {rv1 : forall (i:Idx), RandomVariable dom (cod1 i) (X1 i)}
        {Td2:Idx -> Type} (cod2:forall (i:Idx), SigmaAlgebra (Td2 i))
        (X2 : forall (i:Idx), Td1 i -> Td2 i)
        {rv2 : forall (i:Idx), RandomVariable (cod1 i) (cod2 i) (X2 i)} :
    independent_rv_collection cod1 X1 ->
    independent_rv_collection cod2 (fun i => (X2 i) ∘ (X1 i)).
  Proof.
    intros indep ???.
    specialize (indep (fun i => rv_preimage (X2 i) (l i)) l0 H).
    etransitivity; [etransitivity |]; [| apply indep |].
    - apply ps_proper.
      intros ?; simpl.
      split; intros HH ? inn
      ; apply in_map_iff in inn
      ; destruct inn as [? [??]]
      ; subst
      ; apply rv_preimage_compose
      ; apply HH
      ; apply in_map_iff
      ; eauto.
    - f_equal.
      repeat rewrite map_map.
      apply map_ext; intros.
      now rewrite rv_preimage_compose.
  Qed.
  
  Lemma independent_rv_compose
        {Tdx Tdy Tdf Tdg : Type}
        (codx: SigmaAlgebra Tdx)
        (cody: SigmaAlgebra Tdy)
        (codf: SigmaAlgebra Tdf)
        (codg: SigmaAlgebra Tdg)        
        (X : Ts -> Tdx)
        (Y : Ts -> Tdy)
        (f : Tdx -> Tdf)
        (g : Tdy -> Tdg)
        {rvx: RandomVariable dom codx X}
        {rvy: RandomVariable dom cody Y}
        {rvf: RandomVariable codx codf f}
        {rvg: RandomVariable cody codg g} :
    independent_rvs codx cody X Y ->
    independent_rvs codf codg (f ∘ X) (g ∘ Y).
  Proof.
    unfold independent_rvs.
    intros indep A B.
    unfold independent_events.
    do 2 rewrite rv_preimage_compose.
    apply indep.
  Qed.

    Lemma identically_distributed_rv_compose
        {Td Tdf : Type}
        (cod: SigmaAlgebra Td)
        (codf: SigmaAlgebra Tdf)
        (X : Ts -> Td)
        (Y : Ts -> Td)
        (f : Td -> Tdf)
        {rvx: RandomVariable dom cod X}
        {rvy: RandomVariable dom cod Y}
        {rvf: RandomVariable cod codf f} :
      identically_distributed_rvs cod X Y ->
      identically_distributed_rvs codf (f ∘ X) (f ∘ Y).
  Proof.
    unfold identically_distributed_rvs.
    intros ident A.
    do 2 rewrite rv_preimage_compose.
    apply ident.
  Qed.

  Lemma identically_distributed_rv_collection_compose
        {Idx} {Td Tdf : Type}
        (cod: SigmaAlgebra Td)
        (codf: SigmaAlgebra Tdf)        
        (X : forall (i:Idx), Ts -> Td)
        {rv : forall (i:Idx), RandomVariable dom cod (X i)}
        (f : Td -> Tdf)
        {rvf : RandomVariable cod codf f} :
    identically_distributed_rv_collection cod X ->
    identically_distributed_rv_collection codf (fun i => f ∘ (X i)).
  Proof.
    unfold identically_distributed_rv_collection.
    intros.
    now apply identically_distributed_rv_compose.
  Qed.
  
  Lemma independent_rv_sas {Td1} (cod1:SigmaAlgebra Td1) {Td2} (cod2:SigmaAlgebra Td2)
        (X1 : Ts -> Td1) (X2 : Ts -> Td2)
        {rv1:RandomVariable dom cod1 X1}
        {rv2:RandomVariable dom cod2 X2} :
    independent_rvs cod1 cod2 X1 X2 <->
      independent_sas prts (pullback_rv_sub _ _ _ rv1) (pullback_rv_sub _ _ _ rv2).
  Proof.
    unfold independent_rvs, independent_sas.
    split.
    - intros HH A B.
      unfold independent_events in *.
      destruct A as [? [?[??]]].
      destruct B as [? [?[??]]].
      specialize (HH (exist _ _ s) (exist _ _ s0)).
      etransitivity; [etransitivity |]; [| apply HH |].
      + apply ps_proper; intros ?; simpl.
        apply pre_event_inter_proper
        ; intros ?; simpl; auto.
      + f_equal; apply ps_proper; intros ?; simpl; firstorder.
    - intros HH A B.
      specialize (HH (exist _ _ (pullback_sa_pullback _ X1 A (proj2_sig A)))
                     (exist _ _ (pullback_sa_pullback _ X2 B (proj2_sig B)))).
      etransitivity; [etransitivity |]; [| apply HH |].
      + apply ps_proper; intros ?; simpl.
        reflexivity.
      + f_equal; apply ps_proper; intros ?; simpl; reflexivity.
  Qed.

  Global Instance pullback_sa_issub
         {Idx} {Td:Idx -> Type} (cod:forall (i:Idx), SigmaAlgebra (Td i))
         (X : forall (i:Idx), Ts -> Td i)
         {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)} :
    IsSubAlgebras dom (fun n : Idx => pullback_sa (cod n) (X n)).
  Proof.
    now intros ?; apply pullback_rv_sub.
  Qed.
  
  Lemma independent_rv_collection_sas
        {Idx} {Td:Idx -> Type} (cod:forall (i:Idx), SigmaAlgebra (Td i))
        (X : forall (i:Idx), Ts -> Td i)
        {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)} :
    independent_rv_collection cod X <->
      independent_sa_collection prts (fun n => pullback_sa (cod n) (X n)).
  Proof.
    unfold independent_rv_collection, independent_sa_collection.
    split.
    - intros HH A l nd.

      assert (HHc:forall n, 
               exists ye,
                 (sa_sigma (cod n) ye /\
                    forall a, A n a <-> ye (X n a))).
      {
        intros.
        destruct (A n).
        eauto.
      }
      apply non_dep_dep_functional_choice in HHc; try (red; apply choice).
      destruct HHc as [ye HHc].
      specialize (HH (fun n => (exist _ _ (proj1 (HHc n)))) l nd).
      etransitivity; [etransitivity |]; [| apply HH |].
      + apply ps_proper; intros ?; simpl.
        split; intros HH2 a inna.
        * apply in_map_iff in inna.
          destruct inna as [? [??]]; subst; simpl.
          apply HHc.
          apply (HH2 (((fun n : Idx => event_sa_sub (pullback_sa_issub cod X n) (A n)))
                        x0)).
          apply in_map_iff; eauto.
        * apply in_map_iff in inna.
          destruct inna as [? [??]]; subst; simpl.
          apply HHc.
          apply (HH2 ((fun i : Idx => rv_preimage (X i) (exist (sa_sigma _) (ye i) (proj1 (HHc i)))) x0)).
          apply in_map_iff.
          exists x0; eauto.
      + f_equal.
        repeat rewrite map_map.
        apply map_ext; intros.
        apply ps_proper; intros ?; simpl.
        split; apply HHc.
    - intros HH A l nd.
      specialize (HH (fun n => (exist _ _ (pullback_sa_pullback _ (X n) (A n) (proj2_sig (A n)))))).
      etransitivity; [etransitivity |]; [| apply (HH l nd) |].
      + apply ps_proper; intros ?; simpl.
        split; intros HH2 a inna.
        * apply in_map_iff in inna.
          destruct inna as [? [??]]; subst; simpl.
          red.
          apply (HH2 (rv_preimage (X x0) (A x0))).
          apply in_map_iff; eauto.
        * apply in_map_iff in inna.
          destruct inna as [? [??]]; subst; simpl.
          apply (HH2
                   ((fun n : Idx =>
                       event_sa_sub (pullback_sa_issub cod X n)
                                    (exist (pullback_sa_sigma (cod n) (X n)) (pre_event_preimage (X n) (A n))
                                           (pullback_sa_pullback (cod n) (X n) (A n) (proj2_sig (A n))))) x0)).
          apply in_map_iff; eauto.
      + f_equal.
        repeat rewrite map_map.
        apply map_ext; intros.
        apply ps_proper; intros ?; simpl; reflexivity.
  Qed.

  Lemma pairwise_independent_rv_collection_sas
        {Idx} {dec:EqDec Idx eq} {Td:Idx -> Type} (cod:forall (i:Idx), SigmaAlgebra (Td i))
        (X : forall (i:Idx), Ts -> Td i)
        {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)} :
    pairwise_independent_rv_collection cod X <->
      pairwise_independent_sa_collection prts (fun n => pullback_sa (cod n) (X n)).
  Proof.
    rewrite (pairwise_independent_rv_collection_as_alt _).
    split.
    - intros HH A  i j neq.

      assert (HHc:forall n, 
               exists ye,
                 (sa_sigma (cod n) ye /\
                    forall a, A n a <-> ye (X n a))).
      {
        intros.
        destruct (A n).
        eauto.
      }
      apply non_dep_dep_functional_choice in HHc; try (red; apply choice).
      destruct HHc as [ye HHc].
      specialize (HH (fun n => (exist _ _ (proj1 (HHc n)))) i j neq).
      etransitivity; [etransitivity |]; [| apply HH |].
      + apply ps_proper; intros ?; simpl.
        split; intros HH2.
        * destruct HH2.
          now split; simpl; apply HHc.
        * destruct HH2.
          now split; simpl in *; apply HHc.
      + f_equal
        ; apply ps_proper; intros ?; simpl
        ; split; apply HHc.
    - intros HH A i j neq.
      specialize (HH (fun n => (exist _ _ (pullback_sa_pullback _ (X n) (A n) (proj2_sig (A n)))))).
      etransitivity; [etransitivity |]; [| apply (HH i j neq) |].
      + apply ps_proper; intros ?; simpl.
        now split; intros HH2.
      + f_equal
        ; apply ps_proper; intros ?; simpl; reflexivity.
  Qed.
  
  Lemma independent_rvs_proper
        {Td1} (cod1:SigmaAlgebra Td1) (cod1':SigmaAlgebra Td1)
        (eqqs1:sa_equiv cod1 cod1')
        {Td2} (cod2:SigmaAlgebra Td2) (cod2':SigmaAlgebra Td2)
        (eqqs2:sa_equiv cod2 cod2')
        (X1 X1' : Ts -> Td1) (eqqx1:rv_eq X1 X1')
        (X2 X2' : Ts -> Td2) (eqqx2: rv_eq X2 X2')
        {rv1:RandomVariable dom cod1 X1}
        {rv2:RandomVariable dom cod2 X2}
        {rv1':RandomVariable dom cod1' X1'}
        {rv2':RandomVariable dom cod2' X2'} :
    independent_rvs cod1 cod2 X1 X2 <-> independent_rvs cod1' cod2' X1' X2'.
  Proof.
    split; intros HH
    ; apply independent_rv_sas in HH
    ; apply independent_rv_sas
    ; revert HH
    ; apply independent_sas_proper
    ; apply pullback_sa_sigma_proper
    ; repeat red; intros
    ; firstorder.
  Qed.    
      
  Lemma independent_rv_collection_proper
        {Idx} {Td:Idx -> Type}
        (cod:forall (i:Idx), SigmaAlgebra (Td i))
        (cod':forall (i:Idx), SigmaAlgebra (Td i))
        (eqqs:forall i, sa_equiv (cod i) (cod' i))
        (X : forall (i:Idx), Ts -> Td i)
        (X' : forall (i:Idx), Ts -> Td i)
        (eqqx:forall i, rv_eq (X i) (X' i))
        {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)}
        {rv' : forall (i:Idx), RandomVariable dom (cod' i) (X' i)} :
    independent_rv_collection cod X <-> independent_rv_collection cod' X'.
  Proof.
    split; intros HH l
    ; apply independent_rv_collection_sas in HH
    ; apply independent_rv_collection_sas
    ; revert HH
    ; apply independent_sa_collection_proper
    ; intros ?
    ; apply pullback_sa_sigma_proper
    ; repeat red; intros
    ; firstorder.
    symmetry; apply eqqx.
  Qed.

  Lemma pairwise_independent_rv_collection_proper
        {Idx} {Td:Idx -> Type}
        (cod:forall (i:Idx), SigmaAlgebra (Td i))
        (cod':forall (i:Idx), SigmaAlgebra (Td i))
        (eqqs:forall i, sa_equiv (cod i) (cod' i))
        (X : forall (i:Idx), Ts -> Td i)
        (X' : forall (i:Idx), Ts -> Td i)
        (eqqx:forall i, rv_eq (X i) (X' i))
        {rv : forall (i:Idx), RandomVariable dom (cod i) (X i)}
        {rv' : forall (i:Idx), RandomVariable dom (cod' i) (X' i)} :
    pairwise_independent_rv_collection cod X <-> pairwise_independent_rv_collection cod' X'.
  Proof.
    split; intros HH i j ij
    ; generalize (HH i j ij)
    ; now apply independent_rvs_proper.
  Qed.
  
  Lemma identically_distributed_rvs_proper
        {Td} (cod:SigmaAlgebra Td) (cod':SigmaAlgebra Td)
        (eqqs:sa_equiv cod cod')
        (X1 X1' : Ts -> Td) (eqqx1:rv_eq X1 X1')
        (X2 X2' : Ts -> Td) (eqqx2: rv_eq X2 X2')
        {rv1:RandomVariable dom cod X1}
        {rv2:RandomVariable dom cod X2}
        {rv1':RandomVariable dom cod' X1'}
        {rv2':RandomVariable dom cod' X2'} :
    identically_distributed_rvs cod X1 X2 <-> identically_distributed_rvs cod' X1' X2'.
  Proof.
    unfold identically_distributed_rvs.
    split; intros.
    - destruct (eqqs A).
      specialize (H (exist _ _ (H1 (proj2_sig A)))).
      assert (event_equiv (rv_preimage X1' A)
                          (rv_preimage X1 (exist (sa_sigma _) A (H1 (proj2_sig A))))).
      {
        intro x.
        destruct A.
        simpl.
        now rewrite eqqx1.
      }
      assert (event_equiv (rv_preimage X2' A)
                          (rv_preimage X2 (exist (sa_sigma _) A (H1 (proj2_sig A))))).
      {
        intro x.
        destruct A.
        simpl.
        now rewrite eqqx2.
      }
      now rewrite H2, H3.
    - destruct (eqqs A).
      specialize (H (exist _ _ (H0 (proj2_sig A)))).
      assert (event_equiv (rv_preimage X1 A)
                          (rv_preimage X1' (exist (sa_sigma _) A (H0 (proj2_sig A))))).
      {
        intro x.
        destruct A.
        simpl.
        now rewrite eqqx1.
      }
      assert (event_equiv (rv_preimage X2 A)
                          (rv_preimage X2' (exist (sa_sigma _) A (H0 (proj2_sig A))))).
      {
        intro x.
        destruct A.
        simpl.
        now rewrite eqqx2.
      }
      now rewrite H2, H3.
  Qed.

  Lemma identically_distributed_rv_collection_proper 
        {Td} (cod:SigmaAlgebra Td) (cod':SigmaAlgebra Td)
        (eqqs:sa_equiv cod cod')
        {Idx} (X X' : forall (i:Idx), Ts -> Td) 
        (eqqx:forall (i:Idx), rv_eq (X i) (X' i))
        {rv : forall (i:Idx), RandomVariable dom cod (X i)}
        {rv' : forall (i:Idx), RandomVariable dom cod' (X' i)}  :
    identically_distributed_rv_collection cod X <-> 
    identically_distributed_rv_collection cod' X'.
  Proof.
    unfold identically_distributed_rv_collection.
    split; intros; specialize (H i j); revert H;
      now apply identically_distributed_rvs_proper.
  Qed.
    
End indep.

Section ps_pullback.

  Context {Ts:Type} {Td:Type}
          (dom: SigmaAlgebra Ts)
          (cod: SigmaAlgebra Td).

  Lemma rv_preimage_Ω
        (X: Ts -> Td)
        {rvX : RandomVariable dom cod X} :
    rv_preimage X Ω === Ω.
  Proof.
    unfold rv_preimage; intros ?; simpl.
    reflexivity.
  Qed.

  Lemma rv_preimage_union_of_collection
         (X: Ts -> Td)
         {rvX : RandomVariable dom cod X}
         (c : nat -> event cod) :
    rv_preimage X (union_of_collection c) === union_of_collection (fun n => rv_preimage X (c n)).
  Proof.
    intros ?; simpl; reflexivity.
  Qed.

  Lemma rv_preimage_pairwise_disjoint_collection
         (X: Ts -> Td)
         {rvX : RandomVariable dom cod X}
         (c : nat -> event cod) :
    collection_is_pairwise_disjoint c ->
    collection_is_pairwise_disjoint (fun n : nat => rv_preimage X (c n)).
  Proof.
    intros ???????; simpl in *.
    unfold event_preimage in *.
    now apply (H n1 n2 H0 _ H1 H2).
  Qed.

  Program Instance pullback_ps 
           (ps : ProbSpace dom)
           (X: Ts -> Td)
           {rvX : RandomVariable dom cod X}
    : ProbSpace cod
    :=
    {|
      ps_P a := ps_P (rv_preimage X a)
    |}.
  Next Obligation.
    intros ???.
    apply ps_proper.
    now rewrite H.
  Qed.
  Next Obligation.
    rewrite rv_preimage_union_of_collection.
    apply ps_countable_disjoint_union.
    now apply rv_preimage_pairwise_disjoint_collection.
  Qed.
  Next Obligation.
    now rewrite rv_preimage_Ω, ps_all.
  Qed.
  Next Obligation.
    apply ps_pos.
  Qed.

End ps_pullback.

Section iso_rvs.
  Instance rv_dom_iso_sa_f {Ts Ts' Td} {dom : SigmaAlgebra Ts} {cod : SigmaAlgebra Td} {rv_X : Ts -> Td}
    (iso:Isomorphism Ts Ts')
    (rv:RandomVariable dom cod rv_X) :
    RandomVariable (iso_sa (iso:=iso) dom) cod (fun ω' => rv_X (iso_b ω')).
  Proof.
    now apply pullback_compose_rv.
  Qed.

  Instance rv_dom_iso_sa_b {Ts Ts' Td} (dom : SigmaAlgebra Ts) (cod : SigmaAlgebra Td) (rv_X : Ts -> Td) 
    (iso:Isomorphism Ts Ts')
    (rv:RandomVariable (iso_sa (iso:=iso) dom) cod (fun ω' => rv_X (iso_b ω'))) :
    RandomVariable dom cod rv_X.
  Proof.
    generalize (rv_dom_iso_sa_f (Isomorphism_symm iso) rv).
    eapply RandomVariable_proper; try reflexivity.
    - symmetry.
      apply iso_sa_symm_id.
    - intros ?; simpl.
      now rewrite iso_b_f.
  Qed.

  Instance iso_f_rv {Ts Ts'} (dom : SigmaAlgebra Ts) (iso:Isomorphism Ts Ts') :
    RandomVariable dom (iso_sa (iso:=iso) dom) (iso_f).
  Proof.
    intros ?.
    destruct B.
    simpl in s.
    destruct s as [? [??]]; simpl.
    unfold event_preimage; simpl.
    revert s.
    apply sa_proper; intros ?.
    rewrite i.
    now rewrite iso_b_f.
  Qed.

  Instance iso_b_rv {Ts Ts'} (dom : SigmaAlgebra Ts) (iso:Isomorphism Ts Ts') :
    RandomVariable (iso_sa (iso:=iso) dom) dom (iso_b).
  Proof.
    intros ?.
    simpl.
    apply pullback_sa_pullback.
    now destruct B.
  Qed.

  Instance rv_cod_iso_sa_f {Ts Td Td'} {dom : SigmaAlgebra Ts} {cod : SigmaAlgebra Td} {rv_X : Ts -> Td}
    (iso:Isomorphism Td Td')
    (rv:RandomVariable dom cod rv_X) :
    RandomVariable dom (iso_sa (iso:=iso) cod) (fun ω' => iso_f (Isomorphism:=iso) (rv_X ω')).
  Proof.
    apply compose_rv; trivial.
    apply iso_f_rv.
  Qed.

  Instance rv_cod_iso_sa_b {Ts Td Td'} {dom : SigmaAlgebra Ts} {cod : SigmaAlgebra Td} {rv_X : Ts -> Td}
    (iso:Isomorphism Td Td')
    (rv:RandomVariable dom (iso_sa (iso:=iso) cod) (fun ω' => iso_f (Isomorphism:=iso) (rv_X ω'))) :
    RandomVariable dom cod rv_X.
  Proof.
    generalize (@compose_rv _ _ _ _ (iso_sa cod) cod (fun ω' : Ts => iso_f (rv_X ω')) iso_b); intros HH.
    cut_to HH.
    - revert HH.
      apply RandomVariable_proper; try reflexivity.
      intros ?.
      unfold compose.
      now rewrite iso_b_f.
    - trivial.
    - apply iso_b_rv.
  Qed.

End iso_rvs.
