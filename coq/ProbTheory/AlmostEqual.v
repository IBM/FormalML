Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra.
Require Import Reals.
Require Import Classical ClassicalChoice.

Require Import BorelSigmaAlgebra.
Require Import ProbSpace.
Require Import RandomVariable.
Require Import RealRandomVariable.
Require Import Coquelicot.Rbar.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R.
Local Open Scope prob.

(*
Class HasEventEq {Td:Type} (cod:SigmaAlgebra Td)
  := sa_event_eq :
       forall {Ts} {dom:SigmaAlgebra Ts} (r1 r2:Ts->Td)
         {rv1:RandomVariable dom cod r1}
         {rv2:RandomVariable dom cod r2},
         sa_sigma (fun x => r1 x = r2 x).

Global Instance borel_haseqs : HasEventEq borel_sa.
Proof.
  red; intros.
  eapply sa_proper
  ; [| apply (sa_preimage_singleton (rvminus r1 r2) 0)].
  red; intros.
  unfold pre_event_preimage, pre_event_singleton, rvminus, rvplus, rvopp, rvscale.
  split; lra.
Qed.
 *)
Section almost.


  Context {Ts:Type} {Td:Type}
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Definition almost (P:Ts -> Prop)
    := exists E, ps_P E = 1
            /\ forall x, E x -> P x.

  Definition almost_alt (P:Ts->Prop)
    := exists E, ps_P E = 0
            /\ forall x, ~ P x -> E x.

  Lemma almost_alt_eq
        (P:Ts->Prop)
    : almost P <-> almost_alt P.
  Proof.
    unfold almost, almost_alt.
    split ; intros [E [Eall eq_on]]
    ; exists (¬ E).
    - split.
      + rewrite ps_complement, Eall; lra.
      + unfold event_complement; simpl.
        firstorder.
    - split.
      + rewrite ps_complement, Eall; lra.
      + unfold event_complement, pre_event_complement; simpl.
        intros.
        destruct (classic (P x)); trivial.
        elim H.
        now apply eq_on.
  Qed.

  Global Instance almost_proper : Proper (pointwise_relation _ impl ==> impl) almost.
  Proof.
    intros ?? eqq [E [eone ?]].
    exists E.
    split; trivial; intros.
    apply eqq; auto.
  Qed.

  Global Instance almost_proper_iff : Proper (pointwise_relation _ iff ==> iff) almost.
  Proof.
    intros ?? eqq.
    split; apply almost_proper; firstorder.
  Qed.

  Global Instance almost_alt_proper : Proper (pointwise_relation _ impl ==> impl) almost_alt.
  Proof.
    intros ?? eqq [E [eone ?]].
    exists E.
    split; trivial; intros.
    red in eqq.
    firstorder.
  Qed.

  Global Instance almost_alt_proper_iff : Proper (pointwise_relation _ iff ==> iff) almost_alt.
  Proof.
    intros ?? eqq.
    split; apply almost_alt_proper; firstorder.
  Qed.

  (* Move *)
  Lemma ps_union_sub 
        {T : Type} {σ : SigmaAlgebra T} (ps : ProbSpace σ) (A B : event σ) :
    ps_P A <= ps_P (A ∪ B).
  Proof.
    apply ps_sub.
    auto with prob.
  Qed.

  Lemma all_almost {P:Ts->Prop} :
    (forall x, P x) ->
    almost P.
  Proof.
    exists Ω; auto with prob.
  Qed.

  Lemma almost_witness {P:pre_event Ts} :
    almost P -> exists x, P x.
  Proof.
    intros [p [pone pP]].
    destruct (classic_event_none_or_has p).
    - destruct H; eauto.
    - rewrite H in pone.
      rewrite ps_none in pone.
      lra.
  Qed.

  Lemma almost_and {P1 P2:pre_event Ts} :
    almost P1 ->
    almost P2 ->
    almost (pre_event_inter P1 P2).
  Proof.
    intros [E1 [E1one E1P]].
    intros [E2 [E2one E2P]].
    exists (event_inter E1 E2).
    split.
    - rewrite ps_inter_l1; trivial.
    - intros ? [??].
      split; auto.
  Qed.

  Lemma almost_countable_and {Pn:nat -> pre_event Ts} :
    (forall n, almost (Pn n)) ->
    almost (pre_inter_of_collection Pn).
  Proof.
    intros a.
    apply choice in a.
    destruct a as [pn ?].
    exists (inter_of_collection pn).
    split.
    - apply ps_one_countable_inter; intros.
      apply H.
    - intros ?? n.
      apply (H n).
      apply H0.
  Qed.
  
  Lemma almost_impl' {P1 P2:Ts->Prop} :
    almost P1 ->
    almost (fun x => P1 x -> P2 x) ->
    almost P2.
  Proof.
    intros a1 a2.
    generalize (almost_and a1 a2).
    apply almost_proper; intros ?[??]; auto.
  Qed.
  
  Lemma almost_or_l (P1 P2:Ts->Prop) :
    almost P1 ->
    almost (pre_event_union P1 P2).
  Proof.
    intros a.
    apply (almost_impl' a).
    apply all_almost; firstorder.
  Qed.

  Context (R:Td->Td->Prop).

  Definition almostR2 (r1 r2:Ts -> Td)
    := almost (fun x => R (r1 x) (r2 x)).
  
  Global Instance almost_refl {R_refl:Reflexive R}: Reflexive almostR2.
  Proof.
    unfold almost; intros eqq.
    exists Ω.
    split.
    - auto with prob.
    - intros x?.
      reflexivity.
  Qed.

  Global Instance almost_symm {R_refl:Symmetric R}: Symmetric almostR2.
  Proof.
    unfold almostR2; intros ??.
    intros [P [Pall eq_on]].
    exists P.
    firstorder.
  Qed.

  Global Instance almostR2_trans {R_refl:Transitive R}: Transitive almostR2.
  Proof.
    unfold almostR2; intros x y z.
    intros [P1 [P1all eq_on1]] [P2 [P2all eq_on2]].
    exists (P1 ∩ P2). split.
    + now apply ps_one_inter.
    + intros a [??]; simpl in *.
      transitivity (y a); eauto.
  Qed.

  Global Instance almostR2_pre {R_pre:PreOrder R}: PreOrder almostR2.
  Proof.
    constructor; typeclasses eauto.
  Qed.
  
  Global Instance almostR2_equiv {R_equiv:Equivalence R}: Equivalence almostR2.
  Proof.
    constructor; typeclasses eauto.
  Qed.

End almost.

Section almostR2_part.
  Context {Ts:Type} {Td:Type}
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom).

  Global Instance almostR2_part {eqR preR:Td->Td->Prop} {R_equiv:Equivalence eqR} {R_pre:PreOrder preR} {R_part:PartialOrder eqR preR}:
    PartialOrder (almostR2 prts eqR) (almostR2 prts preR).
  Proof.
    intros x y.
    split.
    - intros [P [Pall eq_on]].
      split.
      + red.
        exists P.
        split; trivial.
        intros a Pa.
        specialize (R_part (x a) (y a)).
        simpl in R_part.
        destruct R_part as [HH _].
        apply HH; auto.
      + exists P.
        split; trivial.
        intros a Pa.
        specialize (R_part (x a) (y a)).
        simpl in R_part.
        destruct R_part as [HH _].
        apply HH; auto.
    - intros [[P1 [P1all eq_on1]] [P2 [P2all eq_on2]]].
      exists (P1 ∩ P2). split.
      + now apply ps_one_inter.
      + intros a [??]; simpl in *.
        transitivity (y a).
        * apply R_part.
          unfold relation_conjunction, predicate_intersection, flip; simpl.
          intuition.
        * intuition.
  Qed.

  
  Global Instance almostR2_subrelation {R1 R2:Td->Td->Prop} {R_subr:subrelation R1 R2}:
    subrelation (almostR2 prts R1) (almostR2 prts R2).
  Proof.
    intros ?? [P [Pall eq_on]].
    exists P.
    split; trivial.
    intros.
    apply R_subr; auto.
  Qed.

  Lemma almost_Ω (P:Ts->Prop) :
    almost prts P ->
    almostR2 prts iff P pre_Ω.
  Proof.
    intros aP.
    destruct aP as [p [pone ph]].
    exists p.
    split; trivial.
    firstorder.
  Qed.

  Global Instance almost_impl
    : Proper (almostR2 prts impl ==> impl) (almost prts).
  Proof.
    unfold almostR2.
    intros ????.
    eapply almost_impl'; eauto.
  Qed.

  Global Instance almost_iff
    : Proper (almostR2 prts iff ==> iff) (almost prts).
  Proof.
    unfold almostR2.
    intros ?? a1
    ; split; intros a2
    ; generalize (almost_and prts a1 a2)
    ; apply almost_proper; intros ?[??]; tauto.
  Qed.

  Definition classic_dec {T : Type} (P : pre_event T)
    := (fun a => ClassicalDescription.excluded_middle_informative (P a)).

  Lemma almost_map_split {B} {f:Ts->B} {P:B->Prop} :
    almost prts (fun x => P (f x)) ->
    exists f', almostR2 prts eq f f' /\
          (forall x, P (f' x)).
  Proof.
    intros aP.
    destruct (almost_witness _ aP) as [x Px].
    destruct aP as [p [pone ph]].
    exists (fun ts:Ts => if ClassicalDescription.excluded_middle_informative (p ts) then f ts else (f x)).
    repeat split.
    - exists p.
      split; trivial.
      intros.
      match_destr; tauto.
    - intros.
      match_destr; eauto.
  Qed.

  Lemma almost_map_R_split {f:Ts->R} {P:R->Prop} :
    almost prts (fun x => P (f x)) ->
    exists f', almostR2 prts eq f f' /\
          (forall x, P (f' x)) /\
          (RandomVariable dom borel_sa f -> RandomVariable dom borel_sa f').
  Proof.
    intros aP.
    destruct (almost_witness _ aP) as [x Px].
    destruct aP as [p [pone ph]].
    exists (rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec p))) x) 0 then false else true)

                f
                (const (f x))
             ).
    repeat split.
    - exists p.
      split; trivial.
      intros.
      rv_unfold.
      destruct (classic_dec p x0); try tauto.
      destruct (Req_EM_T 1 0); try lra; tauto.
    - intros.
      rv_unfold.
      destruct (classic_dec p x0); try tauto.
      + destruct (Req_EM_T 1 0); try lra; auto.
      + destruct (Req_EM_T 0 0); try lra; auto.
    - intros.
      apply measurable_rv.
      eapply rvchoice_rv; trivial.
      + apply EventIndicator_rv.
      + typeclasses eauto.
  Qed.

  Lemma almost_map_Rbar_split {f:Ts->Rbar} {P:Rbar->Prop} :
    almost prts (fun x => P (f x)) ->
    exists f', almostR2 prts eq f f' /\
          (forall x, P (f' x)) /\
          (RandomVariable dom Rbar_borel_sa f -> RandomVariable dom Rbar_borel_sa f').
  Proof.
    intros aP.
    destruct (almost_witness _ aP) as [x Px].
    destruct aP as [p [pone ph]].
    exists (Rbar_rvchoice (fun x => if Req_EM_T (((EventIndicator (classic_dec p))) x) 0 then false else true)

                f
                (const (f x))
             ).
    repeat split.
    - exists p.
      split; trivial.
      intros.
      rv_unfold; unfold Rbar_rvchoice.
      destruct (classic_dec p x0); try tauto.
      destruct (Req_EM_T 1 0); try lra; try tauto.
    - intros.
      rv_unfold; unfold Rbar_rvchoice.
      destruct (classic_dec p x0); try tauto.
      + destruct (Req_EM_T 1 0); try lra; auto.
      + destruct (Req_EM_T 0 0); try lra; auto.
    - intros.
      apply Rbar_measurable_rv.
      eapply Rbar_rvchoice_rv; trivial.
      + apply EventIndicator_rv.
      + typeclasses eauto.
  Qed.

End almostR2_part.

Section borel_almostR2_eq.

  Global Instance almostR2_eq_plus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvplus.
      now rewrite eq_onx, eq_ony.
  Qed.

  Global Instance almostR2_eq_scale_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (eq ==> almostR2 prts eq ==> almostR2 prts eq) rvscale.
  Proof.
    unfold almostR2 in *.
    intros ? c ? x1 x2 [Px [Pxall eq_onx]]; subst.
    exists Px.
    split; trivial.
    intros.
    unfold rvscale.
    now rewrite eq_onx.
  Qed.

  Global Instance almostR2_eq_opp_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq) rvopp.
  Proof.
    now apply almostR2_eq_scale_proper.
  Qed.

  Global Instance almostR2_eq_minus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvminus.
  Proof.
    intros ??????.
    unfold rvminus.
    now rewrite H, H0.
  Qed.  

  Global Instance almostR2_le_plus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts Rle ==> almostR2 prts Rle ==> almostR2 prts Rle) rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvplus.
      apply Rplus_le_compat; auto.
  Qed.

  Global Instance almostR2_le_lt_plus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts Rle ==> almostR2 prts Rlt ==> almostR2 prts Rlt) rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvplus.
      apply Rplus_le_lt_compat; auto.
  Qed.

  Global Instance almostR2_lt_le_plus_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts Rlt ==> almostR2 prts Rle ==> almostR2 prts Rlt) rvplus.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvplus.
      apply Rplus_lt_le_compat; auto.
  Qed.

  Global Instance almostR2_eq_mult_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) rvmult.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold rvmult.
      now rewrite eq_onx, eq_ony.
  Qed.

  Global Instance almostR2_eq_Rbar_mult_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : Proper (almostR2 prts eq ==> almostR2 prts eq ==> almostR2 prts eq) Rbar_rvmult.
  Proof.
    unfold almostR2 in *.
    intros x1 x2 [Px [Pxall eq_onx]] y1 y2 [Py [Pyall eq_ony]].
    exists (Px ∩ Py).
    split.
    - now apply ps_one_inter.
    - intros a [Pxa Pya].
      unfold Rbar_rvmult.
      now rewrite eq_onx, eq_ony.
  Qed.

  Global Instance almostR2_sub
         {Ts Td:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom)
         (R:Td->Td->Prop)
         (f:(Ts->Td)->Ts->Td)
         (fpres: forall x y a, R (x a) (y a) -> R (f x a) (f y a))
    : Proper (almostR2 prts R ==> almostR2 prts R) f.
  Proof.
    intros x1 x2 [Px [Pxall eq_onx]].
    exists Px.
    split; trivial.
    intros; auto.
  Qed.

  Lemma almostR2_eq_pow_abs_proper
        {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom) 
        (x1 x2: Ts -> R)
        n
        (eqqx : almostR2 prts eq (rvabs x1) (rvabs x2)) :
    almostR2 prts eq (rvpow (rvabs x1) n) (rvpow (rvabs x2) n).
  Proof.
    apply (almostR2_sub prts eq (fun x => rvpow x n)); trivial.
    intros.
    now unfold rvpow; rewrite H.
  Qed.

  Global Instance almostR2_eq_power_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) :
    Proper (almostR2 prts eq ==> eq ==> almostR2 prts eq) rvpower.
  Proof.
    intros x1 x2 eqq1 ? n ?; subst.
    apply (almostR2_sub prts eq (fun x => rvpower x n)); trivial.
    intros.
    unfold rvpower, RealAdd.power.
    now rewrite H.
  Qed.

  Global Instance almostR2_eq_abs_proper
         {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) : 
    Proper (almostR2 prts eq ==> almostR2 prts eq) rvabs.
  Proof.
    eapply almostR2_sub; eauto; try typeclasses eauto.
    intros.
    unfold rvabs.
    now rewrite H.
  Qed.

  Global Instance almostR2_eq_subr {Ts Td:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) :
    subrelation (@rv_eq Ts Td) (almostR2 prts eq).
  Proof.
    intros ???.
    exists Ω.
    split; auto with prob.
  Qed.

  Global Instance almostR2_le_subr {Ts:Type} 
         {dom: SigmaAlgebra Ts}
         (prts: ProbSpace dom) :
    subrelation (@rv_le Ts) (almostR2 prts Rle).
  Proof.
    intros ???.
    exists Ω.
    split; auto with prob.
  Qed.

  Global Instance rv_le_sub_eq {Ts:Type}: subrelation (@rv_eq Ts R) rv_le.
  Proof.
    unfold rv_eq, rv_le.
    intros ????.
    rewrite H.
    lra.
  Qed.

  Lemma almostR2_eq_plus_inv  {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom) {x y z} :
    almostR2 prts eq z (rvplus x y) ->
    exists x' y',
      almostR2 prts eq x x' /\
      almostR2 prts eq y y' /\ 
      rv_eq z (rvplus x' y').
  Proof.
    intros [p [pone px]].
    exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then x a else 0).
    exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then y a else z a).
    split; [| split].
    - exists p.
      split; trivial.
      intros ??.
      match_destr.
      tauto.
    - exists p.
      split; trivial.
      intros ??.
      match_destr.
      tauto.
    - intros a; simpl.
      rv_unfold.
      match_destr.
      + auto.
      + lra.
  Qed.

  Lemma almostR2_eq_opp_inv  {Ts:Type} 
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom) {x z} :
    almostR2 prts eq z (rvopp x) ->
    exists x',
      almostR2 prts eq x x' /\
      rv_eq z (rvopp x').
  Proof.
    intros [p [pone px]].

    exists (fun a => if ClassicalDescription.excluded_middle_informative (p a) then x a else - z a).
    split.
    - exists p.
      split; trivial.
      intros ??.
      match_destr.
      tauto.
    - intros ?.
      rv_unfold.
      match_destr.
      + auto.
      + lra.
  Qed.

End borel_almostR2_eq.


