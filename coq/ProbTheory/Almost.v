Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Classical ClassicalChoice Reals Lra.
Require Import utils.Utils ProbSpace.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope R.
Local Open Scope prob.

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

  Lemma almost_forall {Pn:nat -> pre_event Ts} :
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

  Definition almostR2 (r1 r2:Ts -> Td) : Prop
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
    : Proper (almostR2 prts impl ==> impl) (almost prts) | 4.
  Proof.
    unfold almostR2.
    intros ????.
    eapply almost_impl'; eauto.
  Qed.

  Global Instance almost_iff
    : Proper (almostR2 prts iff ==> iff) (almost prts) | 5.
  Proof.
    unfold almostR2.
    intros ?? a1
    ; split; intros a2
    ; generalize (almost_and prts a1 a2)
    ; apply almost_proper; intros ?[??]; tauto.
  Qed.

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

  Lemma ps_almostR2_sub (P1 P2 : event dom) :
    almostR2 prts impl P1 P2 -> ps_P P1 <= ps_P P2.
  Proof.
    intros [a [??]].

    rewrite <- (ps_inter_r1 prts H (A:=P1)).
    rewrite <- (ps_inter_r1 prts H (A:=P2)).
    apply ps_sub.
    unfold event_inter, pre_event_inter.
    intros ? [??]; simpl in *.
    split; trivial.
    now apply H0.
  Qed.

  Lemma ps_almostR2_proper (P1 P2 : event dom) :
    almostR2 prts iff P1 P2 -> ps_P P1 = ps_P P2.
  Proof.
    intros [a [??]].

    rewrite <- (ps_inter_r1 prts H (A:=P1)).
    rewrite <- (ps_inter_r1 prts H (A:=P2)).
    apply ps_proper.
    unfold event_inter, pre_event_inter; intros x; simpl.
    specialize (H0 x).
    tauto.
  Qed.

  Lemma almostR2_sub_event_prob0 (P1 P2 : event dom) :
    ps_P P2 = 0 ->
    almostR2 prts impl P1 P2 -> ps_P P1 = 0.
  Proof.
    intros.
    generalize (ps_almostR2_sub P1 P2 H0); intros.
    generalize (ps_pos P1); intros.
    lra.
  Qed.

  Lemma almost_f_equal {B C} (f:B->C) (x1 x2:Ts->B) :
    almostR2 prts eq (fun x => x1 x) (fun x => x2 x) ->
    almostR2 prts eq (fun x => f (x1 x)) (fun x => f (x2 x)).
  Proof.
    eapply almost_impl; try eapply a1.
    apply all_almost; intros ??.
    congruence.
  Qed.

  
End almostR2_part.
