Require Import QArith NumberIso.
Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Classical ClassicalChoice Reals Lra.
Require Import utils.Utils ProbSpace.
Require Import Coquelicot.Rbar Coquelicot.Hierarchy.

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

  Lemma almost_impl' {P1 P2:Ts->Prop} :
    almost P1 ->
    almost (fun x => P1 x -> P2 x) ->
    almost P2.
  Proof.
    intros a1 a2.
    generalize (almost_and a1 a2).
    apply almost_proper; intros ?[??]; auto.
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

  Lemma forall_almost {Pn:nat -> pre_event Ts} :
    almost (pre_inter_of_collection Pn) ->
    (forall n, almost (Pn n)).
  Proof.
    intros [p [pone ?]] n.
    exists p; split; trivial.
    intros x px.
    now apply H.
  Qed.

  Lemma almost_forall_iff (Pn:nat -> pre_event Ts) :
    (forall n, almost (Pn n)) <->
      almost (pre_inter_of_collection Pn).
  Proof.
    split.
    - apply almost_forall.
    - apply forall_almost.
  Qed.

  Lemma almost_exists {Idx} {Pn:Idx -> pre_event Ts} (n : Ts -> Idx) :
    almost (fun ω => Pn (n ω) ω) ->
    almost (fun ω => exists n : Idx, Pn n ω).
  Proof.
    intros [p [pone ?]].
    exists p; eauto.
  Qed.

  (* this is classically true, with choice *)
  Lemma exists_almost {Idx} {Pn:Idx -> pre_event Ts} :
    almost (fun ω => exists n : Idx, Pn n ω) ->
    (exists (n : Ts -> Idx), almost (fun ω => Pn (n ω) ω)).
  Proof.
    intros palm.
    destruct (almost_witness palm) as [_ [n _]].
    destruct palm as [p [pone ?]].
    assert (HH:forall x : Ts, exists n : Idx, p x ->  Pn n x).
    {
      intros ts.
      destruct (classic (p ts)).
      - destruct (H _ H0).
        exists x; trivial.
      - exists n.
        tauto.
    }
    apply choice in HH.
    destruct HH as [f ?].
    exists f.
    exists p.
    split; trivial.
  Qed.

  Lemma almost_impl_restr (P Q:Ts->Prop) :
    (forall R, (forall x, R x -> P x) -> almost (fun x => R x -> Q x)) -> almost (fun x => P x) -> almost (fun x => Q x).
  Proof.
    intros.
    destruct H0 as [?[??]].
    specialize (H (fun a => x a)); simpl in *.
    apply H in H1.
    destruct H1 as [?[??]].
    exists (event_inter x x0).
    split.
    - rewrite ps_inter_l1; trivial.
    - intros ? [??].
      firstorder.
  Qed.

  Lemma almost_exists_iff {Idx} {Pn:Idx -> pre_event Ts} :
    (exists (n : Ts -> Idx), almost (fun ω => Pn (n ω) ω)) <->
    almost (fun ω => exists n : Idx, Pn n ω).
  Proof.
    split.
    - intros [??].
      eapply almost_exists; eauto.
    - apply exists_almost.
  Qed.

  Lemma almost_forallQ (Pn:Q->pre_event Ts) :
      (forall n : Q, almost (Pn n)) -> almost (fun ts => forall n, Pn n ts).
    Proof.
      intros.
      cut (almost (fun ts => forall (a:nat),
                            Pn (iso_b a) ts)).
      {
        intros HH.
        eapply almost_impl'; try eapply HH.
        apply all_almost; intros ???.
        generalize (H0 (iso_f n)).
        now rewrite iso_b_f.
      }

      apply almost_forall; intros.
      apply H.
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

  Global Instance almostR2_eq_proper {RR:Td->Td->Prop} :
    Proper (almostR2 prts eq ==> almostR2 prts eq ==> iff) (almostR2 prts RR).
  Proof.
    cut (Proper (almostR2 prts eq ==> almostR2 prts eq ==> impl) (almostR2 prts RR)).
    {
      intros ???????.
      split; intros HH
      ; eapply H; try eapply HH
      ; trivial
      ; now symmetry.
    }       
    intros ???????.
    generalize (almost_and _ (almost_and _ H H0) H1).
    apply almost_impl; apply all_almost; intros ? [[??]?].
    congruence.
  Qed.

    Lemma almost_bounded_forall 
        (P:nat->Prop)
        (dec:forall n, {P n} + {~ P n})
        {Pn:forall i (pf:P i), pre_event Ts} :
    (forall i pf1 pf2 x, Pn i pf1 x -> Pn i pf2 x) ->
    (forall n pf, almost prts (Pn n pf)) ->
    almost prts (fun x => forall n pf, Pn n pf x).
  Proof.
    intros prop a.
    assert (forall n, almost prts (
                          match dec n with
                          | left pf => (Pn n pf)
                          | right _ => fun _ => True
                          end
                        )).
    {
      intros.
      match_destr.
      now apply all_almost.
    }
    apply almost_forall in H.
    revert H.
    apply almost_impl.
    apply all_almost.
    intros ??.
    red in H.
    intros.
    specialize (H n).
    match_destr_in H; try tauto.
    eapply prop; eauto.
  Qed.

  Lemma bounded_forall_almost
        (P:nat->Prop)
        (dec:forall n, {P n} + {~ P n})
        {Pn:forall i (pf:P i), pre_event Ts} :
    (forall i pf1 pf2 x, Pn i pf1 x -> Pn i pf2 x) ->
    almost prts (fun x => forall n pf, Pn n pf x) ->
    (forall n pf, almost prts (Pn n pf)).
  Proof.
    intros prop a.
    assert (forall n, almost prts (
                          match dec n with
                          | left pf => (Pn n pf)
                          | right _ => fun _ => True
                          end
                        )).
    {
      intros.
      match_destr.
      - apply forall_almost with (n:=n) in a.
        revert a.
        apply almost_impl.
        apply all_almost; intros ??.
        apply H.
      - now apply all_almost.
    }
    intros n pf.
    generalize (H n).
    match_destr.
    - apply almost_impl.
      apply all_almost; intros ?; red.
      apply prop.
    - tauto.
  Qed.

  Lemma almost_bounded_forall_iff
        (P:nat->Prop)
        (dec:forall n, {P n} + {~ P n})
        {Pn:forall i (pf:P i), pre_event Ts} :
    (forall i pf1 pf2 x, Pn i pf1 x -> Pn i pf2 x) ->
    (forall n pf, almost prts (Pn n pf)) <->
    almost prts (fun x => forall n pf, Pn n pf x).
  Proof.
    split.
    - now apply almost_bounded_forall.
    - now apply bounded_forall_almost.
  Qed.

  (* classically true *)
  Lemma almost_independent_impl (P:Prop) (Q:Ts->Prop) :
    (P -> almost prts Q) <-> almost prts (fun ts => P -> Q ts).
  Proof.
    split.
    - intros PQ.
      destruct (classic P).
      + generalize (PQ H).
        apply almost_impl; apply all_almost; intros ???; trivial.
      + apply all_almost; intros ??; tauto.
    - intros HH ?.
      revert HH.
      apply almost_impl; apply all_almost; intros ??; auto.
  Qed.

  Lemma almost_eventually (P : nat -> Ts -> Prop) :
    eventually (fun n => almost prts (fun ω => P n ω)) ->
    almost prts (fun ω => eventually (fun n => P n ω)).
  Proof.
    intros [N alm].
    apply almost_bounded_forall in alm.
    - revert alm.
      apply almost_impl.
      apply all_almost; intros ω Pω.
      exists N; trivial.
    - intros.
      apply le_dec.
    - trivial.
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

Section sa_sub.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts:ProbSpace dom)
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).

    Lemma almostR2_prob_space_sa_sub_lift {A}
        RR
        (f1 f2:Ts -> A):
    almostR2 (prob_space_sa_sub prts sub) RR f1 f2 ->
    almostR2 prts RR f1 f2.
  Proof.
    intros [p [pone peqq]].
    red.
    simpl in *.
    exists (event_sa_sub sub p).
    split; trivial.
  Qed.

  Lemma almost_prob_space_sa_sub_lift
        (prop : Ts -> Prop) :
    almost (prob_space_sa_sub prts sub) prop ->
    almost prts prop.
  Proof.
    intros [p [pone peqq]].
    red.
    simpl in *.
    exists (event_sa_sub sub p).
    split; trivial.
  Qed.

End sa_sub.

Section sa_restricted.

  Lemma almost_prob_space_event_restricted
          {Ts:Type} 
          {σ: SigmaAlgebra Ts}
          (prts:ProbSpace σ)
          (e:event σ) (pf:0 < ps_P e) 
        (prop : Ts -> Prop) :
    almost prts prop ->
    almost (event_restricted_prob_space prts e pf) (event_restricted_function e prop).
  Proof.
    intros [p [pone peqq]].
    red.
    exists (event_restricted_event e p).
    split.
    - simpl.
      unfold cond_prob.
      rewrite <- event_restricted_inter.
      rewrite ps_inter_l1, Rdiv_diag; trivial.
      lra.
    - intros [??]; simpl.
      unfold event_restricted_pre_event; red; simpl.
      apply peqq.
  Qed.      

End sa_restricted.

