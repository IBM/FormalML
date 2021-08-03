Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Lra.
Require Import Reals.
Require Import Classical.

Require Import BorelSigmaAlgebra.
Require Import ProbSpace.
Require Import RandomVariable.
Require Import RealRandomVariable.

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

  Context (R:Td->Td->Prop).

  Definition almostR2 (r1 r2:Ts -> Td)
    := exists E, ps_P E = 1
            /\ forall x, E x -> R (r1 x) (r2 x).

  
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

End borel_almostR2_eq.


