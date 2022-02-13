Require Import LibUtilsCoqLibAdd.

Require Import ClassicalDescription.
Require Import PeanoNat.
Require Import Morphisms.

Section find.
  Context {P: nat -> Prop} (dec:forall a, {P a} + {~ P a}).

  Fixpoint find_first  n : option nat
    := match n with
       | 0 => if dec 0%nat then Some 0%nat else None
       | S k => match find_first k with
               | Some x => Some x
               | None => if dec (S k) then Some (S k) else None
               end
       end.

  Lemma find_first_some n k : find_first n = Some k -> P k.
    induction n; simpl.
    - match_destr; congruence.
    - match_option.
      + intros; apply IHn; congruence.
      + match_destr; congruence.
  Qed.

  Lemma find_first_none n : find_first n = None -> forall k, (k <= n)%nat -> ~ P k.
    induction n; simpl.
    - match_destr; intros.
      apply Nat.le_0_r in H0.
      congruence.
    - match_option.
      match_destr.
      intros.
      apply Nat.le_succ_r in H0.
      destruct H0.
      + auto.
      + congruence.
  Qed.

  Lemma find_first_some_first n k : find_first n = Some k -> forall i, (i < k)%nat -> ~ P i.
    induction n; simpl.
    - match_destr; intros.
      invcs H.
      now apply Nat.nlt_0_r in H0.
    - match_option.
      + intros; apply IHn; congruence.
      + match_destr; intros.
        invcs H.
        apply (find_first_none n); trivial.
        now apply Nat.lt_succ_r.
  Qed.
  
End find.

Definition classic_min_of_sumbool (P: nat -> Prop) :
  { n : nat | P n /\ forall k, (k < n)%nat -> ~ P k} + {forall n, ~ P n}.
Proof.
  destruct (ClassicalDescription.excluded_middle_informative (exists n, P n /\ forall k, (k < n)%nat -> ~ P k)).
  - left.
    assert ( exists! n : nat, P n /\ (forall k : nat, (k < n)%nat -> ~ P k)).
    {
      destruct e as [n [Pn Pmin]].
      exists n.
      split; [auto| intros ?[??]].
      apply Nat.le_antisymm.
      - apply Nat.nlt_ge.
        intros ?.
        specialize (Pmin _ H1); tauto.
      - apply Nat.nlt_ge.
        intros ?.
        specialize (H0 _ H1); tauto.
    } 
    now apply constructive_definite_description in H.
  - right.
    intros k pk.
    case_eq (find_first (fun a => ClassicalDescription.excluded_middle_informative (P a)) k).
    + intros.
      apply n.
      exists n0.
      split.
      * eapply find_first_some; eauto.
      * apply (find_first_some_first _ _ _ H).
    + intros HH.
      eapply find_first_none in HH; eauto.
Qed.

Definition classic_min_of (P: nat -> Prop) : option nat
  := match classic_min_of_sumbool P with
     | inleft n => Some (proj1_sig n)
     | inright _ => None
     end.

Lemma classic_min_of_some P k : classic_min_of P = Some k -> P k.
Proof.
  unfold classic_min_of.
  match_destr.
  destruct s as [?[??]].
  now intros HH; invcs HH.
Qed.  

Lemma classic_min_of_some_first P k : classic_min_of P = Some k -> forall j, (j < k)%nat -> ~ P j.
Proof.
  unfold classic_min_of.
  match_destr.
  destruct s as [?[??]].
  now intros HH; invcs HH.
Qed.  

Lemma classic_min_of_none P : classic_min_of P = None -> forall k, ~ P k.
Proof.
  unfold classic_min_of.
  match_destr.
Qed.

Global Instance classic_min_of_proper :
  Proper (pointwise_relation _ iff ==> eq) classic_min_of.
Proof.
  intros ???.
  unfold classic_min_of.
  repeat match_destr.
  - destruct s as [?[??]].
    destruct s0 as [?[??]]; simpl.
    f_equal.
    apply antisymmetry.
    + apply Compare_dec.not_lt; intros HH.
      apply H in y0.
      specialize (n _ HH); tauto.
    + apply Compare_dec.not_lt; intros HH.
      apply H in x1.
      specialize (n0 _ HH); tauto.
  - destruct s as [?[??]].
    elim (n x0).
    now apply H.
  - destruct s as [?[??]].
    elim (n x0).
    now apply H.
Qed.

