Require Import List.
Require Import RelationClasses.

Section incl.
  
  Lemma incl_app_iff {A:Type} (l m n : list A) :
    incl (l ++ m) n <-> incl l n /\ incl m n.
  Proof.
    unfold incl; intuition.
    rewrite in_app_iff in H.
    intuition.
  Qed.
  
  Global Instance incl_pre A : PreOrder (@incl A).
  Proof.
    unfold incl.
    constructor; red; intuition.
  Qed.
  Print incl.

  Lemma incl_dec {A} (dec:forall a b:A, {a = b} + {a <> b}) (l1 l2:list A) :
    {incl l1 l2} + {~ incl l1 l2}.
  Proof.
    unfold incl.
    induction l1.
    - left; inversion 1.
    - destruct IHl1.
      + destruct (in_dec dec a l2).
        * left; simpl; intros; intuition; congruence.
        * right; simpl;  intros inn; apply n; intuition.
      + right; simpl; intros inn; apply n; intuition.
  Defined.

  Lemma nincl_exists {A} (dec:forall a b:A, {a = b} + {a <> b}) (l1 l2:list A) :
      ~ incl l1 l2 -> {x | In x l1 /\ ~ In x l2}.
    Proof.
      unfold incl.
      induction l1; simpl.
      - intros H; elim H;  intuition.
      - intros.
        destruct (in_dec dec a l2).
        + destruct IHl1.
          * intros inn.
            apply H. intuition; subst; trivial.
          * exists x; intuition.
        + exists a; intuition.
    Qed.

End incl.