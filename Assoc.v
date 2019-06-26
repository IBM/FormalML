Require Import List.

Section Assoc.
  
  Context {A B:Type}.
  Context (dec:forall a a':A, {a=a'} + {a<>a'}).
  (* define lookup for assocation lists *)
  Fixpoint lookup l a : option B
    := match l with 
       | nil => None
       | (f',v')::os => if dec a f' then Some v' else lookup os a
       end.
  
  Definition domain (l:list (A*B)) := map (@fst A B) l.
  Definition codomain (l:list (A*B)) := map (@snd A B) l.

  Lemma in_dom : forall {l} {a b}, In (a,b) l -> In a (domain l).
    Proof.
      unfold domain; induction l; simpl; trivial.
      intros. destruct a; simpl in *; intuition.
      inversion H0; intuition.
      eauto.
    Qed.

  Lemma lookup_in : forall l {a:A} {b:B}, lookup l a = Some b -> In (a,b) l.
  Proof.
    induction l; simpl; intuition.
    - discriminate.
    - destruct (dec a a0).
      + inversion H; intuition congruence.
      + intuition.
  Qed.

  Lemma lookup_in_domain : forall l {a:A} {b:B}, lookup l a = Some b -> In a (domain l).
  Proof.
    induction l; simpl; intuition.
    - discriminate.
    - destruct (dec a a0); simpl.
      + inversion H; intuition congruence.
      + right; apply (IHl a b0); assumption.
  Qed.

  Lemma in_dom_lookup :  forall {l} {a:A}, In a (domain l) -> {v | lookup l a = Some v}.
    Proof.
      induction l; simpl; [tauto|]; intros.
      destruct a; simpl in *.
      destruct (dec a0 a); [eauto|].
      apply IHl.
      intuition congruence.
    Qed.


  Lemma in_lookup :  forall {l} {a:A} {b0:B}, In (a,b0) l -> {v | lookup l a = Some v}.
  Proof.
    Hint Resolve in_dom_lookup in_dom.
    intros. eauto.
  Qed.

End Assoc.