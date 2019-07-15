Require Import List.
Require Import RelationClasses.

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
    intros. eauto using in_dom_lookup, in_dom.
  Qed.

  Section lookup_eq.
      Definition lookup_equiv (l1 l2:list (A*B))
        := forall x, lookup l1 x = lookup l2 x.
      
  Global Instance lookup_equiv_equiv
    : Equivalence lookup_equiv.
  Proof.
    unfold lookup_equiv.
    constructor; red; intros.
    - trivial.
    - symmetry; auto.
    - rewrite H by trivial.
      eauto.
  Qed.

  End lookup_eq.
  Section lookup_on.


  Definition lookup_equiv_on 
             (dom:list A) (l1 l2:list (A*B))
    := forall x, In x dom -> lookup l1 x = lookup l2 x.

  Global Instance lookup_equiv_on_equiv dom
    : Equivalence (lookup_equiv_on dom).
  Proof.
    unfold lookup_equiv_on.
    constructor; red; intros.
    - trivial.
    - symmetry; auto.
    - rewrite H by trivial.
      eauto.
  Qed.

    Lemma lookup_equiv_on_dom_incl 
          (dom1 dom2:list A) (l1 l2:list (A*B))
      : incl dom2 dom1 ->
        lookup_equiv_on dom1 l1 l2 ->
        lookup_equiv_on dom2 l1 l2.
    Proof.
      unfold lookup_equiv_on; intuition.
    Qed.

    Lemma lookup_equiv_on_dom_app_f
          {dom1 dom2:list A} {l1 l2:list (A*B)}
      : lookup_equiv_on dom1 l1 l2 ->
        lookup_equiv_on dom2 l1 l2 -> 
        lookup_equiv_on (dom1++dom2) l1 l2.
    Proof.
      unfold lookup_equiv_on; intros.
      rewrite in_app_iff in *; intuition.
    Qed.
    
    Lemma lookup_equiv_on_dom_app 
          (dom1 dom2:list A) (l1 l2:list (A*B))
      : lookup_equiv_on (dom1++dom2) l1 l2 ->
        lookup_equiv_on dom1 l1 l2 
        /\ lookup_equiv_on dom2 l1 l2.
    Proof.
      unfold lookup_equiv_on; intuition.
    Qed.

    Lemma lookup_equiv_on_lookup_equiv
          (l1 l2 : list (A * B)) :
      lookup_equiv l1 l2 <-> (forall dom, lookup_equiv_on dom l1 l2).
    Proof.
      unfold lookup_equiv, lookup_equiv_on.
      split; intros.
      - intuition.
      - apply (H (x::nil)); simpl; eauto.
    Qed.
    
  End lookup_on.

End Assoc.