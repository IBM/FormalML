Require Import Utils.

Require Import List.
Require Import Streams.
Require Import Equivalence.
Require Import Morphisms.

Local Open Scope equiv_scope.

Global Instance EqSt_equiv {A} : Equivalence (@EqSt A).
Proof.
  constructor.
  - intros ?; apply EqSt_reflex.
  - intros ??; apply sym_EqSt.
  - intros ??; apply trans_EqSt.
Qed.

Fixpoint ConsList {A:Type} (l:list A) (s:Stream A) : Stream A
  := match l with
     | nil => s
     | cons x xs => Cons x (ConsList xs s)
     end.

Global Instance ConsList_proper {A} : Proper (eq ==> @EqSt A ==> @EqSt A) (@ConsList A).
Proof.
  repeat red; intros; subst.
  induction y; simpl; trivial.
  constructor; simpl; trivial.
Qed.

Lemma ConsList_app {A:Type} (l1 l2:list A) (s:Stream A) :
  ConsList (l1++l2) s = ConsList l1 (ConsList l2 s).
Proof.
  induction l1; simpl; trivial.
  rewrite IHl1; trivial.
Qed.

Section Cutting.

  Context {A:Type}.

  Fixpoint firstn (n:nat) (l:Stream A) : list A :=
    match n with
      | 0 => nil
      | S n => match l with
                 | Cons a l => a::(firstn n l)
               end
    end.

  Global Instance firstn_proper : Proper (eq ==> @EqSt A ==> eq) firstn.
  Proof.
    repeat red; intros; subst.
    revert x0 y0 H0.
    induction y; simpl; trivial; intros x0 y0.
    inversion 1.
    destruct x0; destruct y0; simpl in *.
    f_equal; auto.
  Qed.

    Fixpoint skipn (n:nat)(s:Stream A) : Stream A :=
    match n with
      | 0 => s
      | S n => match s with
                 | Cons a s' => skipn n s'
               end
    end.

  Global Instance skipn_proper : Proper (eq ==> @EqSt A ==> @EqSt A) skipn.
  Proof.
    repeat red; intros; subst.
    revert x0 y0 H0.
    induction y; simpl; trivial; intros x0 y0.
    inversion 1.
    destruct x0; destruct y0; simpl in *.
    f_equal; auto.
  Qed.

  Lemma firstn_length n l : length (firstn n l) = n.
  Proof.
    revert l.
    induction n; simpl; trivial.
    destruct l; simpl.
    rewrite IHn.
    trivial.
  Qed.
  
  Lemma firstn_cons n a l: firstn (S n) (Streams.Cons a l) = cons a (firstn n l).
  Proof.
    reflexivity.
  Qed.
    
  Lemma firstn_O l: firstn 0 l = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma firstn_ConsList n (l:list A) (s:Stream A) :
    n < length l ->
    firstn n (ConsList l s) = List.firstn n l.
  Proof.
    revert n.
    induction l; simpl.
    - intros. inversion H.
    - intros.
      destruct n; simpl; trivial.
      rewrite IHl; auto with arith.
  Qed.
  
  Lemma firstn_skipn n s : ConsList (firstn n s) (skipn n s) = s.
  Proof.
    revert s.
    induction n; trivial; intros [s]; simpl.
    rewrite IHn; trivial.
  Qed.

  Lemma firstn_skipn_swap n1 n2 s : firstn n1 (skipn n2 s) = List.skipn n2 (firstn (n2+n1) s).
  Proof.
    revert n1 s.
    induction n2; simpl; trivial.
    intros n1 [s]; auto.
  Qed.
    
  Lemma firstn_firstn (s:Stream A) (i j : nat) :
    List.firstn i (firstn j s) = firstn (min i j) s.
  Proof.
    revert s j.
    induction i; simpl; trivial.
    intros [s]; simpl.
    destruct j; simpl; trivial.
    rewrite IHi.
    trivial.
  Qed.
  
  Lemma firstn_firstn_swap (s:Stream A) (i j : nat) :
    List.firstn i (firstn j s) = List.firstn j (firstn i s).
  Proof.
    repeat rewrite firstn_firstn.
    rewrite Min.min_comm.
    trivial.
  Qed.
  
End Cutting.

