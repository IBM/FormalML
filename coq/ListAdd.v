Require Import List.
Require Import RelationClasses.
Require Import Omega Lra Rbase.

Import ListNotations.
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

Section olist.
  
  Fixpoint listo_to_olist {a: Type} (l: list (option a)) : option (list a) :=
    match l with
    | nil => Some nil
    | Some x :: xs => match listo_to_olist xs with
                      | None => None
                      | Some xs => Some (x::xs)
                      end
    | None :: xs => None
    end.
  
  Lemma listo_to_olist_some {A:Type} (l:list (option A)) (l':list A) :
      listo_to_olist l = Some l' ->
      l = (map Some l').
    Proof.
      revert l'.
      induction l; simpl; intros l' eqq.
      - inversion eqq; subst; simpl; trivial.
      - destruct a; try discriminate.
        case_eq (listo_to_olist l)
        ; [intros ? eqq2 | intros eqq2]
        ; rewrite eqq2 in eqq
        ; try discriminate.
        inversion eqq; subst.
        rewrite (IHl l0); trivial. 
    Qed.

End olist.

Section Fold.
  Context {A B C: Type}.
  
  Lemma fold_left_map
        (f:A -> C -> A) (g:B->C) (l:list B) (init:A) :
    fold_left f (map g l) init = fold_left (fun a b => f a (g b)) l init.
  Proof.
    revert init.
    induction l; simpl; trivial.
  Qed.

  Lemma fold_left_ext
        (f g:A -> B -> A) (l:list B) (init:A) :
    (forall x y, f x y = g x y) ->
    fold_left f l init = fold_left g l init.
  Proof.
    intros eqq.
    revert init.
    induction l; simpl; trivial; intros.
    rewrite eqq, IHl.
    trivial.
  Qed.

  Lemma fold_right_map
        (f:C -> A -> A) (g:B->C) (l:list B) (init:A) :
    fold_right f init (map g l) = fold_right (fun a b => f (g a) b) init l.
  Proof.
    revert init.
    induction l; simpl; trivial; intros.
    rewrite IHl; trivial.
  Qed.

End Fold.

Lemma fold_right_plus_acc f acc l :
  fold_right (fun (a : nat) (b : R) => f a + b)%R acc l =
  (fold_right (fun (a : nat) (b : R) => f a + b)%R R0 l + acc)%R.
Proof.
  induction l; simpl.
  - lra.
  - rewrite IHl; lra.
Qed.

Section Seq.
  
  Lemma seq_shiftn {A:Type} (l:list A)  (n:nat) :
    seq n (length l) = map (fun x => x + n)%nat (seq 0 (length l)).
  Proof.
    induction n; simpl.
    - erewrite map_ext.
      + erewrite map_id; trivial.
      + intros; omega.
    - rewrite <- seq_shift.
      rewrite IHn.
      rewrite map_map.
      apply map_ext; intros.
      omega.
  Qed.

  Lemma list_as_nthseq_start {A:Type} (l:list A) (d:A) (c:nat) : l = map (fun n => nth (n-c) l d) (seq c%nat (length l)).
  Proof.
    induction l; simpl; trivial.
    rewrite <- seq_shift.
    rewrite map_map.
    simpl.
    replace (c-c)%nat with 0%nat by omega.
    rewrite IHl.
    f_equal.
    rewrite map_length.
    rewrite seq_length.
    apply map_ext_in; intros x inn.
    apply in_seq in inn.
    rewrite <- IHl.
    destruct c.
    - f_equal; omega.
    - assert (x-c > 0)%nat by omega.
      replace (x - S c)%nat with ((x - c) - 1)%nat by omega.
      destruct (x-c)%nat.
      + omega.
      + f_equal; omega.
  Qed.
  
  Lemma list_as_nthseq {A:Type} (l:list A) (d:A) : l = map (fun n => nth n l d) (seq 0%nat (length l)).
  Proof.
    rewrite (list_as_nthseq_start l d 0) at 1.
    apply map_ext; intros.
    f_equal; omega.
  Qed.

  Lemma seq_app s n m : seq s (n + m) = seq s n ++ seq (s+n) m.
  Proof.
    revert s.
    induction n; simpl; intros s.
    - f_equal; omega.
    - rewrite IHn.
      do 3 f_equal.
      omega.
  Qed.
  
  Lemma seq_Sn s n : seq s (S n) = seq s n ++ [(s+n)]%nat.
  Proof.
    replace (S n) with (n + 1)%nat by omega.
    rewrite seq_app.
    simpl; trivial.
  Qed.
  
End Seq.

Section fp.

  Lemma ForallOrdPairs_impl {A:Type} (R:A->A->Prop) (l:list A) (f:A->A) :
    ForallOrdPairs R l ->
    ForallOrdPairs (fun x y => R x y -> R (f x) (f y)) l ->
    ForallOrdPairs R (map f l).
  Proof.
    induction l; intros FP; inversion FP; clear FP; subst; intros FP; simpl.
    - constructor.
    - inversion FP; clear FP; subst.
      constructor.
      + rewrite Forall_forall in *.
        intros x inn.
        apply in_map_iff in inn.
        destruct inn as [xx [eqxx inxx]]; subst.
        auto.
      + intuition.
  Qed.

  Lemma ForallPairs_all {A:Type} (R:A->A->Prop) (l:list A) :
    (forall x1 x2, R x1 x2) -> ForallPairs R l.
  Proof.
    firstorder.
  Qed. 

End fp.
  