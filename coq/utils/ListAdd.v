Require Import List Permutation EquivDec.
Require Import RelationClasses Morphisms.
Require Import Lia Lra Rbase.
Require Import Relation_Definitions Sorted.

Require Import LibUtils BasicUtils.

Import ListNotations.

Section Map.

  Lemma removelast_map {A B : Type} (f:A->B) (l : list A) :
    removelast (map f l) = map f (removelast l).
  Proof.
    induction l; simpl; trivial.
    rewrite IHl.
    destruct l; simpl; trivial.
  Qed.

  Lemma tl_map {A B : Type} (f:A->B) (l : list A) :
    tl (map f l) = map f (tl l).
  Proof.
    destruct l; simpl; trivial.
  Qed.

  Lemma concat_map_swap_perm {A B C} (f:A->B->C) (l1:list A) (l2:list B) :
    Permutation (concat (map (fun x => map (fun y => f x y) l2) l1))
                (concat (map (fun x => map (fun y => f y x) l1) l2)) .
  Proof.
    revert l2.
    induction l1; simpl; intros l2.
    - induction l2; simpl; trivial.
    - rewrite IHl1.
      clear IHl1.
      induction l2; simpl; trivial.
      apply perm_skip.
      rewrite <- IHl2.
      repeat rewrite <- app_ass.
      apply Permutation_app; trivial.
      apply Permutation_app_swap.
  Qed.
  
  Lemma map_app_interleave_perm {A B} (l:list A) (fl:list (A->B)) :
    Permutation (concat (map (fun f => map (fun x => f x) l) fl)) (concat (map (fun x => map (fun f => f x) fl) l)).
  Proof.
    apply concat_map_swap_perm.
  Qed.

  Lemma map2_app_interleave_perm {A B} (l:list A) (f g:A->B) :
    Permutation (map f l ++ map g l) (concat (map (fun x => f x::g x::nil) l)).
  Proof.
    generalize (map_app_interleave_perm l (f::g::nil)); simpl; intros HH.
    rewrite <- HH.
    rewrite app_nil_r.
    reflexivity.
  Qed.

End Map.

Section Fold.
  Context {A B C: Type}.

  Lemma fold_right_map
        (f:C -> A -> A) (g:B->C) (l:list B) (init:A) :
    fold_right f init (map g l) = fold_right (fun a b => f (g a) b) init l.
  Proof.
    revert init.
    induction l; simpl; trivial; intros.
    rewrite IHl; trivial.
  Qed.

End Fold.

Lemma fold_right_assoc_abs {A} (f:A->A->A) (init:A) (l : list (list A))
      (assoc:forall x y z : A, f x (f y z) = f (f x y) z) 
      (abs:forall x, f init x = x) :
  fold_right f init (concat l) =
  fold_right f init (map (fold_right f init) l).
Proof.
  rewrite fold_right_map.
  induction l; simpl; trivial.
  rewrite fold_right_app.
  rewrite <- IHl.
  generalize (fold_right f init (concat l)); intros.
  induction a; simpl.
  - auto.
  - rewrite IHa.
    generalize (fold_right f init a1); intros.
    now rewrite assoc.
Qed.

Lemma fold_right_plus_concat (l : list (list R)) :
  fold_right Rplus R0 (concat l) =
  fold_right Rplus R0 (map (fold_right Rplus R0) l).
Proof.
  apply fold_right_assoc_abs; intros; lra.
Qed.

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
      + intros; unfold id; lia.
    - rewrite <- seq_shift.
      rewrite IHn.
      rewrite map_map.
      apply map_ext; intros.
      lia.
  Qed.

  Lemma list_as_nthseq_start {A:Type} (l:list A) (d:A) (c:nat) : l = map (fun n => nth (n-c) l d) (seq c%nat (length l)).
  Proof.
    induction l; simpl; trivial.
    rewrite <- seq_shift.
    rewrite map_map.
    simpl.
    replace (c-c)%nat with 0%nat by lia.
    rewrite IHl.
    f_equal.
    rewrite map_length.
    rewrite seq_length.
    apply map_ext_in; intros x inn.
    apply in_seq in inn.
    rewrite <- IHl.
    destruct c.
    - f_equal; lia.
    - assert (x-c > 0)%nat by lia.
      replace (x - S c)%nat with ((x - c) - 1)%nat by lia.
      destruct (x-c)%nat.
      + lia.
      + f_equal; lia.
  Qed.
  
  Lemma list_as_nthseq {A:Type} (l:list A) (d:A) : l = map (fun n => nth n l d) (seq 0%nat (length l)).
  Proof.
    rewrite (list_as_nthseq_start l d 0) at 1.
    apply map_ext; intros.
    f_equal; lia.
  Qed.

  Lemma seq_Sn s n : seq s (S n) = seq s n ++ [(s+n)]%nat.
  Proof.
    replace (S n) with (n + 1)%nat by lia.
    rewrite seq_plus.
    simpl; trivial.
  Qed.

  Lemma tl_seq n : tl (seq 0 n) = seq 1 (n-1).
  Proof.
    destruct n; simpl; trivial.
    rewrite Nat.sub_0_r.
    trivial.
  Qed.

  Lemma removelast_seq (n:nat) : removelast (seq 0 n) = seq 0 (n-1).
  Proof.
    induction n; simpl; trivial.
    rewrite Nat.sub_0_r.
    rewrite <- seq_shift.
    rewrite removelast_map.
    rewrite IHn.
    repeat rewrite seq_shift.
    destruct n; simpl; trivial.
    rewrite Nat.sub_0_r.
    trivial.
  Qed.

  Lemma seq_shiftn_map start len : seq start len = map (plus start) (seq 0 len).
  Proof.
    induction start; simpl.
    - rewrite map_id; trivial.
    - rewrite <- seq_shift.
      rewrite IHstart.
      rewrite map_map.
      trivial.
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

Lemma nth_tl {A} idx (l:list A) d : nth idx (tl l) d = nth (S idx) l d.
Proof.
  destruct l; simpl; trivial.
  destruct idx; trivial.
Qed.

Lemma nth_removelast_in {A} idx (l:list A) d :
  idx < pred (length l) ->
  nth idx (removelast l) d = nth idx l d.
Proof.
  revert idx.
  induction l; simpl; trivial; intros idx inn.
  destruct l.
  - destruct idx; simpl in *; lia.
  - simpl in *.
    destruct idx; trivial.
    rewrite IHl by lia.
    trivial.
Qed.

Lemma nth_last {A} (l:list A) d: nth (pred (length l)) l d = last l d.
Proof.
  induction l; simpl; trivial.
  destruct l; simpl in *; trivial.
Qed.

Lemma nth_hd {A} (l:list A) d: nth 0 l d = hd d l.
Proof.
  destruct l; simpl in *; trivial.
Qed.

Lemma hd_app {A} (l1 l2:list A) d : l1 <> nil -> hd d (l1 ++ l2) = hd d l1.
Proof.
  induction l1; simpl; congruence.
Qed.

Lemma last_rev {A} (l:list A) d : last l d = hd d (rev l).
Proof.
  induction l; trivial.
  simpl rev.
  destruct l; trivial.
  rewrite hd_app; trivial.
  intros eqq.
  apply (f_equal (@length A)) in eqq.
  simpl in eqq.
  rewrite app_length in eqq.
  simpl in eqq.
  lia.
Qed.

Lemma last_app {A} (l1 l2:list A) d : l2 <> nil -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros.
  repeat rewrite last_rev.
  rewrite rev_app_distr.
  rewrite hd_app; trivial.
  intro eqq; apply H.
  apply (f_equal (@rev A)) in eqq.
  rewrite rev_involutive in eqq.
  trivial.
Qed.

Lemma last_cons {A} (x:A) l y : last (x::l) y = last l x.
Proof.
  revert y.
  induction l; simpl; trivial; intros.
  destruct l; trivial.
  simpl in *.
  apply IHl.
Qed.

Lemma seq_last s n d :
  (n > 0)%nat ->
  last (seq s n) d = (s+n-1)%nat.
Proof.
  intros.
  destruct n.
  - simpl; lia.
  - rewrite seq_Sn.
    rewrite last_app by congruence.
    simpl.
    lia.
Qed.

Lemma last_map {A B} (f:A->B) (l:list A) d : last (map f l) (f d) = f (last l d).
Proof.
  induction l; simpl; trivial.
  destruct l; simpl; trivial.
Qed.

Lemma map_nth_in {A B} (f:A->B) l d1 n d2 :
  (n < length l)%nat ->
  nth n (map f l) d1 = f (nth n l d2).
Proof.
  revert n.
  induction l; simpl.
  - destruct n; lia.
  - destruct n; trivial.
    intros; eauto.
    rewrite IHl; trivial; lia.
Qed.

Lemma map_nth_in_exists {A B} (f:A->B) l d1 n :
  (n < length l)%nat ->
  exists d2,
    nth n (map f l) d1 = f (nth n l d2).
Proof.
  revert n.
  induction l; simpl.
  - destruct n; lia.
  - destruct n; trivial.
    + intros; eauto.
    + intros.
      destruct (IHl n).
      * lia.
      * rewrite H0.
        eauto.
Qed.

Lemma nth_in_default {A} (l:list A) d1 d2 n :
  (n < length l)%nat ->
  nth n l d1 = nth n l d2.
Proof.
  revert n.
  induction l; simpl.
  - destruct n; lia.
  - destruct n; trivial.
    + intros; eauto.
      rewrite (IHl n); trivial.
      lia.
Qed.

Lemma Forall_app_iff {A} {P:A->Prop} {l1 l2} :
  Forall P (l1 ++ l2) <->
  Forall P l1 /\ Forall P l2.
Proof.
  repeat rewrite Forall_forall.
  intuition.
  apply in_app_iff in H.
  intuition.
Qed.

Lemma StronglySorted_app_inv {A} {R:relation A} {l1 l2} :
  StronglySorted R (l1 ++ l2) ->
  StronglySorted R l1 /\ StronglySorted R l2.
Proof.
  Hint Constructors StronglySorted : list.
  revert l2.
  induction l1; intros l2 ss; simpl in *.
  - simpl in *; split; trivial with list.
  - inversion ss; subst; clear ss.
    destruct (IHl1 _ H1).
    split; trivial.
    constructor; trivial.
    apply Forall_app_iff in H2.
    tauto.
Qed.

Lemma StronglySorted_sub {A} (R1 R2:relation A) :
  subrelation R1 R2 ->
  forall l, StronglySorted R1 l -> StronglySorted R2 l.
Proof.
  Hint Constructors StronglySorted : list.
  intros sub.
  induction l; simpl; intros ssl; trivial with list.
  inversion ssl; clear ssl; subst.
  simpl in *.
  constructor.
  - apply IHl; intuition.
  - rewrite Forall_forall in *.
    eauto.
Qed.

Lemma StronglySorted_map_in {A B} (R1:relation A) (R2:relation B) (f:A->B) l :
  (forall x y, In x l /\ In y l -> R1 x y -> R2 (f x) (f y)) ->
  StronglySorted R1 l -> StronglySorted R2 (map f l).
Proof.
  Hint Constructors StronglySorted : list.
  intros prop.
  induction l; simpl; intros ssl; trivial with list.
  inversion ssl; clear ssl; subst.
  simpl in *.
  constructor.
  - apply IHl; intuition.
  - rewrite Forall_forall in *.
    intros x inn.
    apply in_map_iff in inn.
    destruct inn as [a' [eqq inn]].
    subst; auto.
Qed.

Lemma StronglySorted_map {A B} (R1:relation A) (R2:relation B) (f:A->B) :
  Proper (R1 ==> R2) f ->
  forall l,
    StronglySorted R1 l -> StronglySorted R2 (map f l).
Proof.
  intros.
  eapply StronglySorted_map_in; eauto.
Qed.

Lemma StronglySorted_compose {A B} R (f:A->B) (l:list A) :
  StronglySorted R (map f l) <->
  StronglySorted (fun x y => R (f x) (f y)) l.
Proof.
  induction l; simpl.
  - intuition.
  - split; inversion 1; subst; constructor; intuition.
    + now rewrite Forall_map in H3.
    + now rewrite Forall_map.
Qed.

Lemma StronglySorted_break {A} R (l:list A) x :
  StronglySorted R l ->
  In x l ->
  exists b c, l = b++x::c /\ Forall (fun y => R y x) b /\ Forall (R x) c.
Proof.
  induction l; simpl; intros ss inn; [tauto | ].
  invcs ss.
  destruct inn.
  - subst.
    exists nil, l.
    simpl.
    intuition.
  - destruct IHl as [b [c [p1 [p2 p3]]]]; trivial.
    subst.
    exists (a::b), c.
    simpl; intuition.
    constructor; trivial.
    rewrite Forall_forall in H2.
    specialize (H2 x).
    rewrite in_app_iff in H2; simpl in H2.
    eauto.
Qed.

Lemma StronglySorted_nth_lt {A} R (l:list A) idx1 idx2 d1 d2 :
  StronglySorted R l ->
  (idx2 < length l)%nat ->
  (idx1 < idx2)%nat ->
  R (nth idx1 l d1) (nth idx2 l d2).
Proof.
  intros.
  destruct (@nth_split _ idx1 l d1)
           as [l1 [l2 [leqq l1len]]]
  ; [ lia | ].
  rewrite leqq in H.
  apply StronglySorted_app_inv in H.
  destruct H as [ _ ssl2].
  inversion ssl2; clear ssl2; subst.
  rewrite leqq in *.
  rewrite app_length in H0.
  simpl in H0.
  revert H4.
  generalize (nth (length l1) l d1).
  clear l leqq.
  intros a Fa.
  rewrite Forall_forall in Fa.
  apply Fa.
  rewrite app_nth2 by lia.
  simpl.
  case_eq (idx2 - length l1); try lia.
  intros.
  apply nth_In.
  lia.
Qed.

Lemma StronglySorted_nth_le {A} R (l:list A) idx1 idx2 d1 d2 :
  reflexive _ R ->
  StronglySorted R l ->
  (idx2 < length l)%nat ->
  (idx1 <= idx2)%nat ->
  R (nth idx1 l d1) (nth idx2 l d2).
Proof.
  intros refl ?? leq.
  destruct leq.
  - erewrite nth_in_default; try apply refl.
    trivial.
  - apply StronglySorted_nth_lt; trivial.
    lia.
Qed.

Section bucket.

  Context {A:Type} {R:relation A} (R_dec : forall x y, {R x y} + {~ R x y}).

  Fixpoint find_bucket (needle:A) (haystack:list A)
    := match haystack with
       | x::((y::_) as more) => if R_dec x needle
                                then if R_dec needle y
                                     then Some (x,y)
                                     else find_bucket needle more
                                else None
       | _ => None
       end.
  
  Lemma find_bucket_break {needle l a1 a2}:
    find_bucket needle l = Some (a1, a2) ->
    exists l1 l2,
      l = l1 ++ [a1; a2] ++ l2.
  Proof.
    induction l; simpl; try discriminate.
    destruct l; try discriminate.
    destruct (R_dec a needle); try discriminate.
    destruct (R_dec needle a0).
    - inversion 1; subst.
      exists nil, l.
      reflexivity.
    - intros HH.
      destruct (IHl HH) as [l1 [l2 eqq]].
      rewrite eqq.
      exists (a::l1), l2.
      reflexivity.
  Qed.

  Lemma middle_find_bucket needle l1 l2 a1 a2:
    transitive _ R ->
    antisymmetric _ R ->
    StronglySorted R (l1++[a1]) ->
    R a1 needle ->
    R needle a2 ->
    ~ R needle a1 ->
    find_bucket needle (l1 ++ a1::a2::l2) = Some (a1, a2).
  Proof.
    intros trans antisymm.
    intros sorted r1 r2 nr1.
    revert sorted.
    induction l1; intros sorted.
    - simpl.
      destruct (R_dec a1 needle); [ | tauto].
      destruct (R_dec needle a2); [ | tauto].
      trivial.
    - simpl in *.
      inversion sorted; clear sorted; subst.
      specialize (IHl1 H1).
      rewrite IHl1; trivial.
      destruct (R_dec a needle).
      + destruct l1; simpl.
        * destruct (R_dec needle a1); tauto.
        * destruct (R_dec needle a0); trivial.
          elim nr1.
          apply (trans _ a0); trivial.
          inversion H1; clear H1; subst.
          rewrite Forall_forall in H4.
          apply H4.
          rewrite in_app_iff.
          simpl; tauto.
      + rewrite Forall_forall in H2.
        elim n.
        apply (trans _ a1); trivial.
        apply H2.
        rewrite in_app_iff.
        simpl; tauto.
  Qed.
  
  Lemma find_bucket_nth_finds needle l idx d1 d2:
    transitive _ R ->
    antisymmetric _ R ->
    StronglySorted R l ->
    S idx < length l ->
    R (nth idx l d1) needle ->
    R needle (nth (S idx) l d2) ->
    ~ R needle (nth idx l d1) ->
    find_bucket needle l = Some (nth idx l d1, nth (S idx) l d2).
  Proof.
    intros trans antisymm ss idx_bound.
    assert (idx_bound':idx < length l) by lia.
    destruct (nth_split l d1 idx_bound') as [l1 [l2 [eqq leneq]]].
    revert eqq.
    generalize (nth idx l d1); intros a1.
    intros eqq r1 r2 nr1.
    subst.
    rewrite app_nth2 in * by lia.
    replace ((S (length l1) - length l1)) with 1 in * by lia.
    rewrite app_length in idx_bound.
    simpl in *.
    destruct l2; simpl in *; [ lia | ].
    apply middle_find_bucket; trivial.
    replace (l1 ++ a1 :: a :: l2) with ((l1 ++ a1::nil) ++ (a :: l2)) in ss.
    - apply StronglySorted_app_inv in ss.
      tauto.
    - rewrite app_ass; simpl; trivial.
  Qed.

  Lemma find_bucket_needle_in needle l a1 a2:
    find_bucket needle l = Some (a1, a2) ->
    R a1 needle /\ R needle a2.
  Proof.
    induction l; simpl; try discriminate.
    destruct l; try discriminate.
    destruct (R_dec a needle); try discriminate.
    destruct (R_dec needle a0).
    - inversion 1; subst.
      tauto.
    - intuition.
  Qed.

  Lemma find_bucket_bucket_in needle l a1 a2 d1 d2:
    reflexive _ R ->
    StronglySorted R l ->
    find_bucket needle l = Some (a1, a2) ->
    R (hd d1 l) a1 /\ R a2 (last l d2).
  Proof.
    intros refl ssl eqq1.
    destruct (find_bucket_break eqq1)
      as [l1 [l2 eqq2]].
    replace (l1 ++ [a1; a2] ++ l2) with ((l1 ++ a1::nil) ++ (a2::l2)) in eqq2.
    - subst.
      apply StronglySorted_app_inv in ssl.
      destruct ssl as [ssl1 ssl2].
      split.
      + destruct l1; simpl.
        * apply refl.
        * inversion ssl1; subst.
          rewrite Forall_forall in H2.
          apply H2.
          rewrite in_app_iff; simpl; tauto.
      + inversion ssl2; clear ssl2; subst.
        rewrite last_app by congruence.
        rewrite Forall_forall in H2.
        simpl.
        destruct l2.
        * apply refl.
        * apply H2.
          clear.
          { revert a.
            induction l2.
            - simpl; tauto.
            - simpl in *.
              eauto.
          } 
    - rewrite app_ass; simpl; reflexivity.
  Qed.

  Lemma find_bucket_bounded_le_exists a b l (needle:A) :
    (forall x y, R x y \/ R y x) ->
    R a needle ->
    R needle b ->
    exists lower upper,
      find_bucket needle (a::l++[b]) = Some (lower, upper).
  Proof.
    intros total r1 r2.
    simpl.
    destruct (R_dec a needle); [ | tauto].
    induction l; simpl.
    - destruct (R_dec needle b); [ | tauto].
      eauto.
    - destruct (IHl) as [lower [upper eqq]].
      destruct (R_dec needle a0).
      + eauto.
      + clear IHl r.
        { destruct (R_dec a0 needle).
          - destruct l; simpl in *.
            + destruct (R_dec needle b); simpl; eauto.
            + destruct (R_dec needle a1); eauto.
          - destruct (total needle a0); tauto.
        } 
  Qed.

End bucket.

Lemma StronglySorted_seq s n : StronglySorted lt (seq s n).
Proof.
  revert s.
  induction n; intros s; simpl.
  - constructor.
  - constructor; trivial.
    rewrite Forall_forall; intros.
    apply in_seq in H.
    lia.
Qed.

Lemma length_S_tl {A : Type} (l : list A) :
  l <> nil ->
  length l = S (length (tl l)).
Proof.
  intros.
  destruct l; simpl; congruence.
Qed.

Lemma tl_length {A : Type} (l : list A) :
  length (tl l) = pred (length l).
Proof.
  intros.
  destruct l; simpl; congruence.
Qed.

Lemma removelast_length {A : Type} (l : list A) :
  length (removelast l) = pred (length l).
Proof.
  induction l; trivial.
  destruct l; trivial.
  simpl in *.
  rewrite IHl; trivial.
Qed.

Section combining.

Lemma combine_nth_in {A B : Type} (l : list A) (l' : list B) (n : nat) (x : A) (y : B) :
  n < min (length l) (length l') ->
  nth n (combine l l') (x, y) = (nth n l x, nth n l' y).
Proof.
  revert l' n.
  induction l; simpl; intros l' n nlt.
  - lia.
  - destruct l'; simpl in *.
    + lia.
    + destruct n; simpl; trivial.
      apply IHl.
      lia.
Qed.

Lemma combine_map {A B C D:Type} (f:A->C) (g:B->D) (l1:list A) (l2:list B) :
  combine (map f l1) (map g l2) = map (fun '(x,y) => (f x, g y)) (combine l1 l2).
Proof.
  revert l2.
  induction l1; intros l2; simpl; trivial.
  destruct l2; simpl; trivial.
  f_equal.
  auto.
Qed.

  Lemma combine_self {A:Type} (l:list A) :
    combine l l = map (fun x => (x,x)) l.
  Proof.
    induction l; simpl; trivial.
    f_equal; trivial.
  Qed.

  Lemma combine_nil_l {A B} (l:list B) : combine (@nil A) l = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma combine_nil_r {A B} (l:list A) : combine l (@nil B) = nil.
  Proof.
    destruct l; trivial.
  Qed.

  Lemma combine_swap {A B} (l1:list A) (l2:list B) : combine l1 l2 = map (fun xy => (snd xy, fst xy)) (combine l2 l1).
  Proof.
    revert l2; induction l1; simpl; intros
    ; destruct l2; simpl; trivial.
    rewrite IHl1; trivial.
  Qed.

  Lemma combine_domain_eq {A B} (x:list A) (y:list B) :
    length x = length y -> domain (combine x y) = x.
  Proof.
    revert y.
    induction x; destruct y; simpl in *; intros
    ; try easy.
    inversion H.
    rewrite IHx; trivial.
  Qed.    

  Lemma list_prod_map {A B C D:Type} (f:A->C) (g:B->D) (l1:list A) (l2:list B) :
    list_prod (map f l1) (map g l2) = map (fun '(x,y) => (f x, g y)) (list_prod l1 l2).
  Proof.
    revert l2.
    induction l1; intros l2; simpl; trivial.
    rewrite map_app.
    repeat rewrite map_map.
    rewrite IHl1.
    trivial.
  Qed.

  Lemma list_prod_nil_l {A B} (l:list B) : list_prod (@nil A) l = nil.
  Proof.
    reflexivity.
  Qed.

  Lemma list_prod_nil_r {A B} (l:list A) : list_prod l (@nil B) = nil.
  Proof.
    induction l; trivial.
  Qed.

  Lemma list_prod_cons2_pred {A B} (l1:list A) a (l2:list B) :
    Permutation (list_prod l1 (a :: l2)) (map (fun x : A => (x, a)) l1 ++ list_prod l1 l2).
  Proof.
    revert a l2.
    induction l1; simpl; intros.
    - reflexivity.
    - rewrite IHl1.
      apply Permutation_cons; trivial.
      repeat rewrite <- app_ass.
      apply Permutation_app; [ | reflexivity ].
      rewrite Permutation_app_swap.
      reflexivity.
  Qed.

  Lemma list_prod_swap {A B} (l1:list A) (l2:list B) : Permutation (list_prod l1 l2) (map (fun xy => (snd xy, fst xy)) (list_prod l2 l1)).
  Proof.
    revert l1; induction l2; simpl; intros.
    - rewrite list_prod_nil_r; simpl.
      reflexivity.
    - rewrite map_app.
      rewrite <- IHl2.
      rewrite map_map; simpl.
      apply list_prod_cons2_pred.
  Qed.

  Instance list_prod_perm_proper1 {A B} : Proper ((@Permutation A) ==> eq ==> (@Permutation (A*B))) (@list_prod A B).
  Proof.
    intros l1 l1' perm1 l2' l2 eqq; subst.
    revert l1 l1' perm1.
    apply Permutation_ind_bis; intros.
    - reflexivity.
    - simpl.
      rewrite H0; reflexivity.
    - simpl.
      rewrite H0.
      repeat rewrite <- app_ass.
      apply Permutation_app; [ | reflexivity ].
      rewrite Permutation_app_swap.
      reflexivity.
    - etransitivity; eauto.
  Qed.

  Global Instance list_prod_perm_proper {A B} : Proper ((@Permutation A) ==> (@Permutation B) ==> (@Permutation (A*B))) (@list_prod A B).
  Proof.
    intros l1 l1' perm1 l2 l2' perm2.
    transitivity (list_prod l1' l2).
    - apply list_prod_perm_proper1; trivial.
    - rewrite (list_prod_swap l1' l2).
      rewrite (list_prod_swap l1' l2').
      apply Permutation_map.
      apply list_prod_perm_proper1; trivial.
  Qed.

  Lemma combine_incl_list_prod {A B} (l1:list A) (l2:list B) : incl (combine l1 l2) (list_prod l1 l2).
  Proof.
    intros [x y] inn.
    apply in_prod_iff.
    split.
    - eapply in_combine_l; eauto.
    - eapply in_combine_r; eauto.
  Qed.

End combining.

Definition adjacent_pairs {A:Type} (l:list A) := (combine l (tl l)).

Definition adjacent_pairs_alt {A:Type} (l:list A) := (combine (removelast l) (tl l)).

Lemma adjacent_pairs_alt_eq {A:Type} (l:list A) :
  adjacent_pairs l = adjacent_pairs_alt l.
Proof.
  unfold adjacent_pairs, adjacent_pairs_alt.
  induction l; simpl; trivial.
  destruct l; simpl in *; trivial.
  f_equal.
  trivial.
Qed.

Lemma adjacent_pairs_length {A:Type} (l:list A) : length (adjacent_pairs l) = pred (length l).
Proof.
  unfold adjacent_pairs.
  rewrite combine_length.
  rewrite tl_length.
  rewrite Nat.min_r; trivial.
  lia.
Qed.

Lemma adjacent_pairs_nth_in {A:Type} n (l:list A) d1 d2 :
  S n < length l ->
  nth n (adjacent_pairs l) (d1,d2) = (nth n l d1, nth (S n) l d2).
Proof.
  intros.
  unfold adjacent_pairs.
  rewrite combine_nth_in.
  - rewrite nth_tl; trivial.
  - rewrite tl_length.
    rewrite Nat.min_r; lia.
Qed.

Lemma adjacent_pairs_map {A B:Type} (f:A->B) (l:list A) :
  adjacent_pairs (map f l) = map (fun '(x,y) => (f x, f y)) (adjacent_pairs l).
Proof.
  unfold adjacent_pairs.
  rewrite tl_map, combine_map.
  trivial.
Qed.

Lemma adjacent_pairs_seq s n :
  adjacent_pairs (seq s n) = map (fun i => (i, S i)) (seq s (pred n)).
Proof.
  unfold adjacent_pairs.
  revert s.
  induction n; simpl; intros s; trivial.
  destruct n; simpl; trivial.
  f_equal.
  apply IHn.
Qed.

Section folds_with_history.

  
  (* returns a list of all the partial folds *)
  Definition fold_left_with_history_aux {A B : Type} (f:A -> B -> A) (l:list B) (init:A) (acc:list A) : list A
    := rev (let '(x,y) := (fold_left (fun '(a,hs) b => (f a b, a::hs)) l (init, acc)) in
            x::y).

  Definition fold_left_with_history {A B : Type} (f:A -> B -> A) (l:list B) (init:A) : list A
    :=  fold_left_with_history_aux f l init nil.

  Lemma fold_left_with_history_aux_len {A B : Type} (f:A -> B -> A) (l:list B) (init:A) (acc:list A) :
    (List.length (fold_left_with_history_aux f l init acc) = S (length l) + length acc)%nat.
  Proof.
    unfold fold_left_with_history_aux.
    revert init acc.
    induction l; simpl; intros init x.
    + rewrite app_length, rev_length; simpl.
      lia.
    + rewrite IHl; simpl.
      lia.
  Qed.
  
  Lemma fold_left_with_history_len {A B : Type} (f:A -> B -> A) (l:list B) (init:A) :
    List.length (fold_left_with_history f l init) = S (length l).
  Proof.
    unfold fold_left_with_history.
    rewrite fold_left_with_history_aux_len; simpl.
    lia.
  Qed.

  Fixpoint fold_left_partial_with_history_aux {A B : Type} (f : A -> B -> option A) (l:list B) (acc:A*list A) : list A + list A
    := match l with
       | [] => inl (rev (fst acc :: snd acc))
       | b :: t =>
         match f (fst acc) b with
         | None => inr (rev (fst acc :: snd acc))
         | Some a' => 
           fold_left_partial_with_history_aux f t (a', fst acc::snd acc)
         end
       end.

  Definition fold_left_partial_with_history {A B : Type} (f : A -> B -> option A) (l:list B) (init:A) : list A + list A
    := fold_left_partial_with_history_aux f l (init,nil).
  
  Lemma fold_left_partial_with_history_aux_ok {A B : Type} (f : A -> B -> option A) (l:list B) (init:A) (acc:list A) l' :
    fold_left_partial_with_history_aux f l (init,acc) = inl l' ->
    (List.length l' = S (length l) + length acc)%nat.
  Proof.
    revert init acc l'.
    induction l; simpl; intros init acc l' eqq.
    - invcs eqq.
      rewrite app_length, rev_length; simpl.
      lia.
    - match_destr_in eqq.
      rewrite (IHl _ _ _ eqq); simpl.
      lia.
  Qed.
  
  Lemma fold_left_partial_with_history_ok {A B : Type} (f : A -> B -> option A) (l:list B) (init:A) l' :
    fold_left_partial_with_history f l init = inl l' ->
    List.length l' = S (length l).
  Proof.
    unfold fold_left_partial_with_history; intros eqq.
    apply fold_left_partial_with_history_aux_ok in eqq.
    simpl in eqq.
    lia.
  Qed.

  Lemma fold_left_partial_with_history_aux_err {A B : Type} (f : A -> B -> option A) (l:list B) (init:A) (acc:list A) l' :
    fold_left_partial_with_history_aux f l (init,acc) = inr l' ->
    (List.length l' < S (length l) + length acc)%nat.
  Proof.
    revert init acc l'.
    induction l; simpl; intros init acc l' eqq.
    - invcs eqq.
    - match_destr_in eqq.
      + specialize (IHl _ _ _ eqq); simpl in IHl.
        lia.
      + invcs eqq.
        rewrite app_length, rev_length; simpl.
        lia.
  Qed.

  Lemma fold_left_partial_with_history_aux_total {A B : Type}
        (f : A -> B -> A) (l:list B) (init:A) (acc:list A) :
    fold_left_partial_with_history_aux (fun a b => Some (f a b)) l (init,acc) =
    inl (fold_left_with_history_aux f l init acc).
  Proof.
    unfold fold_left_with_history_aux.
    revert init acc.
    induction l; simpl; intros init acc; trivial.
  Qed.


  Lemma fold_left_partial_with_history_total {A B : Type} (f : A -> B -> A) (l:list B) (init:A) :
    fold_left_partial_with_history (fun a b => Some (f a b)) l init = inl (fold_left_with_history f l init).
  Proof.
    apply fold_left_partial_with_history_aux_total.
  Qed.
End folds_with_history.

Lemma nodup_not_nil (T : Type) (l : list T) (dec:forall (x y:T), {x = y} + {x <> y}) :
  l <> nil <-> nodup dec l <> nil.
Proof.
  intros.
  destruct l; intros; simpl.
  - intuition.
  - intuition try congruence.
    match_destr_in H0.
    apply (nodup_In dec) in i.
    rewrite H0 in i.
    simpl in i; trivial.
Qed.

Lemma map_in_inj_strong {A B} (f:A->B) a (l:list A) :
  (forall a b, In (f a) (map f l) -> In (f b) (map f l) -> f a = f b -> a = b) ->
  In (f a) (map f l) -> In a l.
Proof.
  intros inj HH.
  apply in_map_iff in HH.
  destruct HH as [x [eqqx inx]].
  rewrite (inj a x); trivial.
  - rewrite <- eqqx.
    now apply in_map.
  - now apply in_map.
  - congruence.
Qed.

Lemma nodup_map_inj {A B} decA decB (f:A->B) (l:list A) :
  (forall a b, In (f a) (map f l) -> In (f b) (map f l) -> f a = f b -> a = b) ->
  nodup decB (map f l) = map f (nodup decA l).
Proof.
  intros inj.
  induction l; simpl; trivial.
  assert (forall a b : A, In (f a) (map f l) -> In (f b) (map f l) -> f a = f b -> a = b).
  { simpl in inj.
    intuition.
  } 
  rewrite IHl by trivial.
  match_destr; match_destr.
  - apply map_in_inj_strong in i; trivial.
    congruence.
  - elim n.
    now apply in_map.
Qed.

Lemma list_prod_concat {A B} (l1:list A) (l2:list B) : list_prod l1 l2 = concat (map (fun x => map (fun y => (x, y)) l2) l1).
Proof.
  induction l1; simpl; trivial.
  now rewrite IHl1.
Qed.

Lemma nodup_const_map {A} (c r:A) dec (l : list A) :
  [c] = nodup dec (map (fun _  => c) (r :: l)).
Proof.
  induction l; simpl; trivial.
  rewrite IHl.
  match_destr.
  simpl.
  intuition.
Qed.

Lemma concat_NoDup {A} (l:list (list A)) : NoDup (concat l) -> Forall (@NoDup A) l.
Proof.
  induction l; simpl; intros nd.
  - constructor.
  - constructor.
    + eapply NoDup_app_inv; eauto.
    + apply IHl. eapply NoDup_app_inv2; eauto.
Qed.

Lemma nodup_app2_incl {A} decA (l1 l2:list A) :
  incl l1 l2 ->
  nodup decA (l1 ++ l2) = nodup decA l2.
Proof.
  unfold incl; intros inn.
  induction l1; simpl; trivial; simpl in *.
  match_destr.
  - eauto.
  - elim n.
    apply in_app_iff.
    eauto.
Qed.

Lemma nodup_app_distr {A} decA (l1 l2:list A) :
  disjoint l1 l2 ->
  nodup decA (l1 ++ l2) = nodup decA l1 ++ nodup decA l2.
Proof.
  unfold disjoint.
  intros disj.
  induction l1; simpl; trivial.
  rewrite IHl1 by firstorder.
  destruct (in_dec decA a l1).
  - match_destr.
    elim n.
    apply in_app_iff; auto.
  - match_destr.
    apply in_app_iff in i.
    elim (disj a); simpl; intuition.
Qed.

Lemma list_prod_nodup {A B} decA decB decAB (l1:list A) (l2:list B):
  nodup decAB (list_prod l1 l2) = list_prod (nodup decA l1) (nodup decB l2).
Proof.
  repeat rewrite list_prod_concat.
  revert l2.
  induction l1; simpl; trivial.
  intros l2.
  match_destr.
  - rewrite <- IHl1.
    apply nodup_app2_incl.
    intros x inn.
    apply concat_In.
    eexists.
    split; try eassumption.
    apply in_map_iff.
    eauto.
  - simpl.
    rewrite <- IHl1.
    rewrite nodup_app_distr.
    + f_equal.
      induction l2; simpl; trivial.
      rewrite IHl2.
      match_destr.
      * apply in_map_iff in i.
        destruct i as [x [eqq xin]].
        invcs eqq.
        match_destr.
        congruence.
      * match_destr.
        elim n0.
        apply in_map_iff.
        eauto.
    + unfold disjoint.
      intros [x y] inn HH.
      apply concat_In in HH.
      destruct HH as [xx [xxin xinn]].
      apply in_map_iff in xxin.
      destruct xxin as [xxx [? xxxin]]; subst.
      apply in_map_iff in inn.
      destruct inn as [? [eqq ?]].
      invcs eqq; subst.
      apply in_map_iff in xinn.
      destruct xinn as [? [eqq ?]].
      invcs eqq.
      congruence.
Qed.

Lemma nodup_map_nodup {A B} decA decB (f:A->B) (l:list A) :
  nodup decB (map f (nodup decA l)) = nodup decB (map f l).
Proof.
  induction l; simpl; trivial.
  match_destr; match_destr.
  + elim n.
    apply in_map_iff; eauto.
  + simpl.
    match_destr.
    elim n0.
    eapply in_map_iff.
    eapply in_map_iff in i.
    destruct i as [? [? inn]].
    eapply nodup_In in inn.
    eauto.
  + simpl.
    rewrite IHl.
    match_destr.
    elim n0.
    eapply in_map_iff in i.
    destruct i as [? [? inn]].
    apply nodup_In in inn.
    apply in_map_iff.
    eauto.
Qed.


Lemma nodup_equiv {A} dec (l:list A) : equivlist (nodup dec l) l.
Proof.
  induction l; simpl.
  - reflexivity.
  - match_destr.
    + rewrite IHl.
      unfold equivlist; simpl; intuition congruence.
    + now rewrite IHl.
Qed.

Lemma incl_nil_r {A} (l:list A) : incl l nil -> l = nil.
Proof.
  unfold incl.
  destruct l; simpl; trivial.
  intros HH.
  elim (HH a); auto.
Qed.

Lemma remove_one_nin {A} {dec:EqDec A eq} a (l:list A) :
  ~ In a l ->
  remove_one a l = l.
Proof.
  induction l; simpl; trivial.
  match_destr.
  - intuition.
  - intros; f_equal; apply IHl.
    eauto.
Qed.

Lemma remove_one_app_nin {A} {dec:EqDec A eq} a (l1 l2:list A) :
  ~ In a l1 ->
  remove_one a (l1 ++ l2) = l1 ++ remove_one a l2.
Proof.
  induction l1; simpl; trivial.
  intros ninn.
  match_destr.
  - red in e.
    intuition.
  - rewrite IHl1 by intuition.
    trivial.
Qed.

Lemma remove_one_in_perm {A} {dec : EqDec A eq} (a:A) l :
  In a l ->
  Permutation l (a::remove_one a l).
Proof.
  induction l; simpl; intros inn.
  - tauto.
  - match_destr.
    + red in e; subst.
      reflexivity.
    + rewrite perm_swap.
      apply perm_skip.
      intuition.
Qed.

Lemma remove_other_in {A} {dec : EqDec A eq} (a1 a2:A) l :
  a1 <> a2 ->
  In a1 l <-> In a1 (remove_one a2 l).
Proof.
  intros.
  induction l; simpl.
  - intuition.
  - match_destr.
    + red in e; subst.
      intuition.
    + simpl.
      intuition.
Qed.

Lemma bminus_in_nin {A} {decA:EqDec A eq} a (l1 l2 : list A) :
  In a l1 -> ~ In a l2 -> In a (bminus l2 l1).
Proof.
  revert l1.
  induction l2; simpl in *.
  - intuition.
  - intros.
    apply IHl2.
    + apply remove_other_in; eauto.
    + eauto.
Qed.

Lemma incl_front_perm {A} {decA:EqDec A eq} (l1 l2 : list A) :
  incl l2 l1 ->
  NoDup l2 ->
  {l3: list A |
    Permutation l1 (l2 ++ l3)}.
Proof.
  exists (bminus l2 l1).
  unfold incl in *.
  induction l2; simpl; trivial.
  invcs H0.
  rewrite IHl2; trivial.
  - rewrite Permutation_middle.
    apply Permutation_app; trivial.
    rewrite remove_one_app_nin by trivial.
    rewrite bunion_bminus.
    apply remove_one_in_perm.
    apply bminus_in_nin; trivial.
    apply H; simpl; eauto.
  - simpl in H; intuition.
Qed.

Instance equivlist_incl_part {A} : PartialOrder equivlist (@incl A).
Proof.
  split.
  - intros HH; apply equivlist_incls in HH.
    split; unfold Basics.flip; intuition.
  - intros [??].
    unfold Basics.flip, incl, equivlist in *; intuition.
Qed.

Lemma NoDup_app_disj {A} (a b : list A) : NoDup (a ++ b) -> disjoint a b.
Proof.
  unfold disjoint.
  induction a; simpl.
  - intuition.
  - intros.
    invcs H.
    destruct H0.
    + subst.
      apply H4.
      apply in_app_iff; tauto.
    + eauto.
Qed.

Lemma NoDup_perm_disj {A} (l1 l2 l3 : list A) :
  Permutation l1 (l2 ++ l3) ->
  NoDup l1 ->
  disjoint l2 l3.
Proof.
  intros.
  apply NoDup_app_disj.
  now rewrite <- H.
Qed.

Lemma incl_front_perm_nodup {A} (decA:EqDec A eq) (l1 l2 : list A) :
  incl l2 l1 -> 
  {l3: list A |
    Permutation (nodup decA l1) (nodup decA l2 ++ l3)}.
Proof.
  intros.
  apply incl_front_perm; trivial.
  - now repeat rewrite nodup_equiv.
  - apply NoDup_nodup.
Qed.

Lemma Forallt_in {A} (decA:forall x y:A, {x=y} + {x <> y}) {X:A->Type} {l:list A} (ft:Forallt X l) {a} (pf:In a l) : X a.
Proof.
  induction l; simpl in *.
  - elim pf.
  - inversion ft.
    destruct (decA a a0).
    + congruence.
    + apply IHl; trivial.
      intuition congruence.
Defined.

Fixpoint Forallt_map {A B:Type} {X:A->Type} {l:list A} (f:forall a, X a -> B) (ft:Forallt X l)  : list B
  := match ft with
     | Forallt_nil _ => nil
     | Forallt_cons _ x l px pl => f x px :: Forallt_map f pl
     end.

Lemma map_nil' {A B} (f:A->B) l :
  List.map f l = nil <-> l = nil.
Proof.
  split; intros.
  - induction l; try reflexivity; simpl in *.
    congruence.
  - rewrite H; reflexivity.
Qed.

Lemma map_nil {A B} (f : A -> B) (l : list A) :
  List.map f l = (@nil B) <-> l = (@nil A).
Proof.
  split; intros.
  - induction l; try reflexivity; simpl in *.
    congruence.
  - rewrite H; reflexivity.
Qed.

Lemma map_not_nil {A B} (l : list A) (f : A -> B):
  [] <> List.map f l <-> [] <> l.  
Proof.
  rewrite ne_symm ; rewrite (ne_symm _ l).
  split ; intros.
  * intro Hl. rewrite <-(map_nil f) in Hl ; firstorder.
  * intro Hl. rewrite (map_nil f) in Hl ; firstorder.
Qed.


Lemma not_nil_exists {A} (l : list A) :
  [] <> l <-> exists a, In a l.
Proof.
  split.
  * intros Hl. 
    induction l.
  - firstorder.
  - destruct l.
    -- exists a. simpl; now left. 
    -- set (Hnc := @nil_cons _ a0 l). specialize (IHl Hnc).
       destruct IHl as [a1 Ha1]. 
       exists a1. simpl in * ; intuition.
    * intros [a Ha] not. rewrite <-not in Ha ; firstorder. 
Qed.

Lemma list_prod_not_nil {A B} {la : list A} {lb : list B}(Hla : [] <> la) (Hlb : [] <> lb) :
  [] <> list_prod la lb.
Proof.
  rewrite not_nil_exists.
  rewrite not_nil_exists in Hla.
  rewrite not_nil_exists in Hlb.
  destruct Hla as [a Hla].
  destruct Hlb as [b Hlb].
  exists (a,b). now apply in_prod. 
Qed.

(* Applies a function to an initial argument n times *)
Fixpoint applyn {A} (init : A) (g : A -> A) (n : nat) : A :=
  match n with
  | 0 => init
  | S k => g (applyn init g k)
  end.


Lemma concat_map_map {A} (l : list(list A)) (f : A -> R) :
  concat (map (map f) l) = map f (concat l).
Proof.
  induction l. 
  simpl ; reflexivity. 
  simpl. rewrite map_app. rewrite IHl. 
  reflexivity.
Qed.

Lemma ForallPairs_filter {A} R (l : list A) (p : A -> bool) :
  ForallPairs R l -> ForallPairs R (filter p l).
Proof.
  intros H. unfold ForallPairs in *.
  intros a b Ha Hb.
  apply filter_In in Ha.
  apply filter_In in Hb.
  intuition.
Qed. 

Lemma ForallOrdPairs_filter {A} R (l : list A) (p : A -> bool) :
  ForallOrdPairs R l -> ForallOrdPairs R (filter p l).
Proof.
  intros H.
  induction l. 
  - simpl ; constructor.
  - simpl. case_eq (p a).
    + invcs H. specialize (IHl H3).
      intro Hpa. constructor ; trivial.
      apply Forall_filter ; trivial.
    + intro Hpa.
      invcs H. specialize (IHl H3). assumption. 
Qed.

Lemma ForallOrdPairs_app_in {A R} {l1 l2:list A} : ForallOrdPairs R (l1 ++ l2) ->
                                                   forall x y, In x l1 -> In y l2 -> R x y.
Proof.
  revert l2.
  induction l1; simpl; intros.
  - intuition.
  - invcs H.
    destruct H0.
    + subst.
      eapply (Forall_forall _ _) in H4; try eassumption.
      rewrite in_app_iff ; eauto.
    + eapply IHl1; eauto.
Qed.

Lemma filter_true {A} :  forall p:list A, filter (fun _ => true) p = p.
Proof.
  induction p.
  - simpl; reflexivity.
  - simpl. rewrite IHp. reflexivity.
Qed.

Lemma filter_false {A} :  forall p:list A, filter (fun _ => false) p = [].
Proof.
  induction p.
  - simpl; reflexivity.
  - simpl. rewrite IHp. reflexivity.
Qed.

Lemma Forall2_refl_in {A} R (l:list A) :
  Forall (fun x => R x x) l ->
  Forall2 R l l.
Proof.
  induction l; simpl; trivial.
  intros HH; invcs HH.
  constructor; auto.
Qed.

Lemma Forall2_perm {A} R (l1 l1' l2:list A) :
  Forall2 R l1 l2 ->
  Permutation l1 l1' ->
  exists l2', Permutation l2 l2' /\
         Forall2 R l1' l2'.
Proof.
  revert l2.
  cut (forall (l1 l1':list A),
          Permutation l1 l1' ->
          (fun l1 l1' => forall l2, Forall2 R l1 l2 ->
                            exists l2', Permutation l2 l2' /\
                                   Forall2 R l1' l2') l1 l1')
  ; [ eauto | ].
  apply Permutation_ind_bis; simpl; intros.
  - invcs H. exists nil; eauto.
  - invcs H1.
    destruct (H0 _ H6) as [? [??]].
    exists (y::x0).
    split.
    + now rewrite H1.
    + now constructor.
  - invcs H1.
    invcs H6.
    destruct (H0 _ H7) as [? [??]].
    exists (y1 :: y0 :: x0).
    split.
    + rewrite H1.
      apply perm_swap.
    + repeat constructor; trivial.
  - destruct (H0 _ H3) as [? [??]].
    destruct (H2 _ H5) as [? [??]].
    exists x0.
    split; trivial.
    etransitivity; eauto.
Qed.


Global Instance ForallPairs_sublist {A} {R} : Proper (sublist --> Basics.impl) (@ForallPairs A R).
Proof.
  unfold Proper, respectful, Basics.impl, ForallPairs; intros.
  apply H0;
    eapply sublist_In; eauto.
Qed.

Lemma Forall2_map_rel {A B} (R:A->A->Prop) l1 l2 (f:A->B) :
  (forall x1 x2, In x1 l1 -> In x2 l2 -> R x1 x2 -> f x1 = f x2) ->
  Forall2 R l1 l2 ->
  map f l1 = map f l2.
Proof.
  intros H H0.
  induction H0.
  - simpl ; reflexivity.
  - simpl in *. rewrite IHForall2.
    specialize (H x y).
    rewrite H ; trivial.
    + left ; trivial.
    + left ; trivial.
    + intros x1 x2 H2 H3 H4.
      apply H.
      -- now right.
      -- now right.
      -- assumption.
Qed. 


Section equivlist.

Global Instance app_equivlist_proper {A} : Proper (equivlist ==> equivlist ==> equivlist) (@app A).
Proof.
  split; intros inn
  ; apply in_app_iff
  ; apply in_app_iff in inn.
  - destruct inn.
    + rewrite H in H1; tauto.
    + rewrite H0 in H1; tauto.
  - destruct inn.
    + rewrite <- H in H1; tauto.
    + rewrite <- H0 in H1; tauto.
Qed.

Lemma equivlist_const {A B} (b:B) (l:list A) :
  l <> nil -> 
  equivlist (map (fun _ => b) l) (b::nil).
Proof.
  induction l; simpl; intros.
  - congruence.
  - destruct l; simpl.
    + reflexivity.
    + simpl in IHl.
      rewrite IHl by congruence.
      red; simpl; tauto.
Qed.
            
Lemma list_prod_fst_equiv {A B} (a:list A) (b:list B) : b <> nil -> equivlist (map fst (list_prod a b)) a.
Proof.
  intros.
  induction a; simpl.
  - reflexivity.
  - intros.
    simpl.
    rewrite map_app.
    rewrite map_map; simpl.
    rewrite IHa.
    rewrite equivlist_const by trivial.
    reflexivity.
Qed.

Lemma list_prod_snd_equiv {A B} (a:list A) (b:list B) : a <> nil -> equivlist (map snd (list_prod a b)) b.
Proof.
  intros.
  rewrite ListAdd.list_prod_swap.
  rewrite map_map; simpl.
  rewrite <- (list_prod_fst_equiv b a) at 2 by trivial.
  reflexivity.
Qed.


Global Instance list_prod_equivlist {A B} :
  Proper (equivlist ==> equivlist ==> equivlist) (@list_prod A B).
Proof.
  cut (Proper (equivlist ==> equivlist ==> @incl _) (@list_prod A B))
  ; unfold Proper, respectful; intros.
  - apply equivlist_incls.
    split; apply H; trivial.
    + now symmetry.
    + now symmetry.
  - intros [a b] inn.
    apply in_prod_iff in inn.
    apply in_prod_iff.
    now rewrite <- H, <- H0.
Qed.

Global Instance map_equivlist_proper {A B}: Proper (pointwise_relation _ eq ==> equivlist ==> equivlist) (@map A B).
Proof.
  unfold Proper, respectful, equivlist; intros.
  repeat rewrite in_map_iff.
  unfold pointwise_relation in H.
  split; intros [? [??]].
  - subst.
    exists x2. split.
    + now rewrite H.
    + now apply H0.
  - subst.
    exists x2. split.
    + now rewrite H.
    + now apply H0.
Qed.
 
End equivlist.

Global Instance nodup_perm {A} dec : Proper (@Permutation A ==> @Permutation A) (nodup dec).
Proof.
  repeat red; intros.
  revert x y H.
  apply Permutation_ind_bis; simpl; intros.
  - trivial.
  - repeat match_destr.
    + rewrite H in i; congruence.
    + rewrite <- H in i; congruence.
    + apply perm_skip; trivial.
  - destruct (dec x y)
    ; destruct (dec y x)
    ; try congruence.
    + subst.
      destruct (in_dec dec y l)
      ; destruct (in_dec dec y l')
      ; try congruence.
      * rewrite H in i; congruence.
      * rewrite <- H in i; congruence.
      * apply perm_skip; congruence.
    + destruct (in_dec dec y l)
      ; destruct (in_dec dec x l)
      ; destruct (in_dec dec x l')
      ; destruct (in_dec dec y l')
      ; try congruence
      ; try solve [
              rewrite H in i; congruence
            | rewrite H in i0; congruence
            | rewrite H in i1; congruence
            | rewrite <- H in i; congruence
            | rewrite <- H in i0; congruence
            | rewrite <- H in i1; congruence
            | apply perm_skip; congruence
            ] .
      rewrite H0.
      apply perm_swap.
  - now rewrite H0.
Qed.


Lemma Forall_nodup {A} dec P (l:list A) : Forall P l <-> Forall P (nodup dec l).
Proof.
  repeat rewrite Forall_forall.
  generalize (nodup_In dec).
  firstorder.
Qed.
