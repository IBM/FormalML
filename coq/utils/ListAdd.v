Require Import List Permutation.
Require Import RelationClasses Morphisms.
Require Import Omega Lia Lra Rbase.
Require Import Relation_Definitions Sorted.

Require Import LibUtils.

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

  Lemma seq_Sn s n : seq s (S n) = seq s n ++ [(s+n)]%nat.
  Proof.
    replace (S n) with (n + 1)%nat by omega.
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
  - destruct idx; simpl in *; omega.
  - simpl in *.
    destruct idx; trivial.
    rewrite IHl by omega.
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
  omega.
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
  - simpl; omega.
  - rewrite seq_Sn.
    rewrite last_app by congruence.
    simpl.
    omega.
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
  - destruct n; omega.
  - destruct n; trivial.
    intros; eauto.
    rewrite IHl; trivial; omega.
Qed.

Lemma map_nth_in_exists {A B} (f:A->B) l d1 n :
  (n < length l)%nat ->
  exists d2,
  nth n (map f l) d1 = f (nth n l d2).
Proof.
  revert n.
  induction l; simpl.
  - destruct n; omega.
  - destruct n; trivial.
    + intros; eauto.
    + intros.
      destruct (IHl n).
      * omega.
      * rewrite H0.
        eauto.
Qed.

Lemma nth_in_default {A} (l:list A) d1 d2 n :
  (n < length l)%nat ->
  nth n l d1 = nth n l d2.
Proof.
  revert n.
  induction l; simpl.
  - destruct n; omega.
  - destruct n; trivial.
    + intros; eauto.
      rewrite (IHl n); trivial.
      omega.
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
  ; [ omega | ].
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
  rewrite app_nth2 by omega.
  simpl.
  case_eq (idx2 - length l1); try omega.
  intros.
  apply nth_In.
  omega.
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
    omega.
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
    assert (idx_bound':idx < length l) by omega.
    destruct (nth_split l d1 idx_bound') as [l1 [l2 [eqq leneq]]].
    revert eqq.
    generalize (nth idx l d1); intros a1.
    intros eqq r1 r2 nr1.
    subst.
    rewrite app_nth2 in * by omega.
    replace ((S (length l1) - length l1)) with 1 in * by omega.
    rewrite app_length in idx_bound.
    simpl in *.
    destruct l2; simpl in *; [ omega | ].
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
    omega.
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
  - omega.
  - destruct l'; simpl in *.
    + omega.
    + destruct n; simpl; trivial.
      apply IHl.
      omega.
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
  omega.
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
    rewrite Nat.min_r; omega.
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
