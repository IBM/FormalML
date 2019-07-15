Require Import BinNums Nat List.
Require Import Omega.

Require Import BasicTactics Isomorphism.
Import ListNotations.

Module Internal.
Inductive BinaryDigit
  := | bin_digit0 | bin_digit1.

Fixpoint pos_to_digits (p:positive) : list BinaryDigit
  := match p with
     | xI p' => bin_digit1 :: (pos_to_digits p')
     | xO p' => bin_digit0 :: (pos_to_digits p')
     | xH => [bin_digit1]
     end.

Definition N_to_digits (n:N) : list BinaryDigit
  := match n with
     | N0 => nil
     | Npos p => pos_to_digits p
     end.

Fixpoint digits_to_pos (l:list BinaryDigit) : positive
  := match l with
     | nil => xH
     | [ _ ] => xH
     | bin_digit0 :: l' => xO (digits_to_pos l')
     | bin_digit1 :: l' => xI (digits_to_pos l')
     end.

Fixpoint cleanup_zeros (l:list BinaryDigit) : list BinaryDigit
  := match l with
     | nil => nil
     | bin_digit0 :: l => cleanup_zeros l
     | _ => l
     end.

Definition fixup_trailing_zeros l
  := (rev (cleanup_zeros (rev l))).

Lemma cleanup_zeros_app_middle l1 l2 : cleanup_zeros (l1 ++ bin_digit1::l2) = (cleanup_zeros l1 ++ bin_digit1::l2).
Proof.
  revert l2.
  induction l1; simpl; trivial; intros.
  destruct a; eauto.
Qed.

Lemma fixup_trailing_zeros_app_middle l1 l2 : fixup_trailing_zeros (l1 ++ bin_digit1::l2) = (l1 ++ bin_digit1::fixup_trailing_zeros l2).
Proof.
 unfold fixup_trailing_zeros.
 rewrite rev_app_distr.
 simpl.
 rewrite app_ass; simpl.
 rewrite cleanup_zeros_app_middle.
 rewrite rev_app_distr.
 simpl.
 rewrite rev_involutive.
 rewrite <- app_assoc.
 simpl.
 reflexivity.
Qed.

Lemma fixup_trailing_zeros_end0 l1 : fixup_trailing_zeros (l1 ++ [bin_digit0]) = fixup_trailing_zeros l1.
Proof.
  unfold fixup_trailing_zeros.
  rewrite rev_app_distr.
  simpl; trivial.
Qed.

Lemma fixup_trailing_zeros_end1 l1 : fixup_trailing_zeros (l1 ++ [bin_digit1]) = l1 ++ [bin_digit1].
Proof.
  unfold fixup_trailing_zeros.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  trivial.
Qed.

Definition digits_to_N (l:list BinaryDigit) : N
       := let l_clean := fixup_trailing_zeros l in
          match l_clean with
          | nil => N0
          | _ => Npos (digits_to_pos l_clean)
          end.

Lemma pos_to_digits_nnil p : pos_to_digits p <> nil.
Proof.
  destruct p; simpl; congruence.
Qed.

Definition canon_digits digits := { ld | digits = ld ++ [bin_digit1] }.

Lemma canon_digits_dec digits : canon_digits digits + {last digits bin_digit0 = bin_digit0}.
Proof.
  unfold canon_digits.
  induction digits; simpl.
  - right; trivial.
  - destruct IHdigits.
    + destruct s as [ld pf].
      left.
      rewrite pf.
      exists (a::ld); simpl.
      trivial.
    + destruct digits.
      * destruct a; simpl; [eauto | ].
        left; exists nil; simpl.
        trivial.
      * right; trivial.
Qed.

Lemma cleanup_zeros_form l :
  {l1 |
       l = l1 ++ cleanup_zeros l
       /\ (forall x, In x l1 -> x = bin_digit0)
       /\ (forall a l2, cleanup_zeros l = a::l2 -> a = bin_digit1)}.
Proof.
  induction l.
  - exists nil; simpl.
    intuition congruence.
  - destruct IHl as [l1 [H1 [H2 H3]]].
    destruct a.
    + exists (bin_digit0 :: l1).
      simpl.
      rewrite <- H1.
      intuition.
    + exists nil; simpl; intuition congruence.
Qed.

Lemma cleanup_zeros_zero digits :
  cleanup_zeros digits = nil <-> Forall (eq bin_digit0) digits.
Proof.
  rewrite Forall_forall.
  induction digits; simpl.
  - intuition.
  - destruct a; simpl.
    + intuition.
    + split; intros HH.
      * discriminate.
      * specialize (HH bin_digit1).
        { cut_to HH.
          - discriminate.
          - eauto.
        } 
Qed.
              
Lemma fixup_trailing_zeros_canon digits :
  canon_digits (fixup_trailing_zeros digits) +
  {Forall (eq bin_digit0) digits}.
Proof.
  unfold canon_digits, fixup_trailing_zeros.
  case_eq (cleanup_zeros (rev digits)); intros eqq.
  - destruct (cleanup_zeros_zero (rev digits)).
    specialize (H eqq).
    right.
    rewrite Forall_forall in *.
    intros x xin.
    apply H.
    apply -> in_rev.
    trivial.
  - intros.
    destruct (cleanup_zeros_form (rev digits))
      as [l1 [H1 [H2 H3]]].
    left.
    rewrite (H3 _ _ H).
    simpl.
    eauto.
Qed.

Lemma fixup_trailing_zeros_canon_if digits :
  ~ Forall (eq bin_digit0) digits ->
  canon_digits (fixup_trailing_zeros digits).
Proof.
  intros.
  destruct (fixup_trailing_zeros_canon digits); tauto.
Qed.

Lemma fixup_trailing_zeros_of_canon digits :
  canon_digits digits ->
  fixup_trailing_zeros digits = digits.
Proof.
  intros [l leq].
  unfold fixup_trailing_zeros.
  rewrite leq.
  rewrite rev_app_distr.
  simpl.
  rewrite rev_involutive.
  reflexivity.
Qed.

Lemma Forall_rev {A} P (l:list A) : Forall P l <-> Forall P (rev l).
Proof.
  repeat rewrite Forall_forall.
  intuition.
  - eapply H.
    apply in_rev; trivial.
  - eapply H.
    apply in_rev; trivial.
    rewrite rev_involutive; trivial.
Qed.

Lemma fixup_trailing_zeros_zero digits :
  fixup_trailing_zeros digits = nil <-> Forall (eq bin_digit0) digits.
Proof.
  unfold fixup_trailing_zeros.
  split; intros.
  - assert (rr: rev (rev (cleanup_zeros (rev digits))) = rev []) by congruence.
    rewrite rev_involutive in rr.
    simpl in rr.
    apply cleanup_zeros_zero in rr.
    apply Forall_rev; trivial.
  - apply Forall_rev in H.
    apply cleanup_zeros_zero in H.
    rewrite H.
    reflexivity.
Qed.

Lemma pos_to_digits_canon p : canon_digits (pos_to_digits p).
Proof.
  induction p; simpl.
  - destruct IHp.
    rewrite e.
    exists (bin_digit1 :: x).
    reflexivity.
  - destruct IHp.
    rewrite e.
    exists (bin_digit0 :: x).
    reflexivity.
  - exists nil.
    reflexivity.
Qed.

Lemma digits_to_pos_to_digits p : digits_to_pos (pos_to_digits p) = p.
Proof.
  induction p; simpl.
  - rewrite IHp.
    generalize (pos_to_digits_nnil p).
    destruct (pos_to_digits p); intuition.
  - generalize (pos_to_digits_nnil p).
    rewrite IHp.
    destruct (pos_to_digits p); intuition.
  - trivial.
Qed.

Lemma digits_to_N_to_digits n : digits_to_N (N_to_digits n) = n.
Proof.
  destruct n; simpl; trivial.
  unfold digits_to_N.
  rewrite fixup_trailing_zeros_of_canon.
  - rewrite digits_to_pos_to_digits.
    generalize (pos_to_digits_nnil p).
    destruct (pos_to_digits p); intuition.
  - apply pos_to_digits_canon.
Qed.


Lemma cleanup_zeros_app_repeat l d : cleanup_zeros ((repeat bin_digit0 d) ++ l) = cleanup_zeros l.
Proof.
  induction d; simpl; trivial.
Qed.

Lemma repeat_plus_app  {A} (d:A) n1 n2 : repeat d (n1+n2) = repeat d n1 ++ repeat d n2.
Proof.
  revert n2.
  induction n1; simpl; trivial; intros.
  rewrite IHn1; trivial.
Qed.

Lemma repeat_rev {A} (d:A) n : rev (repeat d n) = repeat d n.
Proof.
  induction n; trivial.
  transitivity (repeat d (n + 1)).
  - rewrite repeat_plus_app.
    simpl.
    rewrite IHn.
    trivial.
  - f_equal.
    omega.
Qed.
  
Lemma fixup_trailing_zeros_app_repeat x d : fixup_trailing_zeros (x ++ repeat bin_digit0 d) = fixup_trailing_zeros x.
Proof.
 unfold fixup_trailing_zeros.
 rewrite rev_app_distr.
 rewrite repeat_rev.
 rewrite cleanup_zeros_app_repeat.
 trivial.
Qed.

Lemma digits_to_N_to_digits_rep n x : digits_to_N (N_to_digits n ++ repeat bin_digit0 x) = n.
Proof.
  unfold digits_to_N.
  rewrite fixup_trailing_zeros_app_repeat.
  apply digits_to_N_to_digits.
Qed.

Lemma digits_to_N_pos_to_digits_rep p x : digits_to_N (pos_to_digits p ++ repeat bin_digit0 x) = Npos p.
Proof.
  generalize (digits_to_N_to_digits_rep (Npos p) x).
  simpl; trivial.
Qed.

Lemma pos_to_digits_to_pos digits :
  canon_digits digits ->
  pos_to_digits (digits_to_pos digits) = digits.
Proof.
  induction digits; simpl.
  - intros [? ?].
    symmetry in e.
    apply app_eq_nil in e.
    destruct e.
    discriminate.
  - intros [ld eqq].
    destruct ld; simpl in eqq; inversion eqq; clear eqq.
    + reflexivity.
    + subst.
      cut_to IHdigits; [ | eauto].
      destruct b; simpl.
      * destruct (ld ++ [bin_digit1]); simpl in *; congruence.
      * destruct (ld ++ [bin_digit1]); simpl in *; congruence.
      * eexists; reflexivity.
Qed.

Lemma N_to_digits_to_N_fixup digits :
  N_to_digits (digits_to_N digits) = fixup_trailing_zeros digits.
Proof.
  intros.
  unfold N_to_digits, digits_to_N.
  generalize (fixup_trailing_zeros_canon digits); intros.
  destruct H.
  - destruct (fixup_trailing_zeros digits); trivial.
    apply pos_to_digits_to_pos; trivial.
  - apply fixup_trailing_zeros_zero in f.
    rewrite f; trivial.
Qed.

Lemma N_to_digits_to_N digits :
  canon_digits digits ->
  N_to_digits (digits_to_N digits) = digits.
Proof.
  intros.
  unfold N_to_digits, digits_to_N.
  rewrite fixup_trailing_zeros_of_canon by trivial.
  destruct digits; trivial.
  apply pos_to_digits_to_pos; trivial.
Qed.

Fixpoint interleave {A:Type} (l1 l2 : list A) {struct l1} : list A
  := match l1, l2 with
     | nil, l2 => l2
     | l1, nil => l1
     | x::l1', y::l2' => x::y::(interleave l1' l2')
     end.


Lemma interleave_length_eq {A:Type} (l1 l2 : list A) :
  length (interleave l1 l2) = length l1 + length l2.
Proof.
  revert l2.
  induction l1; destruct l2; simpl in *; trivial.
  - auto.
  - rewrite IHl1.
    omega.
Qed.

Fixpoint uninterleave {A:Type} (l : list A) : (list A*list A)
  := match l with
     | x::y::l' => let (l1,l2) := uninterleave l' in
                   (x::l1,y::l2)
     | _ => (nil, nil)
     end.

Lemma uninterleave_interleave {A:Type} (l1 l2:list A) :
  length l1 = length l2 ->
  (uninterleave (interleave l1 l2)) = (l1, l2).
Proof.
  revert l2.
  induction l1; destruct l2; simpl; trivial; intros eqq; try discriminate.
  inversion eqq; clear eqq.
  rewrite (IHl1 _ H0).
  trivial.
Qed.

Lemma uninterleave_unfold {A:Type} (l:list A) a b :
  (uninterleave (a::b::l)) = (a::(fst (uninterleave l)), b::(snd (uninterleave l))).
Proof.
  simpl.
  destruct (uninterleave l); simpl; trivial.
Qed.

Program Fixpoint EvenList_ind {A:Type} (P:list A->Prop)
    (pfnil:P nil)
    (pfconscons:forall a b l, P l -> P (a::b::l)) l {struct l} :
  Nat.Even (length l) -> P l
  := fun pfl =>
       match l with
       | nil => pfnil
       | x::y::l => pfconscons x y l (EvenList_ind P pfnil pfconscons l _)
       | _::_ => _
       end.
Next Obligation.
  destruct pfl as [n npf].
  simpl in npf.
  exists (n-1).
  destruct n; simpl; [omega | ].
  destruct n; simpl; [omega | ].
  simpl in npf.
  inversion npf.
  omega.
Qed.
Next Obligation.
  destruct (wildcard'0); simpl in *.
  - destruct pfl as [? ?]; omega.
  - elim (H _ _ _ (eq_refl _)).
Qed.

Lemma uninterleave_odd_skip {A:Type} (l:list A) a :
  Nat.Even (length l) ->
  (uninterleave (l ++ [a])) = uninterleave l.
Proof.
  intros pfeven.
  revert a.
  pattern l.
  revert l pfeven.
  apply EvenList_ind.
  - simpl; trivial.
  - intros.
    replace ((a :: b :: l) ++ [a0]) with (a :: b :: (l ++ [a0])) by reflexivity.
    repeat rewrite uninterleave_unfold.
    rewrite H.
    trivial.
Qed.

Lemma uninterleave_even_end {A:Type} (l:list A) a b :
  Nat.Even (length l) ->
  (uninterleave (l ++ [a;b])) = (fst (uninterleave l) ++ [a], snd (uninterleave l) ++ [b]).
Proof.
  intros pfeven.
  revert a b.
  pattern l.
  revert l pfeven.
  apply EvenList_ind.
  - simpl; trivial.
  - intros.
    replace ((a :: b :: l) ++ [a0; b0]) with (a :: b :: (l ++ [a0; b0])) by reflexivity.
    repeat rewrite uninterleave_unfold.
    rewrite H.
    trivial.
Qed.

Lemma interleave_uninterleave {A:Type} (l:list A) :
  Nat.Even (length l) ->
  (interleave (fst (uninterleave l)) (snd (uninterleave l))) = l.
Proof.
  revert l.
  apply EvenList_ind; simpl; trivial.
  intros.
  destruct (uninterleave l); simpl in *.
  congruence.
Qed.

Definition interleave_with_end_padding {A:Type} (l1:list A) (def1:A) (l2:list A) (def2:A) : list A
 := interleave (l1 ++ repeat def1 (length l2 - length l1)) (l2 ++ repeat def2 (length l1 - length l2)).

Lemma interleave_with_end_padding_ge {A:Type} (l1:list A) (def1:A) (l2:list A) (def2:A) :
  length l1 >= length l2 ->
  interleave_with_end_padding l1 def1 l2 def2 = interleave l1 (l2 ++ repeat def2 (length l1 - length l2)).
Proof.
  unfold interleave_with_end_padding.
  intros.
  f_equal.
  replace (length l2 - length l1) with 0 by omega.
  simpl.
  rewrite <- app_nil_end; trivial.
Qed.

Lemma interleave_with_end_padding_le {A:Type} (l1:list A) (def1:A) (l2:list A) (def2:A) :
  length l1 <= length l2 ->
  interleave_with_end_padding l1 def1 l2 def2 = interleave (l1 ++ repeat def1 (length l2 - length l1)) l2.
Proof.
  unfold interleave_with_end_padding.
  intros.
  f_equal.
  replace (length l1 - length l2) with 0 by omega.
  simpl.
  rewrite <- app_nil_end; trivial.
Qed.

Lemma interleave_with_end_padding_eq {A:Type} (l1:list A) (def1:A) (l2:list A) (def2:A) :
  length l1 = length l2 ->
  interleave_with_end_padding l1 def1 l2 def2 = interleave l1 l2.
Proof.
  intros.
  unfold interleave_with_end_padding.
  intros.
  replace (length l1 - length l2) with 0 by omega.
  replace (length l2 - length l1) with 0 by omega.
  simpl.
  repeat rewrite <- app_nil_end; trivial.
Qed.

Definition encode_digits_pair (x y : list BinaryDigit) : list BinaryDigit
  := interleave_with_end_padding x bin_digit0 y bin_digit0.

Definition decode_digits_pair (xy : list BinaryDigit) : (list BinaryDigit * list BinaryDigit)
  := uninterleave xy.

Definition encode_pair (x:N) (y:N) : N
  := digits_to_N (encode_digits_pair (N_to_digits x) (N_to_digits y)).

Definition make_even_digits digits
  := if Nat.even (length digits) then digits else (digits ++ [bin_digit0]).

Definition decode_pair_to_digits (xy:N) : (list BinaryDigit)*(list BinaryDigit)
  :=  let digits := N_to_digits xy in
       let digits' := make_even_digits digits in
       decode_digits_pair digits'.

Definition decode_pair (xy:N) : N*N
  := if N.eq_dec xy 0 then (0,0)%N else
       let xypair := decode_pair_to_digits xy in
       (digits_to_N (fst xypair), digits_to_N (snd xypair)).

(* Definition canon_digits digits := { ld | digits = ld ++ [bin_digit1] }. *)

Lemma decode_pair_to_digits_digits_to_N digits :
  canon_digits digits ->
  decode_pair_to_digits (digits_to_N digits) = uninterleave (make_even_digits digits).
Proof.
  intros canon.
  unfold decode_pair_to_digits.
  rewrite N_to_digits_to_N; trivial.
Qed.
  
Lemma interleave_in1 {A} (l1 l2:list A) :
  forall x,
  In x l1 ->
  In x (interleave l1 l2).
Proof.
  revert l2.
  induction l1; simpl.
  - intuition.
  - intros l2 x [eqq |inx].
    + subst.
      destruct l2; simpl; tauto.
    + destruct l2; simpl; eauto.
Qed.

Lemma interleave_in2 {A} (l1 l2:list A) :
  forall x,
  In x l2 ->
  In x (interleave l1 l2).
Proof.
  revert l2.
  induction l1; simpl.
  - intuition.
  - intros l2 x eqq.
    destruct l2; simpl in *; intuition eauto.
Qed.

Lemma in_interleave  {A} (l1 l2:list A) :
  forall x,
    In x (interleave l1 l2) ->
    In x l1 \/ In x l2.
Proof.
  revert l2.
  induction l1; simpl; [ eauto | ].
  destruct l2; simpl; [eauto | ].
  intuition subst.
  destruct (IHl1 _ _ H); tauto.
Qed.
  
  
Lemma interleave_with_end_padding_in1 {A} (l1 l2:list A) def1 def2:
  forall x,
  In x l1 ->
  In x (interleave_with_end_padding l1 def1 l2 def2).
Proof.
  unfold interleave_with_end_padding.
  intros.
  apply interleave_in1.
  rewrite in_app_iff.
  eauto.
Qed.

Lemma interleave_with_end_padding_in2 {A} (l1 l2:list A) def1 def2:
  forall x,
  In x l2 ->
  In x (interleave_with_end_padding l1 def1 l2 def2).
Proof.
  unfold interleave_with_end_padding.
  intros.
  apply interleave_in2.
  rewrite in_app_iff.
  eauto.
Qed.

Lemma in_interleave_with_end_padding {A} (l1 l2:list A) def1 def2:
  forall x,
    In x (interleave_with_end_padding l1 def1 l2 def2) ->
    In x l1 \/ In x l2 \/ x = def1 \/ x = def2.
Proof.
  Hint Resolve repeat_spec : list.
  intros.
  destruct (in_interleave _ _ x H)
  ; rewrite in_app_iff in *
  ; intuition eauto with list.
Qed.
  
Lemma encode_digits_pair0 l1 l2 :
  Forall (eq bin_digit0) (encode_digits_pair l1 l2) <->
  Forall (eq bin_digit0) l1 /\
  Forall (eq bin_digit0) l2.
Proof.
  unfold encode_digits_pair.
  repeat rewrite Forall_forall.
  split; intros HH.
  - intuition eauto using interleave_with_end_padding_in1,interleave_with_end_padding_in2.
  - intros ? inn.
    apply in_interleave_with_end_padding in inn.
    intuition eauto.
Qed.


Lemma N_to_digits0 n : Forall (eq bin_digit0) (N_to_digits n) <-> n = 0%N.
Proof.
  rewrite Forall_forall.
  destruct n; simpl; [tauto | ].
  split; intros.
  - specialize (H bin_digit1).
    destruct (pos_to_digits_canon p) as [? eqq].
    cut_to H; [discriminate | ].
    rewrite eqq, in_app_iff.
    simpl.
    eauto.
  - discriminate.
Qed.

Lemma digits_to_N_fixup_encode_0 n1 n2 :
  digits_to_N (encode_digits_pair (N_to_digits n1) (N_to_digits n2)) = 0%N ->
  n1 = 0%N /\ n2 = 0%N.
Proof.
  intros HH.
  unfold digits_to_N in HH.
  destruct (fixup_trailing_zeros_canon (encode_digits_pair (N_to_digits n1) (N_to_digits n2))).
  - destruct c as [? eqq].
    rewrite eqq in HH.
    unfold digits_to_N in HH.
    destruct x; simpl in *; discriminate.
  - apply encode_digits_pair0 in f.
    destruct f as [f1 f2].
    apply N_to_digits0 in f1.
    apply N_to_digits0 in f2.
    eauto.
Qed.

Lemma interleave_decompose {A} (digits1 digits2:list A) :
  digits1 <> nil ->
  length digits1 = length digits2 ->
 exists (l : list A),
    forall d1 d2 : A,
    interleave digits1 digits2 =
    l ++ [last digits1 d1; last digits2 d2].
Proof.
  revert digits2.
  induction digits1; [intuition | ].
  destruct digits2; simpl; intros; [discriminate | ].
  destruct digits1; simpl.
  - destruct digits2; simpl in *; [ | omega].
    exists nil; simpl; trivial.
  - destruct digits2; simpl in *; try discriminate.
    inversion H0.
    specialize (IHdigits1 (a2::digits2)).
    simpl in IHdigits1.
    destruct IHdigits1 as [l leq]
    ; intuition (try congruence).
    exists (a::a0::l).
    intros d1 d2.
    rewrite (leq d1 d2).
    simpl; trivial.
Qed.


Lemma last_app_nnil {A:Type} (l1 l2:list A) (d:A) :
  l2 <> nil ->
  last (l1 ++ l2) d = last l2 d.
Proof.
  intros.
  induction l1; simpl; trivial.
  rewrite IHl1.
  assert (l1 ++ l2 <> nil).
  { intros eqq. apply app_eq_nil in eqq. intuition. }
  destruct (l1 ++ l2); congruence.
Qed.

Lemma last_repeat_nzero {A:Type} (a:A) n d : n > 0 -> last (repeat a n) d = a.
Proof.
  induction n; [omega | ].
  simpl.
  destruct n; simpl in *; trivial.
  intuition.
Qed.

Lemma last_repeat_same {A:Type} (a:A) n : last (repeat a n) a = a.
Proof.
  destruct n.
  - reflexivity.
  - rewrite last_repeat_nzero; trivial.
    omega.
Qed.

Lemma interleave_with_end_padding_decompose_eq {A} (digits1:list A) defA digits2 defB :
  digits1 <> nil ->
  length digits1 = length digits2 ->
  exists l,
  forall d1 d2,
    interleave_with_end_padding digits1 defA digits2 defB = l ++ [last digits1 d1; last digits2 d2].
Proof.
  intros.
  rewrite interleave_with_end_padding_eq by omega.
  destruct (interleave_decompose digits1 digits2)
    as [l eql]; trivial.
  eauto.
Qed.
                                                        
Lemma interleave_with_end_padding_decompose_gt {A} (digits1:list A) defA digits2 defB :
  length digits1 > length digits2 ->
  exists l,
  forall d,
    interleave_with_end_padding digits1 defA digits2 defB = l ++ [last digits1 d; defB].
Proof.
  intros.
  rewrite interleave_with_end_padding_ge by omega.
  destruct (interleave_decompose digits1 (digits2 ++ repeat defB (length digits1 - length digits2)))
    as [l eql].
  - destruct digits1; simpl in *; try congruence.
    omega.
  - rewrite app_length, repeat_length.
    omega.
  - exists l.
    intros d.
    rewrite (eql d defB); simpl.
    rewrite last_app_nnil.
    + rewrite last_repeat_same; trivial.
    + assert ((length digits1 - length digits2) <> 0) by omega.
      destruct (length digits1 - length digits2); simpl; intros; congruence.
Qed.

Lemma interleave_with_end_padding_decompose_lt {A} (digits1:list A) defA digits2 defB :
  length digits1 < length digits2 ->
  exists l,
  forall d,
    interleave_with_end_padding digits1 defA digits2 defB = l ++ [defA ; last digits2 d].
Proof.
  intros.
  rewrite interleave_with_end_padding_le by omega.
  destruct (interleave_decompose (digits1 ++ repeat defA (length digits2 - length digits1)) digits2)
           as [l eql].
  - intros ?; subst.
    destruct digits2; simpl in *.
    + omega.
    + destruct digits1; try discriminate.
  - rewrite app_length, repeat_length.
    omega.
  - exists l.
    intros d.
    rewrite (eql defA d); simpl.
    rewrite last_app_nnil.
    + rewrite last_repeat_same; trivial.
    + assert ((length digits2 - length digits1) <> 0) by omega.
      destruct (length digits2 - length digits1); simpl; intros; congruence.
Qed.


Lemma is_nil {A:Type} (l:list A) : {l = nil} + {l <> nil}.
Proof.
  destruct l.
  - left; trivial.
  - right; intro; discriminate.
Defined.


Lemma interleave_with_end_padding_Even {A:Type} (l1:list A) (def1:A) (l2:list A) (def2:A) :
  Nat.Even (length (interleave_with_end_padding l1 def1 l2 def2)).
Proof.
  unfold interleave_with_end_padding.
  rewrite interleave_length_eq.
  repeat rewrite app_length, repeat_length.
  destruct (Nat.lt_trichotomy (length l1) (length l2))
    as [nlt | [neq | ngt]].
  - exists (length l2); omega.
  - exists (length l2); omega.
  - exists (length l1); omega.
Qed.

Lemma interleave_with_end_padding_even {A:Type} (l1:list A) (def1:A) (l2:list A) (def2:A) :
  Nat.even (length (interleave_with_end_padding l1 def1 l2 def2)) = true.
Proof.
  apply Nat.even_spec.
  apply interleave_with_end_padding_Even.
Qed.



Lemma fixup_trailing_zeros_app_two x d : fixup_trailing_zeros (x ++ [d; bin_digit1]) = (x ++ [d; bin_digit1]).
Proof.
 unfold fixup_trailing_zeros.
 rewrite rev_app_distr.
 simpl.
 rewrite rev_involutive.
 rewrite <- app_assoc.
 simpl.
 reflexivity.
Qed.

Definition padded_interleave_result n1 n2 :
  n1 <> 0%N \/ n2 <> 0%N ->
  (exists l, (interleave_with_end_padding (N_to_digits n1) bin_digit0 (N_to_digits n2) bin_digit0) = l ++ [bin_digit1]) \/
  (exists l, (interleave_with_end_padding (N_to_digits n1) bin_digit0 (N_to_digits n2) bin_digit0) = l ++ [bin_digit1 ; bin_digit0]).
Proof.
  simpl.
  destruct (Nat.lt_trichotomy (length (N_to_digits n1)) (length (N_to_digits n2)))
           as [n1lt | [n1eq | n1gt]].
  - destruct (interleave_with_end_padding_decompose_lt (N_to_digits n1) bin_digit0 (N_to_digits n2) bin_digit0); trivial.
    destruct n2; simpl.
    + simpl in n1lt.
      omega.
    + specialize (H bin_digit0).
      destruct (pos_to_digits_canon p) as [l leq].
      simpl in *.
      rewrite leq in *.
      rewrite last_app_nnil in H by discriminate.
      simpl in H.
      left; exists (x++ [bin_digit0]).
      rewrite app_ass; simpl.
      eauto.
  - destruct n1; simpl in *.
    + destruct n2; simpl in n1eq.
      * intuition congruence.
      * intros.
        destruct p; simpl in *; discriminate.
    + destruct (interleave_with_end_padding_decompose_eq (pos_to_digits p) bin_digit0 (N_to_digits n2) bin_digit0); trivial.
      * apply pos_to_digits_nnil.
      * intros.
        rewrite (H bin_digit0 bin_digit0).
        left.
        exists (x ++ [last (pos_to_digits p) bin_digit0]).
        rewrite app_ass; simpl.
        { destruct n2.
          - destruct p; simpl in n1eq; discriminate.
          - simpl.
            destruct (pos_to_digits_canon p0) as [l leq].
            simpl in *.
            rewrite leq.
            rewrite last_app_nnil by discriminate.
            simpl.
            reflexivity.
        } 
  - destruct (interleave_with_end_padding_decompose_gt (N_to_digits n1) bin_digit0 (N_to_digits n2) bin_digit0); trivial.
    destruct n1; simpl.
    + simpl in n1gt.
      omega.
    + specialize (H bin_digit0).
      destruct (pos_to_digits_canon p) as [l leq].
      simpl in *.
      rewrite leq in *.
      rewrite last_app_nnil in H by discriminate.
      simpl in H.
      eauto.
Qed.

Lemma make_even_digits_fixup_trailing_zeros n1 n2 :
(make_even_digits
   (fixup_trailing_zeros
      (interleave_with_end_padding (N_to_digits n1) bin_digit0 (N_to_digits n2) bin_digit0)))
= interleave_with_end_padding (N_to_digits n1) bin_digit0 (N_to_digits n2) bin_digit0.
Proof.
  generalize (interleave_with_end_padding_even (N_to_digits n1) bin_digit0 (N_to_digits n2) bin_digit0)
  ; intros is_even.
  assert (HH:n1 = 0%N /\ n2 = 0%N \/ (n1 <> 0%N \/ n2 <> 0%N)).
  { destruct n1; destruct n2; simpl; intuition congruence. }
  destruct HH.
  - destruct H; subst.
    reflexivity.
  - destruct (padded_interleave_result n1 n2) as [[l Hl] | [l Hl]]; trivial
    ; rewrite Hl in *.
    + rewrite fixup_trailing_zeros_end1.
      unfold make_even_digits.
      rewrite is_even; trivial.
    + generalize (fixup_trailing_zeros_end0 (l ++ [bin_digit1])); intros HH.
      rewrite app_ass in HH; simpl in HH.
      rewrite HH.
      rewrite fixup_trailing_zeros_end1.
      unfold make_even_digits.
      rewrite app_length in *.
      simpl in *.
      replace (length l + 2) with (S (S (length l))) in is_even by omega.
      rewrite Nat.even_succ_succ in is_even.
      replace (length l + 1) with (S (length l)) by omega.
      rewrite Nat.even_succ.
      rewrite <- Nat.negb_even.
      rewrite is_even.
      simpl.
      rewrite app_ass; simpl.
      reflexivity.
Qed.

Lemma decode_encode_pair (n1 n2:N) :
  decode_pair (encode_pair n1 n2) = (n1, n2).
Proof.
  unfold decode_pair, encode_pair.
  destruct (N.eq_dec (digits_to_N (encode_digits_pair (N_to_digits n1) (N_to_digits n2))) 0).
  - apply digits_to_N_fixup_encode_0 in e.
    intuition congruence.
  - unfold decode_pair_to_digits.
    rewrite N_to_digits_to_N_fixup.
    unfold encode_digits_pair.
    rewrite make_even_digits_fixup_trailing_zeros.
    unfold decode_digits_pair.
    unfold interleave_with_end_padding.
    rewrite uninterleave_interleave.
    + simpl.
      repeat rewrite digits_to_N_to_digits_rep.
      trivial.
    + repeat rewrite app_length.
      repeat rewrite repeat_length.
      omega.
Qed.

Lemma canon_digits_even_break digits :
  canon_digits digits ->
  Nat.even (length digits) = true ->
  { ld & {a | digits = ld ++ [a; bin_digit1] }}.
Proof.
  intros [l lpf] ev.
  rewrite lpf.
  assert (lcons: l <> nil).
  { intros ?; subst.
    simpl in *.
    discriminate.
  }
  destruct (exists_last lcons) as [x [a pf]].
  subst.
  rewrite app_ass; simpl.
  eauto.
Qed.

Lemma fixup_canon_uninterleave_even_snd digits : 
  canon_digits digits ->
  Nat.even (length digits) = true ->
  fixup_trailing_zeros (snd (uninterleave digits)) = snd (uninterleave digits).
Proof.
  intros is_canon is_even.
  destruct (canon_digits_even_break digits is_canon is_even)
    as [l [a eqq]].
  rewrite eqq in *; simpl in *.
  rewrite uninterleave_even_end.
  - simpl.
    rewrite fixup_trailing_zeros_end1.
    trivial.
  - apply Nat.even_spec; trivial.
    rewrite app_length in is_even; simpl in is_even.
    replace (length l + 2) with (2 + length l) in is_even by omega.
    simpl in is_even; trivial.
Qed.

Lemma fixup_canon_uninterleave_odd_fst digits a : 
  canon_digits digits ->
  Nat.even (length digits) = false ->
  fixup_trailing_zeros (fst (uninterleave (digits ++ [a]))) = fst (uninterleave (digits ++ [a])).
Proof.
  intros is_canon is_even.
  destruct is_canon as [a' eqq1].
  rewrite eqq1 in *.
  rewrite <- app_assoc.
  simpl.
  rewrite uninterleave_even_end.
  - simpl.
    rewrite fixup_trailing_zeros_end1; trivial.
  - apply Nat.even_spec.
    rewrite app_length in is_even.
    simpl in is_even.
    replace (length a' + 1) with (S (length a')) in is_even by omega.
    rewrite Nat.even_succ in is_even.
    rewrite <- Nat.negb_odd.
    rewrite is_even; reflexivity.
Qed.

Lemma uninterleave_length_eq_even {A} (l:list A) :
  Nat.even (length l) = true ->
  length (fst (uninterleave l)) = length (snd (uninterleave l)).
Proof.
  intros is_even.
  apply Nat.even_spec in is_even.
  revert l is_even.
  apply EvenList_ind; simpl; trivial.
  intros.
  destruct (uninterleave l); simpl in *.
  congruence.
Qed.

Lemma uninterleave_length_eq_odd {A} (l:list A) :
  Nat.odd (length l) = true ->
  length (fst (uninterleave l)) = length (snd (uninterleave l)).
Proof.
  intros is_odd.
  destruct l.
  - vm_compute in is_odd; discriminate.
  - simpl in is_odd.
    rewrite Nat.odd_succ in is_odd.
    destruct (@exists_last _ (a::l))
    as [l' [a' eqq]]; [simpl; congruence | ].
    rewrite eqq.
    assert (eqlen1:length (a :: l) = length (l' ++ [a'])) by congruence.
    rewrite app_length in eqlen1; simpl in eqlen1.
    assert (eqlen2:length l = length l') by omega.
    rewrite uninterleave_odd_skip.
    + apply uninterleave_length_eq_even; trivial.
      congruence.
    + apply Nat.even_spec; trivial.
      congruence.
Qed.
    
Lemma uninterleave_length_eq {A} (l:list A) :
  length (fst (uninterleave l)) = length (snd (uninterleave l)).
Proof.
  case_eq (Nat.even (length l)); intros is_even.
  - apply uninterleave_length_eq_even; trivial.
  - apply uninterleave_length_eq_odd; trivial.
    rewrite <- Nat.negb_even.
    rewrite is_even.
    reflexivity.
Qed.

Lemma cleanup_zeros_repeat_form l :
  exists n,
    l = repeat bin_digit0 n ++ cleanup_zeros l.
Proof.
  induction l; simpl.
  - exists 0.
    simpl; trivial.
  - destruct IHl as [n eqq].
    destruct a.
    + exists (S n); simpl.
      rewrite <- eqq.
      trivial.
    + exists 0.
      simpl; trivial.
Qed.

Lemma fixup_trailing_zeros_repeat_form l :
  exists n,
    l = fixup_trailing_zeros l ++ repeat bin_digit0 n.
Proof.
  destruct (cleanup_zeros_repeat_form (rev l)) as [n eqq].
  generalize (f_equal (@rev BinaryDigit) eqq); intros eqq2.
  rewrite rev_involutive in eqq2.
  rewrite rev_app_distr in eqq2.
  rewrite repeat_rev in eqq2.
  unfold fixup_trailing_zeros.
  eauto.
Qed.

Lemma interleave_with_end_padding_fixup_uninterleave_make_even digits :
  canon_digits digits ->
  (interleave_with_end_padding
     (fixup_trailing_zeros (fst (uninterleave (make_even_digits digits)))) bin_digit0
     (fixup_trailing_zeros (snd (uninterleave (make_even_digits digits)))) bin_digit0)
  = digits
  \/
  (interleave_with_end_padding
     (fixup_trailing_zeros (fst (uninterleave (make_even_digits digits)))) bin_digit0
     (fixup_trailing_zeros (snd (uninterleave (make_even_digits digits)))) bin_digit0)
  = digits ++ [bin_digit0].
Proof.
  intros is_canon.
  unfold make_even_digits.
  case_eq (Nat.even (length digits)); intros is_even.
  - left.
    rewrite fixup_canon_uninterleave_even_snd by trivial.
    destruct (fixup_trailing_zeros_repeat_form (fst (uninterleave digits)))
      as [n eqq].
    unfold interleave_with_end_padding.
    generalize (uninterleave_length_eq digits); intros leneqq.
    rewrite <- leneqq.
    replace ((length (fst (uninterleave digits)) - length (fixup_trailing_zeros (fst (uninterleave digits))))) with n.
    + rewrite <- eqq.
      replace ((length (fixup_trailing_zeros (fst (uninterleave digits))) - length (fst (uninterleave digits)))) with 0.
      * simpl.
        rewrite app_nil_r.
        apply interleave_uninterleave.
        apply Nat.even_spec.
        trivial.
      * rewrite eqq at 2.
        rewrite app_length.
        rewrite repeat_length.
        omega.
    + rewrite eqq at 1.
      rewrite app_length.
      rewrite repeat_length.
      omega.
  - right.
    rewrite fixup_canon_uninterleave_odd_fst by trivial.
    destruct (fixup_trailing_zeros_repeat_form (snd (uninterleave (digits ++ [bin_digit0]))))
      as [n eqq].
    unfold interleave_with_end_padding.
    generalize (uninterleave_length_eq (digits ++ [bin_digit0])); intros leneqq.
    rewrite leneqq.
      replace ((length (fixup_trailing_zeros (snd (uninterleave (digits ++ [bin_digit0])))) -
                length (snd (uninterleave (digits ++ [bin_digit0]))))) with
                                                                      0.
    + replace ((length (snd (uninterleave (digits ++ [bin_digit0]))) -
                length (fixup_trailing_zeros (snd (uninterleave (digits ++ [bin_digit0]))))))
        with n.
      * simpl.
        rewrite app_nil_r.
        rewrite <- eqq.
        rewrite interleave_uninterleave; trivial.
        apply Nat.even_spec.
        rewrite app_length.
        simpl.
        replace (length digits + 1) with (S (length digits)) by omega.
        rewrite Nat.even_succ.
        rewrite <- Nat.negb_even.
        rewrite is_even; reflexivity.
      * rewrite eqq at 1.
        rewrite app_length.
        rewrite repeat_length.
        omega.
    + rewrite eqq at 2.
      rewrite app_length.
      omega.
Qed.


Lemma interleave_with_end_padding_fixup_uninterleave_make_even_repeat digits :
  canon_digits digits ->
  exists n, 
  (interleave_with_end_padding
     (fixup_trailing_zeros (fst (uninterleave (make_even_digits digits)))) bin_digit0
     (fixup_trailing_zeros (snd (uninterleave (make_even_digits digits)))) bin_digit0)
  = digits ++ repeat bin_digit0 n.
Proof.
  intros is_canon.
  destruct (interleave_with_end_padding_fixup_uninterleave_make_even digits is_canon).
  - exists 0.
    simpl.
    rewrite app_nil_r.
    eauto.
  - exists 1.
    simpl.
    eauto.
Qed.
Lemma encode_decode_pair (n:N) :
  encode_pair (fst (decode_pair n)) (snd (decode_pair n)) = n.
Proof.
  unfold decode_pair, encode_pair.
  destruct n.
  - reflexivity.
  - simpl.
    repeat rewrite N_to_digits_to_N_fixup.
    unfold decode_pair_to_digits.
    unfold decode_digits_pair.
    simpl.
    unfold encode_digits_pair.
    destruct (interleave_with_end_padding_fixup_uninterleave_make_even_repeat (pos_to_digits p))
    as [n neqq].
    + apply pos_to_digits_canon.
    + rewrite neqq.
      apply (digits_to_N_pos_to_digits_rep p n).
Qed.

End Internal.

Program Instance N_pair_encoder : Isomorphism (N*N) N
  := {
      iso_f '(x,y) := Internal.encode_pair x y ;
      iso_b xy := Internal.decode_pair xy
    }.
Next Obligation.
    generalize (@Internal.encode_decode_pair b); intros HH.
    destruct (Internal.decode_pair b); simpl in *.
    trivial.
Qed.
Next Obligation.
  apply Internal.decode_encode_pair.
Qed.

Global Instance pair_encoder {A} (iso:Isomorphism A N) : Isomorphism (A*A) A
  := Isomorphism_trans (Isomorphism_trans (Isomorphism_prod iso iso) N_pair_encoder) (Isomorphism_symm iso).

Global Instance nat_pair_encoder : Isomorphism (nat*nat) nat := pair_encoder nat_to_N_iso.
