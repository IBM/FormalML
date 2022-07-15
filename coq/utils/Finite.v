Require Import List EquivDec FunctionalExtensionality.
Require Import Isomorphism Eqdep_dec.

Require Import LibUtils.
Require Import Lia.
Require Import ListAdd Vector.

Class Finite (A:Type) :=
 { elms  : list A ;
  finite : forall x:A, In x elms
 }.

Lemma Finite_equivlist {A:Type} (fin1:Finite A) (fin2:Finite A) :
  equivlist (@elms _ fin1) (@elms _ fin2).
Proof.
  destruct fin1 as [??]
  ; destruct fin2 as [??].
  split; intuition.
Qed.

Program Instance Finite_iso {A B} {iso:Isomorphism A B} {fin:Finite A} : Finite B
  := {
  elms:= (List.map iso_f elms)
    }.
Next Obligation.
  apply in_map_iff.
  exists (iso_b x).
  split.
  - now rewrite iso_f_b.
  - apply finite.
Qed.

Lemma in_dec_nd_pf_irrel {A:Type} {dec:EqDec A eq} {a:A} {l:list A} (nd:NoDup l) (pf1 pf2:In a l) :
  pf1 = pf2.
Proof.
  induction l.
  - inversion pf1.
  - simpl in pf1, pf2.
    invcs nd.
    destruct pf1; destruct pf2.
    + f_equal.
      apply UIP_dec.
      apply dec.
    + congruence.
    + congruence.
    + f_equal.
      auto.
Qed.

(* When we have a decidable equality, we can define a version of In which 
   has only unique proofs. This is important for avoiding proof irrelevance.
 *)
Fixpoint Inb {A} {dec:EqDec A eq} (a:A) l
  := match l with
     | nil => false
     | b::m => if b == a then
               true
             else Inb a m
     end.

Definition In_strong {A} {dec:EqDec A eq} (a:A) l := Inb a l = true.

Lemma In_strong_In {A} {dec:EqDec A eq} (a:A) l : In_strong a l -> In a l.
Proof.
  unfold In_strong.
  induction l; simpl; intuition.
  destruct (equiv_dec a0 a); intuition.
Qed.

Lemma In_In_strong {A} {dec:EqDec A eq} (a:A) l : In a l -> In_strong a l.
Proof.
  unfold In_strong.
  induction l; simpl; trivial.
  - intuition.
  - destruct (equiv_dec a0 a); simpl; intuition.
Qed.

Lemma in_strong_dec_pf_irrel_helper 
  {SBP:Prop} (v:{SBP} + {~SBP}) (P:Prop) 

    (pf1 pf2 : if v then True else P) 
    (IH : forall pf1 pf2 : P, pf1 = pf2) : pf1 = pf2.
Proof.
  destruct v.
  - destruct pf1; destruct pf2; trivial.
  - apply IH.
Qed.

Lemma in_strong_dec_pf_irrel {A:Type} {dec:EqDec A eq} {a:A} {l:list A} (pf1 pf2:In_strong a l) :
  pf1 = pf2.
Proof.
  apply UIP_dec.
  apply equiv_dec.
Qed.

Program Fixpoint Finite_fun_dep_elems_aux {A:Type} {dec:EqDec A eq} {B:A->Type} (la:list A) 
        {struct la} : (forall x, In_strong x la -> list (B x)) -> list (forall a, In_strong a la -> B a)
  := match la as la' return (forall x, In_strong x la' -> list (B x)) -> list (forall a, In_strong a la' -> B a) with
     | nil => fun _ => _ :: nil
     | a::xs => fun lb => let rest := Finite_fun_dep_elems_aux xs (fun x inx => lb x _) in
                     let lbx := lb a _ in
                     List.concat (List.map (fun b => List.map (fun x => _) rest) lbx)
     end.
Next Obligation.
  unfold In_strong in *.
  simpl.
  rewrite inx.
  now destruct (a == x).
Defined.
Next Obligation.
  unfold In_strong in *.
  simpl.
  now destruct (a == a); [| congruence].
Defined.
Next Obligation.
  destruct (a == a0).
  - now destruct e.
  - apply x.
    unfold In_strong in *.
    simpl in H.
    destruct (a == a0); trivial.
    congruence.
Defined.

Definition Finite_fun_dep_elems
        {A:Type} {dec:EqDec A eq} {B:A->Type} (finA:Finite A) (finB:forall a, Finite (B a))
  : list (forall a, B a)
  := List.map (fun X a => X a (In_In_strong _ _ (finite a))) (Finite_fun_dep_elems_aux (B:=B) elms (fun a ina => elms)).

Lemma Finite_fun_dep_elems_aux_all
      {A:Type} {dec:EqDec A eq} {B:A->Type} (la:list A) 
      (lb:forall a, In_strong a la -> list (B a))
      (lbf:forall a pf x, In x (lb a pf))
  : forall x:(forall a:A, In_strong a la -> B a), In x (Finite_fun_dep_elems_aux la lb).
Proof.
  revert lb lbf.
  induction la; simpl; intros lb lbf x.
  - left.
    apply FunctionalExtensionality.functional_extensionality_dep; intros a.
    apply FunctionalExtensionality.functional_extensionality_dep; intros ina.
    intuition.
  - specialize (IHla (fun (x0 : A) (inx : In_strong x0 la) => lb x0 (Finite_fun_dep_elems_aux_obligation_2 A dec a la x0 inx))).
    cut_to IHla; [| intros; apply lbf].
    rewrite concat_In.
    refine (ex_intro _ (List.map _
                                 (Finite_fun_dep_elems_aux la
                                                           (fun (x0 : A) (inx : In_strong x0 la) => lb x0 (Finite_fun_dep_elems_aux_obligation_2 A dec a la x0 inx)))) _).
    split.
    rewrite in_map_iff.
    eexists; split; [reflexivity | ].
    + apply (lbf a (Finite_fun_dep_elems_aux_obligation_3 A dec a la) (x a (Finite_fun_dep_elems_aux_obligation_3 A dec a la))).
    + apply in_map_iff.
      exists (fun a' pfin => x a' (Finite_fun_dep_elems_aux_obligation_2 A dec a la a' pfin)).
      split; trivial.
      apply FunctionalExtensionality.functional_extensionality_dep; intros a'.
      apply FunctionalExtensionality.functional_extensionality_dep; intros ina'.
      unfold Finite_fun_dep_elems_aux_obligation_4.
      clear.
      revert ina'.
      unfold In_strong.
      simpl.
      pattern (a == a') at 2.
      destruct (a == a'); simpl; intros.
      * destruct e.
        f_equal.
        apply in_strong_dec_pf_irrel.
      * f_equal.
        apply in_strong_dec_pf_irrel.
Qed.      

Lemma Finite_fun_dep_elems_all
      {A:Type} {dec:EqDec A eq} {B:A->Type} (finA:Finite A) (finB:forall a, Finite (B a))
  : forall x:(forall a:A, B a), In x (Finite_fun_dep_elems finA finB).
Proof.
  unfold Finite_fun_dep_elems; simpl.
  intros.
  generalize (Finite_fun_dep_elems_aux_all elms (B:=B) (fun a _ => elms))
  ; intros HH.
  specialize (HH (fun a _ xx => (finite xx))).
  apply List.in_map_iff.
  exists (fun a _ => x a).
  split; trivial.
Qed.

Instance Finite_fun_dep {A:Type} {dec:EqDec A eq} {B:A->Type} (finA:Finite A) (finB:forall a, Finite (B a)): Finite (forall a : A, B a) :=
  {|
  elms := Finite_fun_dep_elems finA finB
  ; finite := Finite_fun_dep_elems_all finA finB
|}.

Instance Finite_fun {A:Type} {dec:EqDec A eq} {B} (finA:Finite A) (finB:Finite B): Finite (A -> B) :=
  @Finite_fun_dep A dec (fun _ => B) finA (fun _ => finB).

Lemma concat_length {A:Type} (l:list (list A)) : length (concat l) = fold_right plus 0 (map (@length _) l).
Proof.
  induction l; simpl; trivial.
  now rewrite app_length, IHl.
Qed.

Lemma fold_right_add_const {A:Type} c (l:list A) :
  fold_right Nat.add 0
    (map (fun _  => c) l) =  c * length l.
Proof.
  induction l; simpl; trivial.
  rewrite IHl; simpl.
  rewrite NPeano.Nat.mul_succ_r.
  now rewrite NPeano.Nat.add_comm.
Qed.

Lemma fold_right_mult_const {A:Type} c (l:list A) :
  fold_right Nat.mul 1
    (map (fun _  => c) l) =  NPeano.Nat.pow c (length l).
Proof.
  induction l; simpl; trivial.
  now rewrite IHl; simpl.
Qed.
                                                                         
Lemma Finite_fun_dep_size {A:Type} {dec:EqDec A eq} {B:A->Type} (finA:Finite A) (finB:forall a, Finite (B a))
  : length (@elms _ (Finite_fun_dep finA finB)) =
    fold_right Nat.mul 1 (List.map (fun a => length (@elms _ (finB a))) (@elms _ finA)).
Proof.
  destruct finA.
  unfold elms; simpl.
  unfold Finite_fun_dep_elems.
  rewrite map_length.
  simpl.
  clear finite0.
  induction elms0; simpl; trivial; intros.
  rewrite concat_length.
  rewrite map_map.
  rewrite (map_ext _ (fun x : B a =>
        length
          (Finite_fun_dep_elems_aux elms0 (fun (x0 : A) (_ : In_strong x0 elms0) => elms))))
    by (intros; now rewrite map_length).
  rewrite fold_right_add_const.
  rewrite NPeano.Nat.mul_comm.
  now rewrite <- IHelms0.
Qed.

Lemma Finite_fun_size {A:Type} {dec:EqDec A eq} {B:Type} (finA:Finite A) (finB:Finite B)
  : length (@elms _ (Finite_fun finA finB)) = NPeano.pow (length (@elms _ finB)) (length (@elms _ finA)).
Proof.
  unfold Finite_fun.
  rewrite Finite_fun_dep_size.
  apply fold_right_mult_const.
Qed.  

Global Program Instance finite_prod {A B} (finA:Finite A) (finB:Finite B) : Finite (A*B)
  := { elms := list_prod elms elms }.
Next Obligation.
  apply in_prod_iff.
  split; apply finite.
Qed.

  Fixpoint list_dep_prod {A : Type} {B : A -> Type}(l:list A) (l': forall a:A, list (B a)) :
      list (sigT B) :=
      match l with
      | nil => nil
      | cons x t => map (fun y: B x => existT _ x y) (l' x) ++(list_dep_prod t l')
      end.

    Lemma in_dep_prod_aux {A : Type} {B : A -> Type} :
      forall (x:A) (y:B x) (l:list (B x)),
	      In y l -> In (existT _ x y) (map (fun y0:B x => existT _ x y0) l).
    Proof.
      induction l;
	[ simpl; auto
	  | simpl; destruct 1 as [H1| ];
	    [ left; rewrite H1; trivial | right; auto ] ].
    Qed.

    Lemma in_dep_prod {A : Type} {B : A -> Type}:
      forall (l:list A) (l':forall a:A, list (B a)) (x:A) (y:B x),
        In x l -> In y (l' x) -> In (existT _ x y) (list_dep_prod l l').
    Proof.
      induction l;
      [ simpl; tauto
      | simpl; intros; apply in_or_app; destruct H];
      [ left; rewrite H; apply in_dep_prod_aux; auto | right; auto ].
    Qed.

    Lemma in_dep_prod_iff {A:Type} {B : A -> Type} :
      forall (l:list A)(l':forall a, list (B a))(x:A)(y:B x),
        In (existT _ x y) (list_dep_prod l l') <-> In x l /\ In y (l' x).
    Proof.
      split; [ | intros; apply in_dep_prod; intuition ].
      induction l; simpl; intros.
      + intuition.
      + destruct (in_app_or _ _ _ H); clear H.
        -- rewrite in_map_iff in H0.
           destruct H0 as [z [H2 H3]].
           injection H2; intuition.
           subst ; clear H.
           (* This is equivalent to assuming Streicher's Axiom K (?). *)
           generalize (Eqdep.EqdepTheory.inj_pair2 A B _ _ _ H2); intros.
           now subst.
        -- intuition.
    Qed.

    Global Program Instance finite_dep_prod {A B} (finA : Finite A)
       (finB : forall a:A, Finite (B a))
      : Finite (sigT B).
    Next Obligation.
      apply list_dep_prod.
      + destruct finA ; auto.
      + intros a. destruct (finB a); auto.
    Defined.
    Next Obligation.
      unfold finite_dep_prod_obligation_1.
      rewrite in_dep_prod_iff.
      destruct finA as [la Hla]; split; auto.
      destruct (finB x) as [lb Hlb]; auto.
    Qed.

Definition bounded_nat_finite_list n : list {x : nat | (x < n)%nat}.
Proof.
  induction n.
  - exact nil.
  - apply cons.
    + exists n; lia.
    + eapply List.map; [| exact IHn].
      intros [x ?].
      exists x; lia.
Defined.

Lemma bounded_nat_finite_list_proj n : List.map (@proj1_sig _ _) (bounded_nat_finite_list n) = rev (seq 0 n).
Proof.
  induction n; trivial.
  rewrite ListAdd.seq_Sn.
  rewrite List.rev_app_distr.
  simpl rev.
  simpl.
  rewrite List.map_map; simpl.
  rewrite <- IHn.
  f_equal.
  now apply map_ext; intros [??].
Qed.

Global Program Instance bounded_nat_finite n : Finite {x : nat | (x < n)%nat}
  := {|
  (* put them in numeric order for the convenience of users *)
  elms := rev (bounded_nat_finite_list n) 
    |}.
Next Obligation.
  apply -> in_rev.
  assert (inn:In x (rev (seq 0 n))).
  - apply -> in_rev.
    apply in_seq; lia.
  - rewrite <- (bounded_nat_finite_list_proj n) in inn.
    apply in_map_iff in inn.
    destruct inn as [[??] [??]].
    simpl in *; subst.
    erewrite index_pf_irrel; eauto.
Qed.

Definition bounded_nat_finite_list' n : list {x : nat | (x <= n)%nat}.
Proof.
  induction n.
  - exact nil.
  - apply cons.
    + exists n; lia.
    + eapply List.map; [| exact IHn].
      intros [x ?].
      exists x; lia.
Defined.

Lemma bounded_nat_finite_list_proj' n :
  List.map (@proj1_sig _ _) (bounded_nat_finite_list' n) = rev (seq 0 n).
Proof.
  induction n; trivial.
  rewrite ListAdd.seq_Sn.
  rewrite List.rev_app_distr.
  simpl rev.
  simpl.
  rewrite List.map_map; simpl.
  rewrite <- IHn.
  f_equal.
  now apply map_ext; intros [??].
Qed.

  Program Definition bounded_nat_lt_le j (x : {m:nat | (m < j)%nat}) :
    {m : nat | (m <= j)%nat} := exist _ (proj1_sig x) _.

  Program Definition bounded_nat_lt_succ_le j (x : {m:nat | (m < j)%nat}) :
    {m : nat | (m <= S j)%nat} := exist _ (proj1_sig x) _.
  Next Obligation.
    lia.
  Defined.

  Program Definition bounded_nat_lt_succ_lt j (x : {m:nat | (m < j)%nat}) :
    {m : nat | (m < S j)%nat} := exist _ (proj1_sig x) _.

  Program Definition bounded_nat_le_succ_lt j (x : {m:nat | (m <= j)%nat}) :
    {m : nat | (m < S j)%nat} := exist _ (proj1_sig x) _.
  Next Obligation.
    lia.
  Defined.

  Program Definition bounded_nat_lt_succ_le j (x : {m:nat | (m < S j)%nat}) :
    {m : nat | (m <= j)%nat} := exist _ (proj1_sig x) _.
  Next Obligation.
    lia.
  Defined.

  Section find_ind.

    Lemma nth_error_nil {A} n : nth_error (@nil A) n = None.
    Proof.
      now destruct n; simpl.
    Qed.
          
    Context  {A} {dec:EqDec A eq}.


    Fixpoint find_index_aux (l:list A) a (index:nat) : option nat
      := match l with
         | nil => None
         | a'::l' => if a == a'
                   then Some index
                   else find_index_aux l' a (S index)
         end.

    Definition find_index (l:list A) a : option nat
      := find_index_aux l a 0%nat.

    Lemma find_index_aux_bounds {l:list A} {a} {index:nat} {n} :
      find_index_aux l a index = Some n ->
      index <= n < length l + index.
    Proof.
      revert index n.
      induction l; simpl; [congruence |]; intros index n eqq.
      match_destr_in eqq.
      - invcs eqq.
        lia.
      - specialize (IHl _ _ eqq).
        lia.
    Qed.
    
    Lemma find_index_bound {l:list A} {a} {n} :
      find_index l a = Some n ->
      n < length l.
    Proof.
      unfold find_index; intros HH.
      generalize (find_index_aux_bounds HH); lia.
    Qed.

    Lemma find_index_aux_correct {l:list A} {a} {index:nat} {n} :
      find_index_aux l a index = Some n ->
      nth_error l (n-index)%nat = Some a.
    Proof.
      revert index.
      induction l; simpl; [congruence |].
      intros index eqq.
      match_destr_in eqq.
      - invcs eqq.
        rewrite PeanoNat.Nat.sub_diag; simpl.
        congruence.
      - specialize (IHl _ eqq).
        generalize (find_index_aux_bounds eqq); intros le1.
        destruct n; [lia |].
        replace (S n - index)%nat with (S (n - index))%nat by lia.
        simpl.
        now replace (S n - S index)%nat with (n - index)%nat in IHl by lia.
    Qed.

    Lemma find_index_correct {l:list A} {a} {n} :
      find_index l a = Some n ->
      nth_error l n = Some a.
    Proof.
      intros HH.
      specialize (find_index_aux_correct HH).
      now rewrite PeanoNat.Nat.sub_0_r.
    Qed.      

    Lemma find_index_aux_first {l:list A} {a} {index:nat} {n} :
      find_index_aux l a index = Some n ->
      forall t,
      nth_error l t = Some a ->
      (n-index)%nat <= t.
    Proof.
      revert index.
      induction l; simpl; [congruence |].
      intros index eqq.
      match_destr_in eqq.
      - invcs eqq.
        rewrite PeanoNat.Nat.sub_diag; simpl.
        lia.
      - specialize (IHl _ eqq).
        intros [|]; simpl; intros eqq2.
        + congruence.
        + specialize (IHl _ eqq2).
          lia.
    Qed.

    
    Lemma find_index_first {l:list A} {a} {index:nat} {n} :
      find_index l a = Some n ->
      forall t,
      nth_error l t = Some a ->
      n <= t.
    Proof.
      intros eqq t eqq2.
      specialize (find_index_aux_first eqq _ eqq2).
      lia.
    Qed.

    Lemma find_index_aux_complete {l:list A} {a} {index:nat} :
      In a l ->
      {t' | find_index_aux l a index = Some t'}.
    Proof.
      revert index.
      induction l; simpl; intros index eqq; [tauto |].
      - match_destr.
        + red in e; subst; eauto.
        + destruct (IHl (S index)); [| eauto].
          destruct eqq; trivial.
          congruence.
    Qed.

    Lemma find_index_complete {l:list A} {a} :
      In a l ->
      { t' | find_index l a = Some t'}.
    Proof.
      intros.
      now apply find_index_aux_complete.
    Qed.

  End find_ind.

  Section fin_ind.
    Context {A} {dec:EqDec A eq} (fin:Finite A).

    Program Instance finite_nodup : Finite A
      := {|
        elms := nodup dec elms
      |}.
    Next Obligation.
      apply nodup_In.
      apply finite.
    Qed.

                 
    Definition finite_index (a:A) : nat
      := proj1_sig (find_index_complete (finite (Finite:=finite_nodup) a)).

    Lemma finite_index_correct a :
      nth_error (elms (Finite:=finite_nodup)) (finite_index a) = Some a.
    Proof.
      unfold finite_index, proj1_sig; match_destr.
      now apply find_index_correct.
    Qed.
    
    Lemma finite_index_bound a :
      finite_index a < length (nodup dec (elms (Finite:=fin))).
    Proof.
      unfold finite_index, proj1_sig; match_destr.
      now apply find_index_bound in e.
    Qed.
      

    Lemma bounded_index_pf_irrel n m1 m2 pf1 pf2 :
      m1 = m2 ->
      exist (fun n' : nat => (n' < n)%nat) m1 pf1 =
        exist (fun n' : nat => (n' < n)%nat) m2 pf2.
    Proof.
      intros eqq.
      destruct eqq.
      assert (pf1 = pf2) by apply digit_pf_irrel.
      congruence.
  Qed.

    Definition nth_error_len_some (l:list A) (n:nat) (pf:n < length l) :
      { x | nth_error l n = Some x}.
    Proof.
      apply nth_error_Some in pf.
      destruct (nth_error l n); [eauto | congruence].
    Qed.
        
    Program Instance finite_index_iso : Isomorphism A {m:nat | (m < length (nodup dec (elms (Finite:=fin))))%nat}
      := {|
        iso_f a := exist _ _ (finite_index_bound a)
      ; iso_b x := proj1_sig (nth_error_len_some (elms (Finite:=finite_nodup)) x _)
      |}.
    Next Obligation.
      apply bounded_index_pf_irrel.
      unfold proj1_sig; match_destr.
      unfold finite_index, proj1_sig; match_destr.
      apply find_index_correct in e0.
      simpl in e0.
      eapply NoDup_nth_error; try now rewrite e, e0.
      - apply NoDup_nodup.
      - apply nth_error_Some.
        congruence.
    Qed.
    Next Obligation.
      unfold proj1_sig; match_destr.
      rewrite finite_index_correct in e.
      congruence.
    Qed.
    
  End fin_ind.

