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
   only admits unique proofs. This is important for avoiding proof irrelevance.
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
