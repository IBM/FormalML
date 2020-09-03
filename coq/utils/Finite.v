Require Import List EquivDec FunctionalExtensionality.
Require Import Isomorphism Eqdep_dec.

Require Import LibUtils.

Class Finite (A:Type) :=
 { elms  : list A ;
  finite : forall x:A, In x elms
 }.

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

Program Fixpoint Finite_fun_dep_elems_aux {A:Type} {dec:EqDec A eq} {B:A->Type} (la:list A) 
        {struct la} : (forall x, In x la -> list (B x)) -> list (forall a, In a la -> B a)
  := match la as la' return (forall x, In x la' -> list (B x)) -> list (forall a, In a la' -> B a) with
     | nil => fun _ => _ :: nil
     | a::xs => fun lb => let rest := Finite_fun_dep_elems_aux xs (fun x inx => lb x _) in
                     let lbx := lb a _ in
                     List.concat (List.map (fun b => List.map (fun x => _) rest) lbx)
     end.
Next Obligation.
  elim H0.
Defined.
Next Obligation.
  destruct (a == a0).
  - now destruct e.
  - apply x. intuition.
Defined.

Definition Finite_fun_dep_elems
        {A:Type} {dec:EqDec A eq} {B:A->Type} (finA:Finite A) (finB:forall a, Finite (B a))
  : list (forall a, B a)
  := List.map (fun X a => X a (finite a)) (Finite_fun_dep_elems_aux (B:=B) elms (fun a ina => elms)).

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

Lemma Finite_fun_dep_elems_aux_all
      {A:Type} {dec:EqDec A eq} {B:A->Type} (la:list A) (nd:NoDup la)
      (lb:forall a, In a la -> list (B a))
      (lbf:forall a pf x, In x (lb a pf))
  : forall x:(forall a:A, In a la -> B a), In x (Finite_fun_dep_elems_aux la lb).
Proof.
  revert lb lbf.
  induction la; simpl; intros lb lbf x.
  - left.
    apply FunctionalExtensionality.functional_extensionality_dep; intros a.
    apply FunctionalExtensionality.functional_extensionality_dep; intros ina.
    intuition.
  - invcs nd.
    specialize (IHla H2 (fun (x0 : A) (inx : In x0 la) => lb x0 (Finite_fun_dep_elems_aux_obligation_2 A a la x0 inx))).
    cut_to IHla; [| intros; apply lbf].
    rewrite concat_In.
    refine (ex_intro _ (List.map _
                                 (Finite_fun_dep_elems_aux la
                                                           (fun (x0 : A) (inx : In x0 la) => lb x0 (Finite_fun_dep_elems_aux_obligation_2 A a la x0 inx)))) _).
    split.
    rewrite in_map_iff.
    eexists; split; [reflexivity | ].
    + apply (lbf a (Finite_fun_dep_elems_aux_obligation_3 A a la) (x a (Finite_fun_dep_elems_aux_obligation_3 A a la))).
    + apply in_map_iff.
      exists (fun a' pfin => x a' (Finite_fun_dep_elems_aux_obligation_2 A a la a' pfin)).
      split; trivial.
      apply FunctionalExtensionality.functional_extensionality_dep; intros a'.
      apply FunctionalExtensionality.functional_extensionality_dep; intros ina'.
      unfold Finite_fun_dep_elems_aux_obligation_4.
      destruct (a == a').
      * destruct e.
        f_equal.
        apply in_dec_nd_pf_irrel.
        now constructor.
      * f_equal.
        apply in_dec_nd_pf_irrel.
        now constructor.
Qed.      

Lemma Finite_fun_dep_elems_nd_all
      {A:Type} {dec:EqDec A eq} {B:A->Type} (finA:Finite A) (nd:NoDup elms) (finB:forall a, Finite (B a))
  : forall x:(forall a:A, B a), In x (Finite_fun_dep_elems finA finB).
Proof.
  unfold Finite_fun_dep_elems; simpl.
  intros.
  generalize (Finite_fun_dep_elems_aux_all elms nd (B:=B) (fun a _ => elms))
  ; intros HH.
  specialize (HH (fun a _ xx => (finite xx))).
  apply List.in_map_iff.
  exists (fun a _ => x a).
  split; trivial.
Qed.

Program Instance Finite_nodup {A:Type} {dec:EqDec A eq} (finA:Finite A) : Finite A
  := {|
  elms := nodup dec elms
  ; finite := _
    |}.
Next Obligation.
  apply nodup_In.
  apply finite.
Qed.

Lemma Finite_nodup_nd {A:Type} {dec:EqDec A eq} (finA:Finite A) : NoDup (@elms _ (Finite_nodup finA)).
Proof.
  apply NoDup_nodup.
Qed.

Lemma Finite_fun_dep_elems_all
      {A:Type} {dec:EqDec A eq} {B:A->Type} (finA:Finite A) (finB:forall a, Finite (B a))
  : forall x:(forall a:A, B a), In x (Finite_fun_dep_elems (Finite_nodup finA) finB).
Proof.
  apply Finite_fun_dep_elems_nd_all.
  apply Finite_nodup_nd.
Qed.

Instance Finite_fun_dep {A:Type} {dec:EqDec A eq} {B:A->Type} (finA:Finite A) (finB:forall a, Finite (B a)): Finite (forall a : A, B a) :=
  {|
  elms := Finite_fun_dep_elems (Finite_nodup finA) finB
  ; finite := Finite_fun_dep_elems_all finA finB
|}.

Instance Finite_fun {A:Type} {dec:EqDec A eq} B (finA:Finite A) (finB:Finite B): Finite (A -> B) :=
  @Finite_fun_dep A dec (fun _ => B) finA (fun _ => finB).

