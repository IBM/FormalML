Require Import List Lia.
Require Import Eqdep_dec.
Require Import LibUtils.
        
Import ListNotations.

Definition vector (T:Type) (n:nat)
  := { l : list T | length l = n}.

Lemma length_pf_irrel {T} {n:nat} {l:list T} (pf1 pf2:length l = n) : pf1 = pf2.
Proof.
  apply UIP_dec.
  apply PeanoNat.Nat.eq_dec.
Qed.

Lemma vector_pf_irrel {T:Type} {n:nat} {l:list T} pf1 pf2
  : exist (fun x=>length x = n) l pf1 = exist _ l pf2.
Proof.
  f_equal.
  apply length_pf_irrel.
Qed.

Lemma vector_ext {T:Type} {n:nat} {l1 l2:list T} pf1 pf2
  : l1 = l2 ->
    exist (fun x=>length x = n) l1 pf1 = exist _ l2 pf2.
Proof.
  intros; subst.
  apply vector_pf_irrel.
Qed.

Lemma vector_eq {T} {n:nat} (x y:vector T n)
  : proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x; destruct y; simpl.
  apply vector_ext.
Qed.

Lemma vector_eqs {T} {n:nat} (x y:vector T n)
  : Forall2 eq (proj1_sig x) (proj1_sig y) -> x = y.
Proof.
  destruct x; destruct y; simpl.
  intros eqq.
  apply vector_ext.
  now apply Forall2_eq.
Qed.

Program Lemma vector_length {T:Type} {n:nat} (v:vector T n)
  : length v = n.
Proof.
  now destruct v; simpl.
Qed.

(* This should move *)
Program Fixpoint map_onto {A B} (l:list A) (f:forall a, In a l -> B) : list B
  := match l with
     | [] => []
     | x::l' => f x _ :: map_onto l' (fun a pf => f a _)
     end.
Next Obligation.
  simpl; auto.
Qed.
Next Obligation.
  simpl; auto.
Qed.

Lemma map_onto_length  {A B} (l:list A) (f:forall a, In a l -> B) :
  length (map_onto l f) = length l.
Proof.
  induction l; simpl; congruence.
Qed.

Program Definition vector_map_onto {A B:Type}
           {n:nat} (v:vector A n) (f:forall a, In a v->B) : vector B n
  := map_onto v f.
Next Obligation.
  rewrite map_onto_length.
  now destruct v; simpl.
Qed.


Program Fixpoint vector_list_create
           {T:Type}
           (n:nat)
           (f:forall m, (m < n)%nat -> T) : list T
  := match n with
     | 0 => []
     | S m => vector_list_create m (fun x pf => f x _) ++ [f m _]
     end.

Lemma vector_list_create_ext
           {T:Type}
           (n:nat)
           (f1 f2:forall m, (m < n)%nat -> T) :
  (forall i pf, f1 i pf = f2 i pf) ->
  vector_list_create n f1 = vector_list_create n f2.
Proof.
  revert f1 f2.
  induction n; simpl; trivial; intros.
  f_equal; auto.
  f_equal.
  f_equal.
Qed.

Lemma vector_list_create_length
           {T:Type}
           (n:nat)
           (f:forall m, (m < n)%nat -> T) 
  : length (vector_list_create n f) = n.
Proof.
  induction n; simpl; trivial.
  rewrite app_length, IHn; simpl.
  lia.
Qed.

Program Definition vector_create
           {T:Type}
           (n:nat)
           (f:forall m, (m < n)%nat -> T) : vector T n
  := vector_list_create n f.
Next Obligation.
  apply vector_list_create_length.
Qed.

Lemma vector_create_ext
           {T:Type}
           (n:nat)
           (f1 f2:forall m, (m < n)%nat -> T) :
  (forall i pf, f1 i pf = f2 i pf) ->
  vector_create n f1 = vector_create n f2.
Proof.
  intros.
  apply vector_eq; simpl.
  now apply vector_list_create_ext.
Qed.

Definition vector_const {T} (c:T) n : vector T n
  := vector_create n (fun _ _ => c).

Program Lemma vector_const_Forall {A} (c:A) n : Forall (fun a => a = c) (vector_const c n).
Proof.
  induction n; simpl; trivial.
  apply Forall_app; auto.
Qed.

Program Lemma vector_const_eq {A} {n} (x:vector A n) c : x = vector_const c n <-> Forall (fun a => a = c) x.
Proof.
  split; intros HH.
  - subst.
    apply vector_const_Forall.
  - apply vector_eq.
    destruct x; simpl in *.
    unfold vector_const; simpl.
    subst n.
    induction x using rev_ind; simpl; trivial.
    apply Forall_app_inv in HH.
    destruct HH as [HH1 HH2].
    invcs HH2.
    rewrite (IHx HH1).
    rewrite app_length; simpl.
    rewrite PeanoNat.Nat.add_1_r; simpl.
    f_equal.
    now rewrite vector_list_create_length.
Qed.    

  Program Definition vector_nth_packed
         {T:Type}
         {n:nat}
         (i:nat)
         (pf:(i<n)%nat)
         (v:vector T n)
    : {x:T | Some x = nth_error v i}
       := match nth_error v i with
          | Some x => x
          | None => _
          end.
  Next Obligation.
    symmetry in Heq_anonymous.
    apply nth_error_None in Heq_anonymous.
   rewrite vector_length in Heq_anonymous.
   lia.
  Defined.

  Program Definition vector_nth
         {T:Type}
         {n:nat}
         (i:nat)
         (pf:(i<n)%nat)
         (v:vector T n)
    : T
    := vector_nth_packed i pf v.

  Program Lemma vector_nth_in
         {T:Type}
         {n:nat}
         (i:nat)
         (pf:(i<n)%nat)
         (v:vector T n)
    : Some (vector_nth i pf v) = nth_error v i.
  Proof.
    unfold vector_nth.
    now destruct ((vector_nth_packed i pf v)); simpl.
  Qed.

Program Definition vector_nth_rect
        {T:Type}
        (P:T->Type)
        {n:nat}
        (i:nat)
        (pf:(i<n)%nat)
        (v:vector T n)
        (Psome:forall x, nth_error v i = Some x -> P x) :
  P (vector_nth i pf v).
Proof.
  unfold vector_nth.
  destruct (vector_nth_packed i pf v); simpl.
  auto.
Qed.

Lemma vector_nth_eq {T} {n} (v1 v2:vector T n) :
  (forall i pf, vector_nth i pf v1 = vector_nth i pf v2) ->
  v1 = v2.
Proof.
  intros eqq.
  apply vector_eq.
  destruct v1; destruct v2; simpl in *.
  subst.
  revert x0 e0 eqq.
  induction x; destruct x0; simpl; intros; trivial; try discriminate.
  f_equal.
  - assert (pf:0 < S (length x)) by lia.
    specialize (eqq 0 pf).
    unfold vector_nth, proj1_sig in eqq.
    repeat match_destr_in eqq.
    simpl in *.
    congruence.
  - assert (pf:length x0 = length x) by lia.
    apply (IHx _ pf); intros.
    assert (pf2: (S i) < S (length x)) by lia.
    specialize (eqq _ pf2).
    unfold vector_nth, proj1_sig in *.
    repeat match_destr_in eqq.
    repeat match_destr.
    simpl in *.
    congruence.
Qed.

Lemma vector_nth_create
      {T : Type}
      {n : nat}
      (i : nat)
      (pf : i < n)
      (f:forall m, (m < n)%nat -> T)
  :
  vector_nth i pf (vector_create n f) = f i pf.
Proof.
  unfold vector_nth, proj1_sig.
  repeat match_destr.
  unfold vector_create in *.
  simpl in *.
  cut (Some x = Some (f i pf)); [congruence | ].
  rewrite e.
  clear.
  induction i; simpl.
  - admit.
  - destruct n; simpl in *; try lia.
    
    
    unfold vector_list_create.
    simpl.
    
    
    

    
  revert n pf f.
  induction i; simpl; intros.
  - destruct n; simpl in *; try lia.
    f_equal.
    admit.
  - assert (pf2:i< S n) by lia.
    specialize (IHi (S n) pf2).
    assert (pft:forall m (pf:m<S n), m < n) by lia.
    
    specialize (IHi pft).


  revert i pf.


  
  induction n; simpl; intros.
  - lia.
  - destruct i; simpl.
    + f_equal.
      clear.
      generalize (vector_list_create_obligation_1 T (S n) f n eq_refl).
      revert f pf.
      induction n; simpl; intros.
      * f_equal.
        apply digit_pf_irrel.
      * assert (pft:forall m (pf:m<S n), m < S (S n)) by lia.
        assert (pf2:0 < S n) by lia.
        assert (pf3:S n - S n < S n) by lia.
        specialize (IHn (fun x pf => f x (pft x pf)) pf2 pf3).
        simpl in IHn.
        replace ((pft (n - n) pf3)) with l in IHn by apply digit_pf_irrel.
        replace ((pft 0 pf2)) with pf in IHn by apply digit_pf_irrel.
        trivial.
    +
      specialize (IHn

            assert (HH:n-n=0) by lia.

      
      induc
      destruct pf.
      

      generalize HH.

      unfold vector_list_create_obligation_1.
      Set Printing All.
      f_equal.

    simpl in *; trivial.
  - simpl in *.
    assert (pf:length x = n) by lia.
    rewrite <- (IHn _ pf); clear.
    
  
  destruct v; simpl.
  revert n x e.
  induction n.
  induction i; simpl.
  induction i; simpl.

             
Lemma vector_create_nth {T} {n} (v:vector T n) :
  vector_create n (fun i pf => vector_nth i pf v) = v.
Proof.
  apply vector_nth_eq; intros.
  
  
  apply vector_eq.
  simpl.
  
  destruct v; simpl.
  revert x e.
  induction n
  ; destruct x; simpl in *; trivial; try congruence.

  intros e.
  assert (e2:length x = n) by lia.
  unfold vector_nth.
  f_equal.
  - unfold proj1_sig; simpl.
    match_destr; simpl in *.
    replace (n - n) with 0 in e0 by lia.
    simpl in e0.
    now invcs e0.
  -
    apply vector_list_create_ext; intros.
    unfold vector_nth.
    unfold proj1_sig.
    repeat match_destr; simpl in *.
    nth_error (t::x) i = nth_error x i

                                  rewrite <- (IHn _ e2).
  
  
    unfold vector_nth, vector_create; simpl.

  intros e.
  assert (n = length x) by congruence.
  f_equal.
  - clear.
    assert (eqq:nth_error (a :: x) (n - n) = Some a).
    { now replace (n - n) with 0 by lia.
    }
    unfold vector_nth_obligation_1.
    
    match_destr.
    simpl.
    
    revert eqq.
    
    
  - rewrite <- (IHx (length x) (eq_refl _)).
    apply vector_list_create_ext; intros.
    clear.
    

    
  
  match_case.
  assert (nth_error (a :: x) (length x - length x)) = a.
  -
  -
    
  constructor.
  - admit.
  - 
  
  
  
  unfold vector_nth.
  destruct v; simpl.
  revert n e.
  induction x; simpl in *; intros; subst; simpl; trivial.
  - f_equal.
    + admit.
    + erewrite <- IHx.
Qed.

Program Definition vector_map {A B:Type}
           {n:nat} (f:A->B) (v:vector A n) : vector B n
  := map f v.
Next Obligation.
  rewrite map_length.
  now destruct v; simpl.
Qed.


Program Definition vector_zip {A B:Type}
           {n:nat} (v1:vector A n) (v2:vector B n) : vector (A*B) n
  := combine v1 v2.
Next Obligation.
  rewrite combine_length.
  repeat rewrite vector_length.
  now rewrite Min.min_idempotent.
Qed.

Program Definition vector_fold_left {A B:Type} (f:A->B->A)
           {n:nat} (v:vector B n) (a0:A) : A
  := fold_left f v a0.

