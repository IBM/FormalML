Require Import List.
Require Import Omega.
Require Import LibUtils.

Section Vector.

    Definition Vector (T:Type) (n : nat) := {n':nat | n' < n}%nat -> T.
    Definition Matrix (T:Type) (n m : nat) := 
      {n':nat | n' < n}%nat -> {m':nat | m' < m}%nat -> T.


    Definition ConstVector {T} (n:nat) (c:T) : (Vector T n) := 
      fun (n': {n':nat | n' < n}%nat) => c.
    Definition ConstMatrix {T} (n m : nat) (c:T) : (Matrix T n m) := 
      fun (n': {n':nat | n' < n}%nat) (m':{m':nat | m' < m}%nat) => c.
  

    Definition vector_fold_right1_bounded_dep {A:nat->Type} {B} 
               (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} 
               (v:Vector B m) (n:nat) (pf:(n<=m)%nat)
      : A n.
    Proof.
      induction n.
      - exact init.
      - destruct n.
        + assert (pf2:(0 < m)%nat) by omega.
          exact (singleton (v (exist _ 0 pf2)%nat)).
        + assert (pf2:(S n <= m)%nat) by omega.
          assert (pf3:(S n < m)%nat) by omega.
          apply f.
          * exact (v (exist _ (S n) pf3)).
          * exact (IHn pf2).
    Defined.

    Definition vector_fold_right_bounded_dep {A:nat->Type} {B} 
               (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} (v:Vector B m) (n:nat) 
               (pf:(n<=m)%nat)
      : A n.
    Proof.
      induction n.
      - exact init.
      - apply f.
        + assert (pf2:(n < m)%nat) by omega.
          exact (v (exist _ n pf2)).
        + apply IHn.
          omega.
    Defined.

    Definition vnil {T} : Vector T 0.
    Proof.
      intros [i pf].
      omega.
    Defined.

    Definition vcons {T} {n} (x:T) (v:Vector T n) : (Vector T (S n)).
    Proof.
      intros [i pf].
      destruct (Nat.eq_dec i n).
      + exact x.
      + apply v.
        exists i.
        omega.
    Defined.

    
    Definition vhd {T} {n} (v:Vector T (S n)) : T := v (exist _ (0%nat) (Nat.lt_0_succ n)).
    Definition vlast {T} {n} (v:Vector T (S n)) : T := v (exist _ (n%nat) (Nat.lt_succ_diag_r n)).

    Definition vdrop_last {T} {n} (v:Vector T (S n)) : Vector T n.
    Proof.
      intros [i pf]; apply v.
      exists i.
      apply NPeano.Nat.lt_lt_succ_r; trivial.
    Defined.


    Definition vector_fold_right1_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) 
               (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} (v:Vector B m) : A m
      := vector_fold_right1_bounded_dep f init singleton v m (le_refl _).

    Definition vector_fold_right_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) 
               (init:A 0%nat) {m:nat} (v:Vector B m) : A m
      := vector_fold_right_bounded_dep f init v m (le_refl _).

    Definition vector_fold_right1 {A B:Type} (f:B->A->A) (init:A) (singleton:B->A) {m:nat} (v:Vector B m)
      := vector_fold_right1_dep (A:=fun _ => A) (fun _ => f) init singleton v.

    Definition vector_fold_right {A B:Type} (f:B->A->A) (init:A) {m:nat} (v:Vector B m)
      := vector_fold_right_dep (fun _ => f) init v.

    Definition vectoro_to_ovector {T} {n} (v:Vector (option T) n) : option (Vector T n)
      := vector_fold_right_dep (fun n => lift2 (@vcons _ n)) (Some vnil) v.

    Definition matrixo_to_omatrix {T} {m n} (v:Matrix (option T) m n) : option (Matrix T m n)
      := vectoro_to_ovector (fun i => vectoro_to_ovector (v i)).

    Definition vmap {A B} {n} (f:A->B) (v:Vector A n) : Vector B n
      := vector_fold_right_dep (fun n x y => vcons (n:=n) (f x) y) vnil v.


    Definition mmap {A B} {m n} (f:A->B) (mat:Matrix A m n) : Matrix B m n
      := vmap (fun mrow => vmap f mrow) mat.

    Definition list_fold_right1_bounded_dep {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
               (init:A 0%nat) (singleton:B->A 1%nat) (l:list B) (n:nat) (pf:(n<=length l)%nat)
    : A n.
    Proof.
      induction n.
      - exact init.
      - destruct n.
        + assert (pf2:(0 < length l)%nat) by omega.
          destruct l.
          * simpl in pf; omega.
          * exact (singleton b).
        + assert (pf2:(S n <= length l)%nat) by omega.
          apply f.
          * destruct l; simpl in *; try omega.
            apply b.
          * apply IHn.
            apply pf2.
    Defined.

    Definition list_fold_right1_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) 
               (init:A 0%nat) (singleton:B->A 1%nat) (l:list B) : A (length l)
      := list_fold_right1_bounded_dep f init singleton l (length l) (le_refl _).

    Definition list_fold_right_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) 
               (init:A 0%nat) (l:list B) : A (length l)
      := list_fold_right1_dep f init (fun a => f _ a init) l.

    Definition list_to_vector {A} (l:list A) : Vector A (length l)
      := list_fold_right_dep (@vcons _) vnil l.

    Definition vector_to_list {A} {n} (v:Vector A n) : list A
      := vector_fold_right cons nil v.
    
    Definition matrix_to_list_list {T} {m n} (v:Matrix T m n) : (list (list T))
      := vector_to_list (fun i => vector_to_list (v i)).

    Definition matrix_to_list {T} {m n} (v:Matrix T m n) : (list T)
      := concat (matrix_to_list_list v).

    Definition vseq start len : Vector nat len
      := eq_rect _ _ (list_to_vector (seq start len)) _ (seq_length _ _).

    Definition vector_zip {A B} {m:nat} (v1:Vector A m) (v2:Vector B m) : Vector (A*B) m
      := fun i => (v1 i, v2 i).

    Definition matrix_zip {A B} {m n:nat} (mat1:Matrix A m n) (mat2:Matrix B m n) : Matrix (A*B) m n
      := let mat12:Vector (Vector A n*Vector B n) m := vector_zip mat1 mat2 in
         vmap (fun '(a,b) => vector_zip a b) mat12.
                                 
    Definition vector_split {A B} {m:nat} (v:Vector (A*B) m) : Vector A m * Vector B m
      := (fun i => fst (v i), fun i => snd (v i)).

    Program Definition vtake {A} {m:nat} (v:Vector (A) m) (n:nat) (pf:(n<=m)%nat) : Vector A n
      := fun i => v i.
    Next Obligation.
      omega.
    Defined.

    Definition vec_eq {A} {m:nat} (x y:Vector A m) := forall i, x i = y i.
    Notation "x =v= y" := (vec_eq x y) (at level 70).
    
    (* If we are willing to assume an axiom *)
    (*
    Lemma vec_eq_eq {A} {m:nat} (x y:Vector A m) : vec_eq x y -> x = y.
    Proof.
      Require Import FunctionalExtensionality.
      intros.
      apply functional_extensionality.
      apply H.
    Qed.
     *)

    Lemma index_pf_irrel n m pf1 pf2 : 
      exist (fun n' : nat => (n' < n)%nat) m pf1 =
      exist (fun n' : nat => (n' < n)%nat) m pf2.
      f_equal.
      apply digit_pf_irrel.
    Qed.
    
    Lemma vector_Sn_split {T} {n} (v:Vector T (S n)) :
      v =v= vcons (vlast v) (vdrop_last v).
    Proof.
      intros [i pf].
      unfold vcons, vlast, vdrop_last.
      destruct (Nat.eq_dec i n)
      ; subst
      ; f_equal
      ; apply index_pf_irrel.
    Qed.

    Lemma vector_split_zip {A B} {m:nat} (v:Vector (A*B) m) :
      let '(va,vb):=vector_split v in vector_zip va vb =v= v.
    Proof.
      simpl.
      intros i.
      vm_compute.
      now destruct (v i).
    Qed.

    Lemma split_vector_zip {A B} {m:nat} (va:Vector A m) (vb:Vector B m) :
      vector_split (vector_zip va vb) = (va,vb).
    Proof.
      vm_compute.
      f_equal.
    Qed.
    

  Definition vlconcat {A n} (v:Vector (list A) n) : list A
    := concat (vector_to_list v).

  Definition vlconcat_map {A B n} (f:A->list B) (v:Vector A n) : list B
    := vlconcat (vmap f v).

  Definition vin {A n} (x:A) (v:Vector A n) : Prop
    := exists i, v i = x.

(*
  Lemma nth_In :
    forall (n:nat) (l:list A) (d:A), n < length l -> In (nth n l d) l.

  Lemma In_nth l x d : In x l ->
    exists n, n < length l /\ nth n l d = x.
 *)
  
(*
  Lemma vector_list_n (n : nat) (A : Type) (v : Vector A n) :
    length (vector_to_list v) = n.
  Proof.
    induction n.
    reflexivity.
    intros.
*)

  Notation "x =v= y" := (vec_eq x y) (at level 70).

    Lemma vector_fold_right_dep_bounded_pf_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
          (init:A 0%nat) {m:nat} (v:Vector B m) bound pf1 pf2 :
      vector_fold_right_bounded_dep f init v bound pf1 = vector_fold_right_bounded_dep f init v bound pf2.
    Proof.
      revert pf1 pf2.
      induction bound; trivial; intros.
      simpl.
      f_equal.
      f_equal.
      apply index_pf_irrel.
      trivial.
  Qed.
  
  Lemma vector_fold_right_dep_bounded_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) {m:nat} (x y:Vector B m) bound pf :
    x =v= y -> vector_fold_right_bounded_dep f init x bound pf = vector_fold_right_bounded_dep f init y bound pf.
  Proof.
    intros eqq.
    induction bound; simpl; congruence.
  Qed.

  Lemma vector_fold_right_dep_bounded_cut_down {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) {m:nat} (x:Vector B (S m)) bound pf1 pf2 :
    vector_fold_right_bounded_dep f init x bound pf1 = vector_fold_right_bounded_dep f init (vdrop_last x) bound pf2.
  Proof.
    induction bound; simpl; trivial.
    f_equal.
    - f_equal.
      apply index_pf_irrel.
    - apply IHbound.
  Qed.

  Lemma vector_fold_right_dep_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) {m:nat} {x y:Vector B m} :
    x =v= y -> vector_fold_right_dep f init x = vector_fold_right_dep f init y.
  Proof.
    apply vector_fold_right_dep_bounded_ext.
  Qed.

  Lemma vector_fold_right_ext {A:Type} {B} (f:B->A->A) (init:A) {m:nat} {x y:Vector B m} :
    x =v= y -> vector_fold_right f init x = vector_fold_right f init y.
  Proof.
    apply (@vector_fold_right_dep_ext (fun _ => A)).
  Qed.

  Lemma veq_refl {T} {n} (x:Vector T n) : x =v= x.
  Proof.
    intros i; reflexivity.
  Qed.

  Lemma veq_sym {T} {n} {x y:Vector T n} : x =v= y -> y =v= x.
  Proof.
    intros eqq i; symmetry; trivial.
  Qed.

  Lemma veq_trans {T} {n} {x y z:Vector T n} : x =v= y -> y =v= z -> x =v= z.
  Proof.
    intros eqq1 eqq2 i; etransitivity; eauto.
  Qed.

  Lemma vcons_proper {T} {n} a b (x y:Vector T n) : a = b -> x =v= y -> vcons a x =v= vcons b y.
  Proof.
    intros; subst.
    intros [i pf].
    unfold vcons.
    destruct (Nat.eq_dec i n); simpl; trivial.
  Qed.

  Lemma vdrop_last_proper {T} {n} (x y:Vector T (S n)) : x =v= y -> vdrop_last x =v= vdrop_last y.
  Proof.
    intros eqq [i pf].
    apply eqq.
  Qed.
  
  Lemma vector_fold_right_dep_Sn {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) {m:nat} (v:Vector B (S m)) : 
    vector_fold_right_dep f init v = f m (vlast v) (vector_fold_right_dep f init (vdrop_last v)).
  Proof.
    rewrite (vector_fold_right_dep_ext _ _ (vector_Sn_split v)).
    unfold vector_fold_right_dep.
    simpl.
    destruct (Nat.eq_dec m m) ; [ | congruence].
    f_equal. 
    erewrite vector_fold_right_dep_bounded_pf_ext.
    erewrite vector_fold_right_dep_bounded_cut_down.
    apply vector_fold_right_dep_bounded_ext.
    apply vdrop_last_proper.
    apply veq_sym.
    apply vector_Sn_split.
    Unshelve.
    omega.
  Qed.

  Lemma vector_fold_right_Sn {A:Type} {B} (f:B->A->A) (init:A%nat) {m:nat} (v:Vector B (S m)) : 
    vector_fold_right f init v = f (vlast v) (vector_fold_right f init (vdrop_last v)).
  Proof.
    unfold vector_fold_right.
    apply (@vector_fold_right_dep_Sn (fun _ => A)).
  Qed.
  
  Lemma vector_to_list_In {A} (x:A) {n} (v:Vector A n) :
    vin x v -> In x (vector_to_list v).
  Proof.
    induction n.
    - intros [[i pf] eqqi].
      omega.
    - intros [[i pf] eqqi].
      unfold vector_to_list in *.
      rewrite vector_fold_right_Sn; simpl.
      destruct (Nat.eq_dec i n).
      + left.
        unfold vlast.
        subst.
        erewrite index_pf_irrel; eauto.
      + right.
        apply IHn.
        eexists (exist _ i _).
        simpl.
        erewrite index_pf_irrel; eauto.
        
        Unshelve.
        simpl; omega.
  Qed.

  Lemma vin_cons {A} x (a:A) {n} {v:Vector A n} : vin x (vcons a v) <-> (x = a \/ vin x v).
  Proof.
    unfold vcons.
    split.
    - intros [[i pf] eqq].
      destruct (Nat.eq_dec i n).
      + subst; eauto.
      + right.
        eexists (exist _ i _).
        erewrite index_pf_irrel; eauto.
        
        Unshelve.
        simpl; omega.
    - intros [eqq | inn].
      + red.
        eexists (exist _ n _).
        destruct (Nat.eq_dec n n); congruence.
      + destruct inn as [[i pf] eqq].
        eexists (exist _ i _).
        destruct (Nat.eq_dec i n); [omega | ].
        erewrite index_pf_irrel; eauto.
        Unshelve.
        simpl; omega.
        simpl; omega.
  Qed.        

  Lemma vin_proper {A} (x:A) {n} {v1 v2:Vector A n} : v1 =v= v2 -> vin x v1 <-> vin x v2.
  Proof.
    revert v1 v2.
    cut (forall (v1 v2:Vector A n), v1 =v= v2 -> vin x v1 -> vin x v2).
    { intros; split; [eauto| ].
      apply veq_sym in H0; eauto.
    }
    intros v1 v2 eqq1 [i eqq2].
    exists i.
    rewrite <- eqq1; trivial.
  Qed.
    
  Lemma vector_to_list_vin {A} (x:A) {n} (v:Vector A n) :
    In x (vector_to_list v) -> vin x v.
  Proof.
    unfold vector_to_list.
    revert v.
    induction n; [simpl; tauto|].
    intros v inn.
    rewrite vector_fold_right_Sn in inn.
    destruct inn as [eqq | inn].
    - eexists.
      apply eqq.
    - apply (@vin_proper A _ (S n) _ _ (vector_Sn_split v)).
      apply vin_cons.
      eauto.
  Qed.


    Lemma vdrop_last_i {A} {n} (v:Vector A (S n)) i pf1 pf2 :
      vdrop_last v (exist (fun n' : nat => (n' < n)%nat) i pf1) =
      v (exist (fun n' : nat => (n' < S n)%nat) i pf2).
    Proof.
      unfold vdrop_last.
      erewrite index_pf_irrel; eauto.
    Qed.

    
    Lemma vmap_nth {A B : Type} (f : A -> B) {n} (v : Vector A n) i : 
      vmap f v i = f (v i).
    Proof.
      revert v i.
      unfold vmap.
      induction n; intros v [i pf].
      - omega.
      - rewrite vector_fold_right_dep_Sn.
        simpl.
        destruct (Nat.eq_dec i n).
        + subst.
          unfold vlast.
          erewrite index_pf_irrel; eauto.
        + specialize (IHn (vdrop_last v)).
          unfold vdrop_last.
          erewrite index_pf_irrel; rewrite IHn.
          erewrite vdrop_last_i; eauto.
          Unshelve.
          omega.
    Qed.

(*
    Lemma vin_vmap {A B : Type} (f : A -> B) {n} (v : Vector A n) (y : B) :
      vin y (vmap f v) -> (exists x : A, f x = y /\ vin x v).
    Proof.
      intros [i ieq].
      unfold vin.
      unfold vector_fold_right_dep.
      induction n; simpl; intros.
    Qed.
*)


    Fixpoint bounded_seq (start len : nat) {struct len} : list {n':nat | n' < start+len}%nat.
    Proof.
      revert start.
      induction len; intros start.
      - exact nil.
      - apply cons.
        + exists start.
          omega.
        + rewrite Nat.add_succ_r.
          exact (IHlen (S start)).
    Defined.

    Definition bounded_seq0 len : list {n':nat | n' < len}%nat := bounded_seq 0 len.
      
    Definition vforall {A n} (P:A->Prop) (v:Vector A n) :=
      vector_fold_right (fun x p => P x /\ p) True v.

   Lemma vforall_forall {A n} (P:A->Prop) (v:Vector A n) :
     vforall P v <-> forall i, P (v i).
   Proof.
     unfold vforall.
     split.
     - induction n.
       + intros ? [??].
         omega.
       + rewrite vector_fold_right_Sn.
         intros [Plast Pdrop].
         intros [i pf].
         destruct (Nat.eq_dec i n).
         * unfold vlast in Plast.
           subst.
           erewrite index_pf_irrel; eauto.
         * assert (pf2:(i < n)%nat) by omega.
           specialize (IHn _ Pdrop (exist _ i pf2)).
           erewrite index_pf_irrel; eauto.
     - induction n.
       + vm_compute; trivial.
       + rewrite vector_fold_right_Sn.
         intros.
         split.
         * eauto.
         * eapply IHn.
           intros [i pf].
           assert (pf2 : (i < S n)%nat) by omega.
           specialize (H (exist _ i pf2)).
           simpl in *.
           erewrite index_pf_irrel; eauto.
   Qed.

   Lemma vectoro_to_ovector_forall_some_f {A n} {vo:Vector (option A) n} {v:Vector A n} :
     vectoro_to_ovector vo = Some v ->
     (forall i, vo i = Some (v i)).
   Proof.
     unfold vectoro_to_ovector.
     induction n; simpl.
     - intros ? [??]; omega.
     - rewrite vector_fold_right_dep_Sn.
       intros eqq.
       apply some_lift2 in eqq.
       destruct eqq as [x [y eqq1 [eqq2 eqq3]]].
       subst.
       intros [i pf].
       rewrite vector_Sn_split.
       specialize (IHn _ _ eqq2).
       rewrite eqq1.
       unfold vcons.
       destruct (Nat.eq_dec i n); trivial.
   Qed.

   Lemma vectoro_to_ovector_forall_some_b {A n} (vo:Vector (option A) n) (v:Vector A n) :
     (forall i, vo i = Some (v i)) ->
     exists v', vectoro_to_ovector vo = Some v' /\ v =v= v'.
   Proof.
     unfold vectoro_to_ovector.
     induction n; simpl.
     - intros eqq.
       unfold vector_fold_right_dep.
       simpl.
       exists vnil; split; trivial.
       intros [??]; omega.
     - rewrite vector_fold_right_dep_Sn.
       intros eqq.
       specialize (IHn (vdrop_last vo) (vdrop_last v)).
       destruct IHn as [v' [eqq2 eqq3]].
       + intros [i pf].
         simpl; eauto.
       + rewrite eqq2.
         unfold vlast.
         rewrite eqq.
         simpl.
         eexists; split; [reflexivity | ].
         eapply veq_trans; [eapply (vector_Sn_split v) | ].
         apply vcons_proper; simpl; trivial.
   Qed.

   Lemma vectoro_to_ovector_forall_some_b_strong {A n} (vo:Vector (option A) n) (v:Vector A n) :
     (forall i, vo i = Some (v i)) ->
     vectoro_to_ovector vo = Some v.
   Proof.
     Require Import FunctionalExtensionality.
     intros.
     destruct (vectoro_to_ovector_forall_some_b _ _ H) as [? [??]].
     rewrite H0.
     f_equal.
     apply functional_extensionality.
     intros.
     symmetry.
     apply H1.
   Qed.

End Vector.
