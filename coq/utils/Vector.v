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

(*  Definition vector_fold_right1_bounded_dep {A:nat->Type} {B} 
             (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} 
             (v:Vector B m) (n:nat) (pf:(n<=m)%nat) {struct n}
    : A n.
  Proof.
    destruct n.
    - exact init.
    - specialize (vector_fold_right1_bounded_dep A B f init singleton m v n (le_Sn_le _ _ pf)).
      destruct n; intros.
      + exact (singleton (v (exist _ 0 pf)%nat)).
      + apply f.
        * exact (v (exist _ n (le_Sn_le _ _ pf))).
        * exact vector_fold_right1_bounded_dep.
  Defined.
*)

  Fixpoint vector_fold_right1_bounded_dep {A:nat->Type} {B} 
           (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} 
           (v:Vector B m) (bound:nat) {struct bound}
    : (bound <= m)%nat -> A bound :=
    match bound as bound' return (bound' <= m -> A bound') with
    | 0 => fun _ =>
             init
    | S bound1 =>
      fun pf0 : S bound1 <= m =>
        let an := vector_fold_right1_bounded_dep f init singleton v bound1 (le_Sn_le bound1 m pf0) in

        match bound1 as bound1' return (A bound1' -> S bound1' <= m -> A (S bound1')) with
        | 0 => fun (_ : A 0) (pf1 : 1 <= m) =>
                 singleton (v (exist _ 0 pf1))
        | S bound2 => fun (an' : A (S bound2)) (pf1 : S (S bound2) <= m) =>
                        f (S bound2) (v (exist _ bound1 pf0)) an'
        end an pf0
    end.

  Definition vector_fold_right_bounded_dep {A:nat->Type} {B}
               (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} (v:Vector B m) (n:nat)
               (pf:(n<=m)%nat)
      : A n.
    Proof.
      induction n.
      - exact init.
      - apply f.
        + exact (v (exist _ n pf)).
        + apply IHn.
          exact (le_Sn_le _ _ pf).
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
      apply NPeano.Nat.le_neq.
      split; trivial.
      now apply le_S_n in pf.
  Defined.

  
  Definition vhd {T} {n} (v:Vector T (S n)) : T := v (exist _ (0%nat) (Nat.lt_0_succ n)).
  Definition vlast {T} {n} (v:Vector T (S n)) : T := v (exist _ (n%nat) (Nat.lt_succ_diag_r n)).

  Definition vdrop_last {T} {n} (v:Vector T (S n)) : Vector T n.
  Proof.
    intros [i pf]; apply v.
    exists i.
    apply NPeano.Nat.lt_lt_succ_r; trivial.
  Defined.


  Lemma vector_fold_right1_bounded_dep_as_vector_fold_right_bounded_dep {A:nat->Type} {B} 
           (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} 
           (v:Vector B m) (bound:nat) pf
    :
      (forall x, singleton x = f _ x init) ->
        vector_fold_right1_bounded_dep f init singleton v bound pf = 
        vector_fold_right_bounded_dep f init v bound pf.
  Proof.
    intros feq.
    unfold vector_fold_right_bounded_dep.
    induction bound; simpl; trivial.
    rewrite IHbound.
    destruct bound; simpl; auto.
  Qed.

  Lemma vector_fold_right_bounded_dep_as_vector_fold_right1_bounded_dep {A:nat->Type} {B} 
        (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} 
        (v:Vector B m) (bound:nat) pf
    :
      vector_fold_right_bounded_dep f init v bound pf = 
      vector_fold_right1_bounded_dep f init (fun x => f 0 x init) v bound pf.
  Proof.
    unfold vector_fold_right_bounded_dep.
    induction bound; simpl; trivial.
    rewrite IHbound.
    destruct bound; simpl; auto.
  Qed.

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


  Lemma vector_fold_right1_dep_as_vector_fold_right_dep {A:nat->Type} {B} 
        (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} 
        (v:Vector B m)
    :
      (forall x, singleton x = f _ x init) ->
        vector_fold_right1_dep f init singleton v  = 
        vector_fold_right_dep f init v.
  Proof.
    apply vector_fold_right1_bounded_dep_as_vector_fold_right_bounded_dep.
  Qed.

  Lemma vector_fold_right_dep_as_vector_fold_right1_dep {A:nat->Type} {B} 
        (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} 
        (v:Vector B m)
    :
      vector_fold_right_dep f init v = 
      vector_fold_right1_dep f init (fun x => f 0 x init) v.
  Proof.
    apply vector_fold_right_bounded_dep_as_vector_fold_right1_bounded_dep.
  Qed.

  Lemma vector_fold_right1_as_vector_fold_right {A:Type} {B} 
        (f:B->A->A) (init:A) (singleton:B->A) {m:nat} 
        (v:Vector B m)
    :
      (forall x, singleton x = f x init) ->
        vector_fold_right1 f init singleton v  = 
        vector_fold_right f init v.
  Proof.
    apply (vector_fold_right1_dep_as_vector_fold_right_dep (fun _ => f)).
  Qed.

  Lemma vector_fold_right_as_vector_fold_right1 {A:Type} {B} 
        (f:B->A->A) (init:A) {m:nat} 
        (v:Vector B m)
    :
      vector_fold_right f init v = 
      vector_fold_right1 f init (fun x => f x init) v.
  Proof.
    apply (vector_fold_right_dep_as_vector_fold_right1_dep (fun _ => f)).
  Qed.

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
  
  Program Definition vskip {A} {m:nat} (v:Vector (A) m) (n:nat) (pf:(n<=m)%nat) : Vector A (m-n)
    := fun i => v (i+n).
  Next Obligation.
    omega.
  Defined.
  
  Definition vec_eq {A} {m:nat} (x y:Vector A m) := forall i, x i = y i.
  Notation "x =v= y" := (vec_eq x y) (at level 70).
  
  (* If we are willing to assume an axiom *)
  Lemma vec_eq_eq {A} {m:nat} (x y:Vector A m) : vec_eq x y -> x = y.
  Proof.
    intros.
    apply FunctionalExtensionality.functional_extensionality.
    apply H.
  Qed.

  Lemma index_pf_irrel n m pf1 pf2 : 
    exist (fun n' : nat => (n' < n)%nat) m pf1 =
    exist (fun n' : nat => (n' < n)%nat) m pf2.
    f_equal.
    apply digit_pf_irrel.
  Qed.

  Ltac index_prover := erewrite index_pf_irrel; reflexivity.

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

  Lemma vlast_vcons {T} {n} x (d:Vector T n) : vlast (vcons x d) = x.
  Proof.
    unfold vlast, vcons.
    match_destr; congruence.
  Qed.

  Lemma vdrop_last_vcons {T} {n} x (d:Vector T n) : vdrop_last (vcons x d) = d.
  Proof.
    unfold vdrop_last, vcons.
    apply vec_eq_eq; intros [i pf].
    match_destr; [omega | ].
    erewrite index_pf_irrel; eauto.
  Qed.

  Lemma vector_fold_right_dep_0 {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) (v:Vector B 0) : 
    vector_fold_right_dep f init v = init.
  Proof.
    reflexivity.
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

  Lemma vector_fold_right_dep_vcons {A:nat->Type} {B}
        (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} 
        x (v:Vector B m) :
    vector_fold_right_dep f init (vcons x v) = f m x (vector_fold_right_dep f init v).
  Proof.
    now rewrite vector_fold_right_dep_Sn, vlast_vcons, vdrop_last_vcons.
  Qed.

  Lemma vector_fold_right_vcons {A:Type} {B}
        (f:B->A->A) (init:A) {m:nat} 
        x (v:Vector B m)  :
    vector_fold_right f init (vcons x v) = f x (vector_fold_right f init v).
  Proof.
    apply (vector_fold_right_dep_vcons (fun _ => f)).
  Qed.

  Lemma vector_fold_right1_dep_bounded_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m:nat} (x y:Vector B m) bound pf :
    x =v= y -> vector_fold_right1_bounded_dep f init sing x bound pf = vector_fold_right1_bounded_dep f init sing y bound pf.
  Proof.
    intros eqq.
    induction bound; simpl; trivial.
    destruct bound; trivial.
    - congruence.
    - f_equal.
      + erewrite index_pf_irrel; eauto.
      + apply IHbound.
    Unshelve.
    omega.
  Qed.

  Lemma vector_fold_right1_dep_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m:nat} {x y:Vector B m} :
    x =v= y -> vector_fold_right1_dep f init sing x = vector_fold_right1_dep f init sing y.
  Proof.
    apply vector_fold_right1_dep_bounded_ext.
  Qed.

  Lemma vector_fold_right1_ext {A:Type} {B} (f:B->A->A) (init:A) sing {m:nat} {x y:Vector B m} :
    x =v= y -> vector_fold_right1 f init sing x = vector_fold_right1 f init sing y.
  Proof.
    apply (@vector_fold_right1_dep_ext (fun _ => A)).
  Qed.

  Lemma vector_fold_right1_dep_bounded_f_ext {A:nat->Type} {B} (f1 f2:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m:nat} (v:Vector B m) bound pf :
    (forall n pf a, f1 n (v (exist _ n pf)) a = f2 n (v (exist _ n pf)) a) -> vector_fold_right1_bounded_dep f1 init sing v bound pf = vector_fold_right1_bounded_dep f2 init sing v bound pf.
  Proof.
    intros eqq.
    induction bound; simpl; trivial.
    destruct bound; trivial.
    f_equal.
    eauto.
  Qed.

  Lemma vector_fold_right1_dep_f_ext {A:nat->Type} {B} (f1 f2:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m:nat} {v:Vector B m} :
    (forall n pf a, f1 n (v (exist _ n pf)) a = f2 n (v (exist _ n pf)) a) -> vector_fold_right1_dep f1 init sing v = vector_fold_right1_dep f2 init sing v.
  Proof.
    apply vector_fold_right1_dep_bounded_f_ext.
  Qed.

  Lemma vector_fold_right1_f_ext {A:Type} {B} (f1 f2:B->A->A) (init:A) sing {m:nat} {v:Vector B m} :
   (forall i a, f1 (v i) a = f2 (v i) a) -> vector_fold_right1 f1 init sing v = vector_fold_right1 f2 init sing v.
  Proof.
    intros.
    apply (@vector_fold_right1_dep_f_ext (fun _ => A)); eauto.
  Qed.

  Lemma vector_fold_right1_dep_0 {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing (v:Vector B 0) : 
    vector_fold_right1_dep f init sing v = init.
  Proof.
    reflexivity.
  Qed.
  
  Lemma vector_fold_right1_dep_1 {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing (v:Vector B 1) : 
    vector_fold_right1_dep f init sing v = sing (v (exist _ 0 Nat.lt_0_1)).
  Proof.
    unfold vector_fold_right1_dep.
    simpl.
    f_equal.
    erewrite index_pf_irrel; eauto.
  Qed.

    Lemma vector_fold_right1_bounded_dep_pf_ext {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m:nat} (v:Vector B m) bound pf1 pf2 :
    vector_fold_right1_bounded_dep f init sing v bound pf1 = vector_fold_right1_bounded_dep f init sing v bound pf2.
  Proof.
    revert pf1 pf2.
    induction bound; trivial; intros.
    simpl.
    destruct bound; simpl.
    - f_equal; index_prover.
    - f_equal; try index_prover.
      apply IHbound.
  Qed.

  Lemma vector_fold_right1_bounded_dep_SSn {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m:nat} (v:Vector B (S m)) bound pf1 pf2 pf4: 
    vector_fold_right1_bounded_dep f init sing v (S (S bound)) pf1 = f _ (v (exist _ (S bound) pf4)) (vector_fold_right1_bounded_dep f init sing v (S bound) pf2).
  Proof.
    revert pf4.
    induction bound; simpl; trivial; intros.
    f_equal; try index_prover.
    simpl in *.
    f_equal; try index_prover.
    destruct bound.
    - f_equal; try index_prover.
    - destruct bound.
      apply IHbound.
      f_equal; try index_prover.
      f_equal; try index_prover.
      apply vector_fold_right1_bounded_dep_pf_ext.
  Qed.

  Lemma vector_fold_right1_bounded_dep_relevant {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m1:nat} (v1:Vector B m1) {m2:nat} (v2:Vector B m2) bound pf1 pf2:
    (forall i, i <= bound -> forall pf1 pf2, v1 (exist _ i pf1) = v2 (exist _ i pf2)) ->
    vector_fold_right1_bounded_dep f init sing v1 bound pf1 =
    vector_fold_right1_bounded_dep f init sing v2 bound pf2.
  Proof.
    intros eqq.
    induction bound; simpl; trivial.
    destruct bound; simpl.
    - f_equal; try index_prover.
      apply eqq.
      omega.
    - f_equal.
      + apply eqq.
        omega.
      + apply IHbound; auto.
  Qed.

  Lemma vector_fold_right1_bounded_dep_droplast {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m:nat} (v:Vector B (S m)) bound pf1 pf2:
    bound < S m ->
    vector_fold_right1_bounded_dep f init sing (vdrop_last v) bound pf1 =
    vector_fold_right1_bounded_dep f init sing v bound pf2.
  Proof.
    intros.
    apply vector_fold_right1_bounded_dep_relevant; intros.
    unfold vdrop_last.
    index_prover.
  Qed.
  
  Lemma vector_fold_right1_dep_SSn {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing {m:nat} (v:Vector B (S (S m))) : 
    vector_fold_right1_dep f init sing v = f (S m) (vlast v) (vector_fold_right1_dep f init sing (vdrop_last v)).
  Proof.
    unfold vector_fold_right1_dep.
    unfold vlast.
    erewrite vector_fold_right1_bounded_dep_SSn.
    f_equal.
    erewrite vector_fold_right1_bounded_dep_droplast; trivial.
    omega.
    Unshelve.
    omega.
  Qed.

  Lemma vector_fold_right_bounded_dep_ind {A:nat->Type} {B} {P:forall m, A m -> Prop} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat)
        (finit : P 0 init)
        (ff: forall n b v, P n v -> P (S n) (f n b v)) :
    forall {m:nat} (v:Vector B m) bound pf, P bound (vector_fold_right_bounded_dep f init v bound pf).
  Proof.
    intros m v bound pf.
    revert m pf v.
    induction bound; simpl; trivial; intros.
    apply ff.
    apply IHbound.
  Qed.

  Lemma vector_fold_right_dep_ind {A:nat->Type} {B} {P:forall m, A m -> Prop} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) 
        (finit : P 0 init)
      (ff: forall n b v, P n v -> P (S n) (f n b v)) :
    forall {m:nat} (v:Vector B m), P m (vector_fold_right_dep f init v).
  Proof.
    intros.
    apply vector_fold_right_bounded_dep_ind; trivial.
  Qed.

  Lemma vector_fold_right_ind {A:Type} {B} {P:A -> Prop} (f:B->A ->A) 
        (init:A)
        (finit : P init)
      (ff: forall b v, P v -> P (f b v)) :
    forall {m:nat} (v:Vector B m), P (vector_fold_right f init v).
  Proof.
    intros.
    apply (vector_fold_right_dep_ind (P:=fun _ => P)); trivial.
  Qed.


  Lemma vector_fold_right1_bounded_dep_ind {A:nat->Type} {B} {P:forall m, A m -> Prop} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing
        (finit : P 0 init)
        (fsing: forall b, P 1 (sing b))
        (ff: forall n b v, P n v -> P (S n) (f n b v)) :
    forall {m:nat} (v:Vector B m) bound pf, P bound (vector_fold_right1_bounded_dep f init sing v bound pf).
  Proof.
    intros m v bound pf.
    revert m pf v.
    induction bound; simpl; trivial; intros.
    destruct bound; simpl; trivial.
    apply ff.
    apply IHbound.
  Qed.

  Lemma vector_fold_right1_dep_ind {A:nat->Type} {B} {P:forall m, A m -> Prop} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing
        (finit : P 0 init)
       (fsing: forall b, P 1 (sing b))
      (ff: forall n b v, P n v -> P (S n) (f n b v)) :
    forall {m:nat} (v:Vector B m), P m (vector_fold_right1_dep f init sing v).
  Proof.
    intros.
    apply vector_fold_right1_bounded_dep_ind; trivial.
  Qed.

  Lemma vector_fold_right1_ind {A:Type} {B} {P:A -> Prop} (f:B->A ->A) 
        (init:A) sing
        (finit : P init)
       (fsing: forall b, P (sing b))
      (ff: forall b v, P v -> P (f b v)) :
    forall {m:nat} (v:Vector B m), P (vector_fold_right1 f init sing v).
  Proof.
    intros.
    apply (vector_fold_right1_dep_ind (P:=fun _ => P)); trivial.
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

  Lemma vin_vlast {A n} (v:Vector A (S n)) : vin (vlast v) v.
  Proof.
    unfold vin, vlast.
    eauto.
  Qed.

  Lemma vin_vdrop_last {A n} x (v:Vector A (S n)) : vin x (vdrop_last v) -> vin x v.
  Proof.
    unfold vin, vdrop_last.
    intros [[??]?].
    eauto.
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

  Lemma vmap_ext {A B n} (f1 f2:A->B) (df:Vector A n) :
    (forall x, vin x df -> f1 x = f2 x) ->
    vmap f1 df = vmap f2 df.
  Proof.
    unfold vmap.
    induction n.
    - reflexivity.
    - intros.
      repeat rewrite vector_fold_right_dep_Sn.
      f_equal.
      + eapply H.
        eapply vin_vlast.
      + rewrite IHn; trivial.
        intros.
        eapply H.
        now apply vin_vdrop_last.
  Qed.

  Lemma vnil0 {A} (v:Vector A 0) : v = vnil.
  Proof.
    apply FunctionalExtensionality.functional_extensionality.
    intros [i pf].
    omega.
  Qed.

  Lemma vmap_id {A n} (df:Vector A n) :
    vmap (fun x => x) df = df.
  Proof.
    unfold vmap.
    induction n; simpl.
    - now rewrite vnil0, vector_fold_right_dep_0.
    - rewrite vector_fold_right_dep_Sn, IHn.
      apply vec_eq_eq.
      apply veq_sym.
      apply vector_Sn_split.
  Qed.

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
    intros.
    destruct (vectoro_to_ovector_forall_some_b _ _ H) as [? [??]].
    rewrite H0.
    f_equal.
    apply FunctionalExtensionality.functional_extensionality.
    intros.
    symmetry.
    apply H1.
  Qed.

  Lemma vectoro_to_ovector_not_none {A n} (vo : Vector (option A) n) :
    (forall i, vo i <> None) -> vectoro_to_ovector vo <> None.
  Proof.
    unfold vectoro_to_ovector.
    induction n; simpl.
    - intros eqq.
      unfold vector_fold_right_dep.
      simpl.
      congruence.
    - rewrite vector_fold_right_dep_Sn.
      intros eqq.
      specialize (IHn (vdrop_last vo)).
      unfold lift2 in *.
      repeat match_option.
      + elim IHn; trivial.
        unfold vdrop_last.
        now intros [i pf].
      + unfold vlast in eqq0.
        elim (eqq _ eqq0).
  Qed.

  Lemma vectoro_to_ovector_exists_None {A n} {vo:Vector (option A) n} :
    vectoro_to_ovector vo = None ->
    {i | vo i = None}.
  Proof.
    unfold vectoro_to_ovector.
    induction n; simpl.
    - unfold vector_fold_right_dep; simpl.
      discriminate.
    - rewrite vector_fold_right_dep_Sn.
      intros eqq.
      specialize (IHn (vdrop_last vo)).
      unfold lift2 in *.
      repeat match_option_in eqq.
      + destruct (IHn eqq1) as [[i pf] ?].
        eauto.
      + eauto.
  Qed.

  Lemma vectoro_to_ovector_None_None {A n} {vo:Vector (option A) n} i :
    vo i = None ->
    vectoro_to_ovector vo = None.
  Proof.
    destruct i as [i pf].
    unfold vectoro_to_ovector.
    induction n; simpl.
    - omega.
    - intros eqq.
      rewrite vector_fold_right_dep_Sn.
      unfold vlast.
      destruct (Nat.eq_dec i n).
      + subst.
        erewrite index_pf_irrel.
        rewrite eqq; simpl; trivial.
      + unfold lift2.
        erewrite IHn; simpl.
        * match_destr.
        * erewrite index_pf_irrel; eauto.
   Unshelve.
   omega.
  Qed.

  Definition vfirstn {T} {n} (v:Vector T n) m (pf:(m<=n)%nat): Vector T m.
  Proof.
    intros [i pf2].
    apply v.
    exists i.
    eapply NPeano.Nat.lt_le_trans; eassumption.
  Defined.

  Definition vfirstn_eq {T} {n} (v:Vector T n) pf : vfirstn v n pf = v.
  Proof.
    unfold vfirstn.
    apply FunctionalExtensionality.functional_extensionality; intros [??].
    erewrite index_pf_irrel; eauto.
  Qed.

  Lemma vfirstn_vdrop_last {T} {n} (v:Vector T n) bound pf pf2 :
      vdrop_last (vfirstn v (S bound) pf) = vfirstn v bound pf2.
  Proof.
    apply FunctionalExtensionality.functional_extensionality; intros [??]; simpl.
    erewrite index_pf_irrel; eauto.
  Qed.

  
  Lemma vlast_vfirstn {T} {n} (d:Vector T n) bound pf pf2 :
    (vlast (vfirstn d (S bound) pf)) = d ((exist _ bound pf2)).
  Proof.
    unfold vfirstn, vlast.
    erewrite index_pf_irrel; eauto.
  Qed.

  Lemma vector_fold_right1_bounded_dep_gen_ind {A:nat->Type} {B} {P:forall m, Vector B m -> A m -> Prop} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing
        (finit : P 0%nat vnil init)
        (fsing: forall b, P 1%nat (vcons b vnil) (sing b))
        (ff: forall n b v r, P n v r -> P (S n) (vcons b v) (f n b r)) :
    forall {m:nat} (v:Vector B m) bound pf, P bound (vfirstn v _ pf) (vector_fold_right1_bounded_dep f init sing v bound pf).
  Proof.
    intros m v bound pf.
    revert m pf v.
    induction bound; simpl; trivial; intros.
    - generalize (vfirstn v 0 pf); intros.
      rewrite (vnil0 v0); trivial.
    - destruct m; [omega | ].
      destruct bound; simpl; trivial.
      + replace (vfirstn v 1 pf) with (vcons (v (exist (fun n' : nat => (n' < S m)%nat) 0%nat pf)) vnil)
        ; trivial.
        apply FunctionalExtensionality.functional_extensionality; intros [??]; simpl.
        destruct x; [ | omega].
        simpl.
        erewrite index_pf_irrel; eauto.
      + assert (pf2:(S bound <= S m)%nat) by omega.
        replace (vfirstn v (S (S bound)) pf)
          with (vcons (v (exist (fun n' : nat => (n' < S m)%nat) (S bound) pf)) (vfirstn v (S bound) pf2)).
        * apply ff.
          replace (match bound as bound1' return (A bound1' -> (S bound1' <= S m)%nat -> A (S bound1')) with
                   | 0%nat =>
                     fun (_ : A 0%nat) (pf1 : (1 <= S m)%nat) =>
                       sing (v (exist (fun n' : nat => (n' < S m)%nat) 0%nat pf1))
                   | S bound2 =>
                     fun (an' : A (S bound2)) (_ : (S (S bound2) <= S m)%nat) =>
                       f (S bound2) (v (exist (fun n' : nat => (n' < S m)%nat) bound (le_Sn_le (S bound) (S m) pf))) an'
                   end
                     (vector_fold_right1_bounded_dep f init sing v bound
                                                     (le_Sn_le bound (S m) (le_Sn_le (S bound) (S m) pf))) (le_Sn_le (S bound) (S m) pf)) with (vector_fold_right1_bounded_dep f init sing v (S bound) pf2); try eapply IHbound.
          clear.
          destruct bound; simpl.
          -- erewrite index_pf_irrel; eauto.
          -- f_equal.
             ++ erewrite index_pf_irrel; eauto.
             ++ destruct bound.
                ** erewrite index_pf_irrel; eauto.
                ** { f_equal.
                     -- erewrite index_pf_irrel; eauto.
                     -- apply vector_fold_right1_bounded_dep_pf_ext.
                   } 
        * generalize (vector_Sn_split (vfirstn v (S (S bound)) pf)); intros eqq.
          apply vec_eq_eq in eqq.
          rewrite eqq.
          f_equal.
          -- unfold vlast; simpl.
             erewrite index_pf_irrel; eauto.
          -- erewrite vfirstn_vdrop_last; eauto.
  Qed.

  Lemma vector_fold_right1_dep_gen_ind {A:nat->Type} {B} {P:forall m, Vector B m -> A m -> Prop} (f:forall n,B->A n->A (S n)) 
        (init:A 0%nat) sing
        (finit : P 0%nat vnil init)
        (fsing: forall b, P 1%nat (vcons b vnil) (sing b))
        (ff: forall n b v r, P n v r -> P (S n) (vcons b v) (f n b r)) :
    forall {m:nat} (v:Vector B m), P m v (vector_fold_right1_dep f init sing v).
  Proof.
    intros.
    rewrite <- (vfirstn_eq v (le_refl m)) at 1.
    apply vector_fold_right1_bounded_dep_gen_ind; trivial.
  Qed.

  Program Definition vapp {A} {m n} (v1:Vector A m) (v2:Vector A n) : Vector A (m+n)
    := fun i => if lt_dec i m then v1 i else v2 (i-m).
  Next Obligation.
    omega.
  Defined.  

  Lemma vtake_skip_app_eq_pf n m (pf:(n<=m)%nat) : n + (m - n) = m.
  Proof.
    rewrite Nat.add_sub_assoc by trivial.
    now rewrite minus_plus.
  Defined.

  Lemma vtake_skip_app_lt_pf {m n i} (pf:(n<=m)%nat) (p2f:i < m) : i < n + (m - n).
  Proof.
    now rewrite vtake_skip_app_eq_pf.
  Defined.

  Lemma vtake_skip_app {A} {m:nat} (v:Vector (A) m) (n:nat) (pf:(n<=m)%nat) :
    forall i, v i = vapp (vtake v n pf) (vskip v n pf) (exist _ (proj1_sig i) (vtake_skip_app_lt_pf pf (proj2_sig i))).
  Proof.
    intros.
    unfold vapp, vtake, vskip.
    destruct i; simpl.
    match_destr.
    - now erewrite index_pf_irrel.
    -
      match goal with
        [|- _ = v (exist _ _ ?pff)] => generalize pff
      end.
      assert (HH:x - n + n = x) by omega.
      rewrite HH.
      intros.
      now erewrite index_pf_irrel.
  Qed.

End Vector.