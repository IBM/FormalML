Require Import Program.Basics.
Require Import List Lia.
Require Import Eqdep_dec.
Require Import Equivalence EquivDec Isomorphism.
Require Import LibUtils ListAdd.
Require Import Arith.

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

Definition vector0 {T} : vector T 0%nat := exist _ [] (eq_refl _).

Lemma vector0_0 {T} (v:vector T 0%nat) : v = vector0.
Proof.
  apply vector_eq.
  destruct v; simpl.
  destruct x; simpl in *; trivial.
  congruence.
Qed.

Program Lemma vector_length {T:Type} {n:nat} (v:vector T n)
  : length v = n.
Proof.
  now destruct v; simpl.
Qed.

Program Definition vector_map_onto {A B:Type}
        {n:nat} (v:vector A n) (f:forall a, In a v->B) : vector B n
  := map_onto v f.
Next Obligation.
  rewrite map_onto_length.
  now destruct v; simpl.
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


Program Lemma vector_Forall2_nth_iff {A B} {n} (P:A->B->Prop) (v1:vector A n) (v2:vector B n) :
  (forall (i : nat) (pf : (i < n)%nat), P (vector_nth i pf v1) (vector_nth i pf v2)) <->
  Forall2 P v1 v2.
Proof.
  destruct v1 as [v1 ?]; destruct v2 as [v2 ?]; simpl in *; subst.
  split
  ; revert v2 e0
  ; induction v1
  ; destruct v2; simpl in *; try discriminate
  ; intros e; intros.
  - trivial.
  - constructor.
    + assert (pf0:(0 < S (length v1))%nat) by lia.
      specialize (H _ pf0).
      unfold vector_nth, proj1_sig in H.
      repeat match_destr_in H; simpl in *.
      congruence.
    + assert (pf1:length v2 = length v1) by lia.
      apply (IHv1 _ pf1); intros.
      unfold vector_nth, proj1_sig.
      repeat match_destr; simpl in *.
      assert (pf2:(S i < S (length v1))%nat) by lia.
      specialize (H (S i) pf2).      
      unfold vector_nth, proj1_sig in H.
      repeat match_destr_in H; simpl in *.
      congruence.
  - lia.
  - invcs H.
    unfold vector_nth, proj1_sig.
    repeat match_destr; simpl in *.
    destruct i; simpl in *.
    + congruence.
    + invcs e.
      assert (pf1:(i < length v1)%nat) by lia.
      specialize (IHv1 _ H0 H5 i pf1).
      unfold vector_nth, proj1_sig in IHv1.
      repeat match_destr_in IHv1; simpl in *.
      congruence.
Qed.

Lemma vector_nth_eq {T} {n} (v1 v2:vector T n) :
  (forall i pf, vector_nth i pf v1 = vector_nth i pf v2) ->
  v1 = v2.
Proof.
  intros.
  apply vector_eqs.
  now apply vector_Forall2_nth_iff.
Qed.


Program Lemma vector_nth_In {A}
        {n}
        (v:vector A n)
        i
        pf
  : In (vector_nth i pf v) v.
Proof.
  unfold vector_nth, proj1_sig.
  repeat match_destr.
  simpl in *.
  symmetry in e.
  now apply nth_error_In in e.
Qed.  

Program Lemma In_vector_nth_ex {T} {n} {x:vector T n} a :
  In a x ->
  exists i pf, vector_nth i pf x = a.
Proof.
  intros inn.
  apply In_nth_error in inn.
  destruct inn as [i eqq].
  destruct x; simpl in *.
  destruct (lt_dec i (length x)).
  - subst.
    exists i, l.
    unfold vector_nth, proj1_sig.
    repeat match_destr.
    simpl in *.
    congruence.
  - assert (HH:(length x <= i)%nat) by lia.
    apply nth_error_None in HH.
    congruence.
Qed.

Lemma nth_error_map_onto {A B} (l:list A) (f:forall a, In a l->B) i d :
  nth_error (map_onto l f) i = Some d ->
  exists d' pfin, nth_error l i = Some d' /\
                  d = f d' pfin.
Proof.
  revert l f d.
  induction i; destruct l; simpl; intros; try discriminate.
  - invcs H.
    eauto.
  - destruct (IHi _ _ _ H) as [d' [pfin [??]]]; subst.
    eauto.
Qed.

Program Lemma vector_nth_map_onto
        {A B:Type}
        {n:nat} (v:vector A n) (f:forall a, In a v->B)
        i
        (pf:i<n) :
  exists pfin, vector_nth i pf (vector_map_onto v f) = f (vector_nth i pf v) pfin.
Proof.
  unfold vector_map_onto.
  unfold vector_nth, proj1_sig.
  repeat match_destr.
  simpl in *.
  symmetry in e1.
  destruct (nth_error_map_onto _ _ _ _ e1) as [?[?[??]]].
  subst.
  rewrite H in e.
  invcs e.
  eauto.
Qed.

Program Fixpoint vector_list_create
        {T:Type}
        (start:nat)
        (len:nat)
        (f:(forall m, start <= m -> m < start + len -> T)%nat) : list T
  := match len with
     | 0 => []
     | S m => f start _ _ :: vector_list_create (S start) m (fun x pf1 pf2 => f x _ _)
     end.
Solve All Obligations with lia.

Lemma vector_list_create_length
      {T:Type}
      (start:nat)
      (len:nat)
      (f:(forall m, start <= m -> m < start + len -> T)%nat) :
  length (vector_list_create start len f) = len.
Proof.
  revert start f.
  induction len; simpl; trivial; intros.
  f_equal.
  auto.
Qed.

Program Definition vector_create
        {T:Type}
        (start:nat)
        (len:nat)
        (f:(forall m, start <= m -> m < start + len -> T)%nat) : vector T len
  := vector_list_create start len f.
Next Obligation.
  apply vector_list_create_length.
Qed.

Lemma vector_list_create_ext
      {T:Type}
      (start len:nat)
      (f1 f2:(forall m, start <= m -> m < start + len -> T)%nat) :
  (forall i pf1 pf2, f1 i pf1 pf2 = f2 i pf1 pf2) ->
  vector_list_create start len f1 = vector_list_create start len f2.
Proof.
  revert f1 f2.
  revert start.
  induction len; simpl; trivial; intros.
  f_equal; auto.
Qed.

Lemma vector_create_ext
      {T:Type}
      (start len:nat)
      (f1 f2:(forall m, start <= m -> m < start + len -> T)%nat) :
  (forall i pf1 pf2, f1 i pf1 pf2 = f2 i pf1 pf2) ->
  vector_create start len f1 = vector_create start len f2.
Proof.
  intros.
  apply vector_eq; simpl.
  now apply vector_list_create_ext.
Qed.

Definition vector_const {T} (c:T) n : vector T n
  := vector_create 0 n (fun _ _ _ => c).


Lemma vector_list_create_const_Forall {A} (c:A) start len :
  Forall (fun a : A => a = c)
         (vector_list_create start len (fun (m : nat) (_ : start <= m) (_ : m < start + len) => c)).
Proof.
  revert start.
  induction len; simpl; trivial; intros.
  constructor; trivial.
  now specialize (IHlen (S start)).
Qed.

Program Lemma vector_const_Forall {A} (c:A) n : Forall (fun a => a = c) (vector_const c n).
Proof.
  unfold vector_const, vector_create; simpl.
  apply vector_list_create_const_Forall.
Qed.

Lemma vector_list_create_const_shift {A} (c:A) start1 start2 len :
  vector_list_create start1 len (fun (m : nat) _ _ => c) =
  vector_list_create start2 len (fun (m : nat) _ _ => c).
Proof.
  revert start1 start2.
  induction len; simpl; trivial; intros.
  f_equal.
  now specialize (IHlen (S start1) (S start2)).
Qed.

Lemma vector_list_create_const_vector_eq {A} x c start :
  Forall (fun a : A => a = c) x ->
  x = vector_list_create start (length x) (fun m _ _ => c).
Proof.
  revert start.
  induction x; simpl; trivial; intros.
  invcs H.
  f_equal.
  now apply IHx.
Qed.

Lemma vector_list_create_shiftS
      {T:Type}
      (start len:nat)
      (f:(forall m, S start <= m -> m < S start + len -> T)%nat) :
  vector_list_create (S start) len f =
  vector_list_create start len (fun x pf1 pf2 => f (S x)%nat (le_n_S _ _ pf1) (lt_n_S _ _ pf2)).
Proof.
  revert start f.
  induction len; simpl; trivial; intros.
  rewrite IHlen.
  f_equal.
  - f_equal; apply le_uniqueness_proof.
  - apply vector_list_create_ext; intros.
    f_equal; apply le_uniqueness_proof.
Qed.

Lemma vector_list_create_shift0
      {T:Type}
      (start len:nat)
      (f:(forall m, start <= m -> m < start + len -> T)%nat) :
  vector_list_create start len f =
  vector_list_create 0 len (fun x _ pf2 => f (start+x)%nat (le_plus_l start _) (plus_lt_compat_l _ _ start pf2)).
Proof.
  induction start; simpl.
  - apply vector_list_create_ext; intros.
    f_equal; apply le_uniqueness_proof.
  - rewrite vector_list_create_shiftS.
    rewrite IHstart.
    apply vector_list_create_ext; intros.
    f_equal; apply le_uniqueness_proof.
Qed.

Lemma vector_list_create_map
      {T U:Type}
      (start len:nat)
      (f:(forall m, start <= m -> m < start + len -> T)%nat)
      (g:T->U) :
  map g (vector_list_create start len f) =
  vector_list_create start len (fun x pf1 pf2 => g (f x pf1 pf2)).
Proof.
  revert start f.
  induction len; simpl; trivial; intros.
  f_equal.
  apply IHlen.
Qed.

Program Lemma vector_const_eq {A} {n} (x:vector A n) c : x = vector_const c n <-> Forall (fun a => a = c) x.
Proof.
  split; intros HH.
  - subst.
    apply vector_const_Forall.
  - apply vector_eq.
    destruct x; simpl in *.
    subst n.
    rewrite (vector_list_create_const_vector_eq x c 0); trivial.
    now rewrite vector_list_create_length.
Qed.

Lemma vector_create_fun_ext
      {T}
      (start len:nat)
      (f:(forall m, start <= m -> m < start + len -> T)%nat)
      m1 m2
      pf1 pf1'
      pf2 pf2'
  : m1 = m2 ->
    f m1 pf1 pf2 = f m2 pf1' pf2'.
Proof.
  intros eqq.
  destruct eqq.
  f_equal; apply le_uniqueness_proof.
Qed.

Lemma vector_create_fun_simple_ext
      {T}
      (len:nat)
      (f:(forall m, m < len -> T)%nat)
      m1 m2
      pf pf'
  : m1 = m2 ->
    f m1 pf = f m2 pf'.
Proof.
  intros eqq.
  destruct eqq.
  f_equal; apply le_uniqueness_proof.
Qed.

Lemma vector_nth_create
      {T : Type}
      (start len : nat)
      (i : nat)
      (pf2: i < len)
      (f:(forall m, start <= m -> m < start + len -> T)%nat) :
  vector_nth i pf2 (vector_create start len f) = f (start + i) (PeanoNat.Nat.le_add_r start i) (Plus.plus_lt_compat_l _ _ start pf2).
Proof.
  unfold vector_nth, proj1_sig.
  repeat match_destr.
  unfold vector_create in *.
  simpl in *.
  match goal with
    [|- ?x = ?y] => cut (Some x = Some y); [now inversion 1 |]
  end.
  rewrite e; clear e.
  revert start len pf2 f.

  induction i; simpl; intros
  ; destruct len; simpl; try lia. 
  - f_equal.
    apply vector_create_fun_ext.
    lia.
  - assert (pf2':i < len) by lia.
    rewrite (IHi (S start) len pf2').
    f_equal.
    apply vector_create_fun_ext.
    lia.
Qed.

Lemma vector_nth_create'
      {T : Type}
      (len : nat)
      (i : nat)
      (pf: i < len)
      (f:(forall m, m < len -> T)%nat) :
  vector_nth i pf (vector_create 0 len (fun m _ pf => f m pf)) = f i pf.
Proof.
  rewrite vector_nth_create.
  apply vector_create_fun_simple_ext.
  lia.
Qed.

Lemma vector_create_nth {T} {n} (v:vector T n) :
  vector_create 0 n (fun i _ pf => vector_nth i pf v) = v.
Proof.
  apply vector_nth_eq; intros.
  now rewrite vector_nth_create'.
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

(* move this *)
Lemma nth_error_combine {A B} (x:list A) (y:list B) i :
  match nth_error (combine x y) i with
  | Some (a,b) => nth_error x i = Some a /\
                  nth_error y i = Some b
  | None => nth_error x i = None \/
            nth_error y i = None
  end.
Proof.
  revert i y.
  induction x; simpl; intros i y.
  - destruct i; simpl; eauto.
  - destruct y; simpl.
    + destruct i; simpl; eauto.
    + destruct i; simpl; [eauto | ].
      apply IHx.
Qed.

Lemma vector_nth_zip {A B:Type}
      {n:nat} (x:vector A n) (y:vector B n) i pf : 
  vector_nth i pf (vector_zip x y) = (vector_nth i pf x, vector_nth i pf y).
Proof.
  unfold vector_nth, vector_zip, proj1_sig; simpl.
  repeat match_destr.
  simpl in *.
  destruct x; destruct y; simpl in *.
  specialize (nth_error_combine x x3 i).
  rewrite <- e.
  destruct x0.
  intros [??].
  congruence.
Qed.

Program Definition vector_fold_left {A B:Type} (f:A->B->A)
        {n:nat} (v:vector B n) (a0:A) : A
  := fold_left f v a0.

Lemma vector_zip_explode {A B} {n} (x:vector A n) (y:vector B n):
  vector_zip x y = vector_create 0 n (fun i _ pf => (vector_nth i pf x, vector_nth i pf y)).
Proof.
  apply vector_nth_eq; intros.
  rewrite vector_nth_create'.
  now rewrite vector_nth_zip.
Qed.

Lemma vector_nth_map {A B:Type}
      {n:nat} (f:A->B) (v:vector A n) i pf
  : vector_nth i pf (vector_map f v) = f (vector_nth i pf v).
Proof.
  unfold vector_nth, vector_map, proj1_sig.
  repeat match_destr.
  simpl in *.
  symmetry in e0.
  rewrite (map_nth_error _ _ _ e0) in e.
  congruence.
Qed.

Lemma vector_map_create {A B} (start len:nat) f (g:A->B) :
  vector_map g (vector_create start len f) = vector_create start len (fun x pf1 pf2 => g (f x pf1 pf2)).
Proof.
  apply vector_nth_eq; intros.
  rewrite vector_nth_map.
  now repeat rewrite vector_nth_create.
Qed.

Lemma vector_nth_const {T} n (c:T) i pf : vector_nth i pf (vector_const c n) = c.
Proof.
  unfold vector_const.
  now rewrite vector_nth_create.
Qed.


Lemma vector_nth_ext {T} {n} (v:vector T n) i pf1 pf2:
  vector_nth i pf1 v = vector_nth i pf2 v.
Proof.
  f_equal.
  apply le_uniqueness_proof.
Qed.

Lemma vector_nth_ext' {T} {n} (v1 v2 : vector T n) i pf1 pf2 :
  v1 = v2 -> vector_nth i pf1 v1 = vector_nth i pf2 v2.
Proof.
  intros Hv1v2.
  rewrite Hv1v2.
  apply vector_nth_ext.
Qed.

Lemma vector_map_const {A B} {n} (c:A) (f:A->B) : vector_map f (vector_const c n) = vector_const (f c) n.
Proof.
  apply vector_nth_eq; intros.
  rewrite vector_nth_map.
  now repeat rewrite vector_nth_const.
Qed.

Definition vectorize_relation {T:Type} (R:T->T->Prop) (n:nat) : vector T n -> vector T n -> Prop
  := fun v1 v2 => forall i pf, R (vector_nth i pf v1) (vector_nth i pf v2).

Global Instance vectorize_relation_refl {T:Type} (R:T->T->Prop) (n:nat) {refl:Reflexive R} : Reflexive (vectorize_relation R n).
Proof.
  intros ???.
  reflexivity.
Qed.

Global Instance vectorize_relation_sym {T:Type} (R:T->T->Prop) (n:nat) {sym:Symmetric R} : Symmetric (vectorize_relation R n).
Proof.
  intros ?????.
  now apply sym.
Qed.

Global Instance vectorize_relation_trans {T:Type} (R:T->T->Prop) (n:nat) {trans:Transitive R} : Transitive (vectorize_relation R n).
Proof.
  intros ???????.
  etransitivity; eauto.
Qed.

Global Instance vectorize_relation_equiv {T:Type} (R:T->T->Prop) (n:nat) {equiv:Equivalence R} : Equivalence (vectorize_relation R n).
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance vectorize_relation_pre {T:Type} (R:T->T->Prop) (n:nat) {pre:PreOrder R} : PreOrder (vectorize_relation R n).
Proof.
  constructor; typeclasses eauto.
Qed.

Global Instance vectorize_relation_part {T}
       (eqR preR:T->T->Prop) (n:nat) {R_equiv:Equivalence eqR} {R_pre:PreOrder preR} {R_part:PartialOrder eqR preR}:
    PartialOrder (vectorize_relation eqR n) (vectorize_relation preR n).
Proof.
  split ; intros HH.
  - repeat red.
    split
    ; intros ??; now apply R_part.
  - destruct HH.
    intros ??.
    apply R_part.
    split.
    + apply H.
    + apply H0.
Qed.

Global Instance vectorize_relation_equiv_dec {T:Type} (R:T->T->Prop) {eqR:Equivalence R} {eqdecR:EqDec T R} {n:nat}
  : EqDec (vector T n) (vectorize_relation R n).
Proof.
  repeat red.
  destruct x; destruct y; simpl.
  revert x x0 e e0.
  induction n; intros x y e1 e2.
  - left.
    intros ??; lia.
  - destruct x; try discriminate.
    destruct y; try discriminate.
    destruct (eqdecR t t0).
    + simpl in *.
      assert (pfx: (length x = n)%nat) by lia.
      assert (pfy: (length y = n)%nat) by lia.
      destruct (IHn x y pfx pfy).
      * left.
        intros ??.
        unfold vector_nth, proj1_sig.
        repeat match_destr.
        simpl in *.
        destruct i; simpl in *.
        -- invcs e3.
           invcs e4.
           trivial.
        -- assert (pf2:(i < n)%nat) by lia.
           specialize (e0 i pf2).
           unfold vector_nth, proj1_sig in e0.
           repeat match_destr_in e0.
           simpl in *.
           congruence.
      * right.
        intros HH.
        apply c.
        intros i pf.
        assert (pf2:(S i < S n)%nat) by lia.
        specialize (HH (S i) pf2).
        unfold vector_nth, proj1_sig in *.
        repeat match_destr_in HH.
        repeat match_destr.
        simpl in *.
        congruence.
    + right.
      intros HH.
      red in HH.
      assert (pf1:(0 < S n)%nat) by lia.
      specialize (HH 0%nat pf1).
      unfold vector_nth in HH; simpl in HH.
      apply c.
      apply HH.
Defined.

Global Instance vector_eq_dec {T:Type} {eqdecR:EqDec T eq} {n:nat}
  : EqDec (vector T n) eq.
Proof.
  intros x y.
  destruct (vectorize_relation_equiv_dec eq x y).
  - left.
    unfold equiv in *.
    apply vector_nth_eq.
    apply e.
  - right.
    unfold equiv, complement in *.
    intros ?; subst.
    apply c.
    reflexivity.
Defined.

Program Definition vectoro_to_ovector {A} {n} (v:vector (option A) n) : option (vector A n)
  := match listo_to_olist v with
     | None => None
     | Some x => Some x
     end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply listo_to_olist_length in Heq_anonymous.
  now rewrite vector_length in Heq_anonymous.
Qed.

Lemma vector_to_ovector_proj1_sig {A} {n} (x:vector (option A) n) :
  listo_to_olist (proj1_sig x) = 
  match (vectoro_to_ovector x) with
  | None => None
  | Some x => Some (proj1_sig x)
  end.
Proof.
  intros; destruct x; simpl; subst.
  unfold vectoro_to_ovector; simpl.
  generalize ((@eq_refl (option (list A)) (@listo_to_olist A x))).

  cut(forall o, forall e : o = listo_to_olist x,
             o =
             match
               match
                 o as anonymous' return (anonymous' = listo_to_olist x -> option (vector A (length x)))
               with
               | Some x0 =>
                 fun Heq_anonymous : Some x0 = listo_to_olist x =>
                   Some
                     (exist (fun l : list A => length l = length x) x0
                            (DVector.vectoro_to_ovector_obligation_1 A (length x)
                                                                     (exist (fun l : list (option A) => length l = length x) x eq_refl) x0 Heq_anonymous))
    | None => fun _ : None = listo_to_olist x => None
               end e
             with
             | Some x0 => Some (proj1_sig x0)
             | None => None
             end); trivial.
  intros.
  destruct o; trivial.
Qed.

Lemma vectoro_to_ovector_some_eq {A} {n} (v1:vector (option A) n) (v2:vector A n) :
      vectoro_to_ovector v1 = Some v2 <->
      listo_to_olist (proj1_sig v1) = Some (proj1_sig v2).
  Proof.
    rewrite vector_to_ovector_proj1_sig.
    match_destr; [| intuition congruence].
    - split; intros HH; invcs HH; trivial.
      apply vector_eq in H0; congruence.
  Qed.

Definition vector_list {A} (l:list A) : vector A (length l)
  := exist _ l (eq_refl _).

Definition Forall_vectorize {T} {n} (l:list (list T)) 
           (flen:Forall (fun x => length x = n) l) : list (vector T n)
  := list_dep_zip l flen.

Lemma Forall_vectorize_length {T} {n} (l:list (list T)) 
      (flen:Forall (fun x => length x = n) l) :
  length (Forall_vectorize l flen) = length l.
Proof.
  apply list_dep_zip_length.
Qed.

Program Definition vector_dep_zip {T} {n} {P:T->Prop} (v:vector T n)
  : Forall P (proj1_sig v) -> vector (sig P) n
  := fun ff => exist _ (list_dep_zip _ ff) _.
Next Obligation.
  now rewrite list_dep_zip_length, vector_length.
Qed.

Lemma Forall_vectorize_in {T} {n} (l:list (list T)) 
      (flen:Forall (fun x => length x = n) l) (x:vector T n) :
  In x (Forall_vectorize l flen) <-> In (proj1_sig x) l.
Proof.
  rewrite <- (list_dep_zip_map1 l flen) at 2.
  rewrite in_map_iff.
  split; intros.
  - eauto.
  - destruct H as [? [??]].
    apply vector_eq in H.
    now subst.
Qed.

Program Definition vector_list_product {n} {T} (l:vector (list T) n)
  : list (vector T n)
  := Forall_vectorize (list_cross_product l) _.
Next Obligation.
  destruct l.
  subst.
  apply list_cross_product_inner_length.
Qed.

Program Lemma vector_list_product_length {n} {T} (lnnil:n <> 0) (l:vector (list T) n) :
  length (vector_list_product l) = fold_left Peano.mult (vector_map (@length T) l) 1%nat.
Proof.
  unfold vector_list_product.
  rewrite Forall_vectorize_length.
  rewrite list_cross_product_length; simpl; trivial.
  destruct l; simpl.
  destruct x; simpl in *; congruence.
Qed.

Program Lemma vector_list_product_in_iff {n} {T} (lnnil:n <> 0) (l:vector (list T) n) (x:vector T n):
  In x (vector_list_product l) <-> Forall2 (@In T) x l.
Proof.
  unfold vector_list_product.
  rewrite Forall_vectorize_in.
  apply list_cross_product_in_iff.
  destruct l; simpl.
  destruct x0; simpl in *; congruence.
Qed.


Program Lemma Forallt_vector {A} {P:A->Type} {n:nat} (l:vector A n) :
  (forall i pf, P (vector_nth i pf l)) ->
  Forallt P l.
Proof.
  destruct l; simpl; subst.
  induction x; simpl; intros.
  - constructor.
  - constructor.
    + apply (X 0%nat ltac:(lia)).
    + apply IHx; intros.
      specialize (X (S i) (ltac:(lia))).
      unfold vector_nth, proj1_sig in *.
      match_destr.
      match_destr_in X.
      simpl in *.
      congruence.
Defined.

Program Lemma Forall_vector {A} {P:A->Prop} {n:nat} (l:vector A n)
  : (forall i pf, P (vector_nth i pf l)) ->
    Forall P l.
Proof.
  destruct l; simpl; subst.
  induction x; simpl; intros.
  - constructor.
  - constructor.
    + apply (H 0%nat ltac:(lia)).
    + apply IHx; intros.
      specialize (H (S i) (ltac:(lia))).
      unfold vector_nth, proj1_sig in *.
      match_destr.
      match_destr_in H.
      simpl in *.
      congruence.
Defined.

Program Lemma vector_Forall {A} {P:A->Prop} {n:nat} (l:vector A n)
  : Forall P l -> (forall i pf, P (vector_nth i pf l)).
Proof.
  intros.
  rewrite Forall_forall in H.
  apply H.
  apply vector_nth_In.
Qed.



Lemma vector_nthS {A} a i (l:list A) pf1 pf2 :
  (vector_nth (S i) pf1
              (exist (fun l0 : list A => length l0 = S (length l)) (a :: l) pf2))
  = vector_nth i (lt_S_n _ _ pf1) (exist (fun l0 : list A => length l0 = length l) (l) (eq_add_S _ _ pf2)).
Proof.
  unfold vector_nth, proj1_sig.
  repeat match_destr.
  simpl in *.
  congruence.
Qed.

Program Definition vector_append {A} {n1} (l1:vector A n1) {n2} (l2:vector A n2) : vector A (n1 + n2)
  := l1 ++ l2.
Next Obligation.
  destruct l1; destruct l2; simpl.
  rewrite app_length.
  congruence.
Qed.

Lemma vector_map_map {A B C} {n} (f:B->C) (g:A->B) (v:vector A n) :
  vector_map f (vector_map g v) = vector_map (fun x => f (g x)) v.
Proof.
  apply vector_ext; simpl.
  apply map_map.
Qed.

Program Lemma vector_map_ext' {A B} {n} (f g:A->B) (v:vector A n) :
  (forall x, In x v -> f x = g x) ->
  vector_map f v = vector_map g v.
Proof.
  intros.
  apply vector_ext; simpl.
  apply map_ext_in; auto.
Qed.

Lemma vector_map_ext {A B} {n} (f g:A->B) (v:vector A n) :
  (forall i pf, f (vector_nth i pf v) = g (vector_nth i pf v)) ->
  vector_map f v = vector_map g v.
Proof.
  intros.
  apply vector_map_ext'; intros ? inn.
  apply In_vector_nth_ex in inn.
  destruct inn as [?[??]]; subst.
  auto.
Qed.

Lemma proj1_sig_vector_map {A B} {n} (f:A->B) (v:vector A n) :
  proj1_sig (vector_map f v) = map f (proj1_sig v).
Proof.
  reflexivity.
Qed.

Lemma proj1_sig_vector_map_onto {A B} {n} (v:vector A n) (f:forall a, In a (proj1_sig v) -> B) :
  proj1_sig (vector_map_onto v f) = map_onto (proj1_sig v) f.
Proof.
  reflexivity.
Qed.

Lemma vector_dep_zip_map1 {T : Type} {P : T -> Prop} {n} (l : vector T n) (Fp : Forall P (proj1_sig l)) :
  vector_map (proj1_sig (P:=P)) (vector_dep_zip l Fp) = l.
Proof.
  apply vector_eq.
  unfold vector_dep_zip.
  unfold vector_map; simpl.
  now rewrite list_dep_zip_map1.
Qed.      

Lemma vector_dep_zip_nth_proj1 {T} {n} {P:T->Prop} (v:vector T n)
      (fl:Forall P (proj1_sig v)) :
  forall i pf,
    proj1_sig (vector_nth i pf (vector_dep_zip v fl)) =
      vector_nth i pf v.
Proof.
  intros.
  rewrite <- (vector_nth_map (@proj1_sig _ _)).
  now rewrite vector_dep_zip_map1.
Qed.


Definition vector_apply {n} {A B} (f : vector (A -> B) n)  (x : vector A n) : vector B n
  := vector_map (fun '(a,b) => a b) (vector_zip f x).

Lemma vector_nth_apply {n} {A B} (f : vector (A -> B) n)  (x : vector A n) i pf :
  vector_nth i pf (vector_apply f x) = (vector_nth i pf f) (vector_nth i pf x).
Proof.
  unfold vector_apply.
  now rewrite vector_nth_map, vector_nth_zip.
Qed.

Lemma vector_apply_const {n} {A B} (f: A->B) (a:vector A n) : vector_apply (vector_const f n) a = vector_map f a.
Proof.
  apply vector_nth_eq; intros.
  now rewrite vector_nth_apply, vector_nth_map, vector_nth_const.
Qed.

Program Definition vector_cons {n} {A} (x:A) (v:vector A n) : vector A (S n)
  := exist _ (x::proj1_sig v) _.
Next Obligation.
  destruct v; simpl; congruence.
Defined.

Definition vector_singleton {A} (x:A) : vector A 1%nat
  := vector_cons x vector0.

Program Definition vector_add_to_end {n} {A} (x:A) (v:vector A n) : vector A (S n)
  := exist _ (proj1_sig v ++ x::nil) _.
Next Obligation.
  destruct v; simpl.
  rewrite app_length; simpl.
  rewrite e.
  rewrite Nat.add_1_r.
  congruence.
Defined.

Lemma vector_nth_singleton {A} (x:A) i pf : vector_nth i pf (vector_singleton x) = x.
Proof.
  destruct i; [| lia].
  reflexivity.
Qed.

Lemma vector_nth_add_to_end_prefix {n} {A} (x:A) (v:vector A n) i pf (pf2:(i<n)%nat):
  vector_nth i pf (vector_add_to_end x v) = vector_nth i pf2 v.
Proof.
  generalize (vector_nth_in i pf (vector_add_to_end x v)); intros HH1.
  generalize (vector_nth_in i pf2 v); intros HH2.
  cut ( nth_error (proj1_sig (vector_add_to_end x v)) i = nth_error (proj1_sig v) i)
  ; [congruence | ].
  simpl.
  rewrite nth_error_app1; trivial.
  now rewrite vector_length.
Qed.

Lemma vector_nth_add_to_end_suffix {n} {A} (x:A) (v:vector A n) pf :
  vector_nth n pf (vector_add_to_end x v) = x.
Proof.
  generalize (vector_nth_in n pf (vector_add_to_end x v)); intros HH1.
  simpl in HH1.
  rewrite nth_error_app2 in HH1.
  - rewrite vector_length, Nat.sub_diag in HH1.
    simpl in HH1.
    congruence.
  - rewrite vector_length; reflexivity.
Qed.

Section ivector.

  Fixpoint ivector (T:Type) (n:nat) : Type :=
    match n with
    | 0%nat => unit
    | S m => prod T (ivector T m)
    end.

  Fixpoint ivector_const {T:Type} (n:nat) (v:T) : ivector T n :=
    match n with
    | 0%nat => tt
    | S m => (v, ivector_const m v)
    end.

    Fixpoint ivector_nth {T:Type} {n:nat} (idx:nat): (idx < n)%nat -> ivector T n -> T :=
    match n with
    | 0%nat => fun pf _ => False_rect _ (Nat.nlt_0_r _ pf)
    | S n' => match idx with
             | 0%nat => fun pf '(hd,tl) => hd
             | S m' => fun pf '(hd,tl) => ivector_nth m' (lt_S_n _ _ pf) tl
             end
    end.

   Lemma ivector_nth_prf_irrelevance {T} (n : nat) (vec : ivector T n) index pf1 pf2 :
     ivector_nth index pf1 vec = ivector_nth index pf2 vec.
   Proof.
     f_equal.
     apply le_uniqueness_proof.
   Qed.

   Lemma ivector_nth_ext {T} {n} (v1 v2 : ivector T n) i pf1 pf2 :
     v1 = v2 -> ivector_nth i pf1 v1 = ivector_nth i pf2 v2.
   Proof.
     intros Hv1v2.
     rewrite Hv1v2.
     apply ivector_nth_prf_irrelevance.
   Qed.

   Lemma ivector_nth_ext' {T} {n} (v1 v2 : ivector T n) i1 i2 pf1 pf2 :
     i1 = i2 ->
     v1 = v2 -> 
     ivector_nth i1 pf1 v1 = ivector_nth i2 pf2 v2.
   Proof.
     intros Hi1i2 Hv1v2.
     rewrite Hv1v2.
     destruct Hi1i2.
     apply ivector_nth_prf_irrelevance.
   Qed.

  Fixpoint ivector_take {T:Type} (n:nat) (idx:nat): (idx <= n)%nat -> ivector T n -> ivector T idx :=
    match n with
    | 0%nat => match idx with
            | 0%nat => fun _ _ => tt
            | _ => fun pf _ => False_rect _ (Nat.nle_succ_0 _ pf)
            end
    | S n' => match idx with
             | 0%nat => fun pf '(hd,tl) => tt
             | S m' => fun pf '(hd,tl) => (hd, ivector_take n' m' (le_S_n _ _ pf) tl)
             end
    end.

  Lemma ivector_take_const {T} (x:T) n m lt :
    ivector_take m n lt (ivector_const m x) = ivector_const n x.
  Proof.
    revert n lt.
    induction m; simpl; intros.
    - now destruct n; [| lia]; simpl.
    - destruct n; [simpl; trivial |].
      now rewrite IHm with (lt:=le_S_n n m lt); simpl.
  Qed.


  Lemma ivector_take_0 {T} {n} pf (ivec : ivector T n) :
    ivector_take n 0 pf ivec = tt.
    Proof.
      induction n.
      - now simpl.
      - simpl.
        now destruct ivec.
    Qed.
    
    Fixpoint ivector_append {T} {n1 n2} : ivector T n1 -> ivector T n2 -> ivector T (n1 + n2) :=
     match n1 as n1' return ivector T n1' -> ivector T n2 -> ivector T (n1' + n2) with
     | 0%nat => fun _ v2 => v2
     | S n%nat => fun '(hd,tail) v2 => (hd, ivector_append tail v2)
     end.

  Fixpoint ivector_map {A B} {n} (f : A -> B ) : ivector A n -> ivector B n
    := match n with
       | 0%nat => fun _ => tt
       | S _ =>
           fun '(hd,tl) => (f hd, ivector_map f tl)
       end.

  Lemma ivector_map_const {n} {A B} (f : A -> B) (a : A) :
    ivector_map f (ivector_const n a) = ivector_const n (f a).
  Proof.
    induction n.
    - now simpl.
    - simpl.
      f_equal.
      apply IHn.
  Qed.

  Fixpoint ivector_zip {A B} {n} : ivector A n -> ivector B n -> ivector (A*B) n
    := match n with
       | 0%nat => fun _ _ => tt
       | S _ =>
           fun '(hd1,tl1) '(hd2,tl2) => ((hd1,hd2), ivector_zip tl1 tl2)
       end.

    Lemma ivector_nth_zip {T} {n} (x1 x2 : ivector T n) i pf :
      ivector_nth i pf (ivector_zip x1 x2) = (ivector_nth i pf x1, ivector_nth i pf x2).
    Proof.
      revert i pf x1 x2.
      induction n; try lia.
      destruct x1; destruct x2.
      simpl.
      match_destr.
    Qed.

  Fixpoint ivector_fold_left {A} {n} {T} (f : A -> T -> A) : ivector T n -> A -> A
    := match n with
       | 0%nat => fun _ acc => acc
       | S _ =>
           fun '(hd,tl) acc => ivector_fold_left f tl (f acc hd)
       end.

  Fixpoint ivector_fold_right {A} {n} {T} (f : T -> A -> A) (init:A) : ivector T n -> A
    := match n with
       | 0%nat => fun _ => init
       | S _ =>
           fun '(hd,tl) => f hd (ivector_fold_right f init tl)
       end.

  Fixpoint ivector_Forall2 {A B} {n} (R:A->B->Prop): ivector A n -> ivector B n -> Prop
    := match n with
       | 0%nat => fun _ _ => True
       | S _ => fun '(hd1,tl1) '(hd2,tl2) =>
                 R hd1 hd2 /\ ivector_Forall2 R tl1 tl2
       end.

  Global Instance ivector_Forall2_refl {A} {n} (R:A->A->Prop) {refl:Reflexive R} : Reflexive (ivector_Forall2 (n:=n) R).
  Proof.
    red.
    induction n; simpl; trivial.
    intros [??]; auto.
  Qed.

  Global Instance ivector_Forall2_sym {A} {n} (R:A->A->Prop) {sym:Symmetric R} : Symmetric (ivector_Forall2 (n:=n) R).
  Proof.
    red.
    induction n; simpl; trivial.
    intros [??][??]; firstorder.
  Qed.

  Global Instance ivector_Forall2_trans {A} {n} (R:A->A->Prop) {trans:Transitive R} : Transitive (ivector_Forall2 (n:=n) R).
  Proof.
    red.
    induction n; simpl; trivial.
    intros [??][??][??]; firstorder.
  Qed.

  Global Instance ivector_Forall2_equiv {A} {n} (R:A->A->Prop) {trans:Equivalence R} : Equivalence (ivector_Forall2 (n:=n) R).
  Proof.
    constructor; typeclasses eauto.
  Qed.
  
  Global Instance ivector_Forall2_pre {A} {n} (R:A->A->Prop) {trans:PreOrder R} : PreOrder (ivector_Forall2 (n:=n) R).
  Proof.
    constructor; typeclasses eauto.
  Qed.

  Global Instance ivector_Forall2_part {A} {n} (eqA:A->A->Prop) {equivA:Equivalence eqA} (R:A->A->Prop) {preo:PreOrder R} {part:PartialOrder eqA R} : PartialOrder (ivector_Forall2 (n:=n) eqA) (ivector_Forall2 (n:=n) R).
  Proof.
    repeat red.
    unfold relation_conjunction, predicate_intersection, pointwise_extension, flip.
    induction n; simpl; [tauto |].
    intros [??][??].
    firstorder.
  Qed.

  Fixpoint ivector_Forall {A} {n} (P:A->Prop): ivector A n -> Prop
    := match n with
       | 0%nat => fun _ => True
       | S _ => fun '(hd,tl) =>
                 P hd /\ ivector_Forall P tl
       end.
  
  Lemma ivector_Forall2_Forall_zip  {A B} {n} (R:A->B->Prop) (v1:ivector A n) (v2:ivector B n) :
    ivector_Forall2 R v1 v2 <-> ivector_Forall (fun '(a,b) => R a b) (ivector_zip v1 v2).
  Proof.
    revert v1 v2.
    induction n; simpl; [tauto |].
    intros [??] [??].
    now rewrite IHn.
  Qed.

  Lemma ivector_Forall2_eq {A} {n} (vec1 vec2 : ivector A n) :
    ivector_Forall2 (fun (a1 a2 : A) => a1 = a2) vec1 vec2 <->
    vec1 = vec2.
  Proof.
    intros.
    induction n; destruct vec1; destruct vec2.
    - simpl.
      tauto.
    - split; intros HH; invcs HH.
      + assert (i = i0).
        {
          apply IHn.
          apply H0.
        }
        now rewrite H.
      + now apply ivector_Forall2_refl.
  Qed.

  

  Fixpoint ivector_from_list {A} (l : list A) : ivector A (length l)
    := match l with
       | nil => tt
       | a :: l' => (a, ivector_from_list l')
       end.

  Fixpoint ivector_to_list {A} {n} : ivector A n -> list A 
    := match n with
       | 0%nat => fun _ => nil
       | S _ => fun '(hd,tl) => hd::(ivector_to_list tl)
       end.

  Lemma ivector_to_list_from_list {A} (l:list A) : ivector_to_list (ivector_from_list l) = l.
  Proof.
    induction l; simpl; congruence.
  Qed.

  Lemma ivector_to_list_length {A} {n} (v:ivector A n) : length (ivector_to_list v) = n.
  Proof.
    induction n; simpl; trivial.
    destruct v; simpl; auto.
  Qed.

  Definition ivector_hd {A} {n} (vec : ivector A (S n)) : A :=
    (fun '(hd, tl) => hd) vec.
    
  Definition ivector_tl {A} {n} (vec : ivector A (S n)) : ivector A n :=
    (fun '(hd, tl) => tl) vec.
  
  Definition ivector_cons {n} {T} (x : T) (v : ivector T n) : ivector T (S n) :=
    (x, v).

  Lemma ivector_hd_take {T} {n idx} pf (ivec : ivector T (S n)) :
    ivector_hd (ivector_take (S n) (S idx) pf ivec) = ivector_hd ivec.
  Proof.
    destruct ivec.
    now simpl.
  Qed.

  Lemma ivector_tl_take {T} {n idx} pf (ivec : ivector T (S n)) :
    ivector_tl (ivector_take (S n) (S idx) pf ivec) =
    ivector_take n idx (le_S_n idx n pf) (ivector_tl ivec).
  Proof.
    destruct ivec.
    now simpl.
  Qed.

  Lemma ivector_eq2 {A} {n} (vec1 vec2 : ivector A (S n)) :
    vec1 = vec2 <-> ivector_hd vec1 = ivector_hd vec2 /\ ivector_tl vec1 = ivector_tl vec2.
  Proof.
    destruct vec1; destruct vec2.
    split; intros.
    - invcs H.
      tauto.
    - simpl in H.
      destruct H.
      now rewrite H, H0.
   Qed.

  
  Lemma ivector_Forall2_nth_iff {A B} {n} (P:A->B->Prop) (v1:ivector A n) (v2:ivector B n) :
  (forall (i : nat) (pf : (i < n)%nat), P (ivector_nth i pf v1) (ivector_nth i pf v2)) <->
    ivector_Forall2 P v1 v2.
  Proof.
    split; revert v1 v2.
    - induction n; simpl; trivial; intros.
      destruct v1; destruct v2.
      split.
      + specialize (H 0 ((Nat.lt_0_succ _))).
        apply H.
      + apply IHn; intros.
        specialize (H (S i1) ( (lt_n_S _ _ pf))).
        simpl in H.
        rewrite (ivector_nth_prf_irrelevance _ i _ _ pf) in H.
        now rewrite (ivector_nth_prf_irrelevance _ i0 _ _ pf) in H.
    - induction n; simpl; intros; [lia |].
      destruct v1; destruct v2; destruct H.
      destruct i; auto.
  Qed.

Lemma ivector_nth_eq {T} {n} (v1 v2:ivector T n) :
  (forall i pf, ivector_nth i pf v1 = ivector_nth i pf v2) ->
  v1 = v2.
Proof.
  intros.
  apply ivector_Forall2_eq.
  now apply ivector_Forall2_nth_iff.
Qed.

  Lemma ivector_nth_map {A B:Type}
      {n:nat} (g:A->B) (v:ivector A n) i pf
  : ivector_nth i pf (ivector_map g v) = g (ivector_nth i pf v).
  Proof.
    revert v i pf.
    induction n; simpl; intros; [lia |].
    destruct v.
    destruct i; trivial.
  Qed.

   Fixpoint ivector_create {B} n : (forall i (pf:(i<n)%nat), B) -> ivector B n
    := match n as n' return  (forall i (pf:(i<n')%nat), B) -> ivector B n' with
       | 0%nat => fun _ => tt
       | S m =>
           fun f => (f 0%nat (Nat.lt_0_succ _) , ivector_create m (fun i pf => f (S i) (lt_n_S _ _ pf)))
       end.

  Lemma ivector_nth_from_list {A} 
        (l : list A) (i : nat) (pf : (i < length l)%nat):
    nth_error l i = Some (ivector_nth i pf (ivector_from_list l)).
  Proof.
    revert i pf.
    induction l; simpl in *; [lia |].
    destruct i; simpl; trivial.
  Qed.

  Lemma ivector_vector_nth_from_list {A} 
        (l : list A) (i : nat) (pf : (i < length l)%nat):
    ivector_nth i pf (ivector_from_list l) =
    vector_nth i pf (vector_list l).
  Proof.
    generalize (vector_nth_in i pf (vector_list l)); simpl.
    rewrite (ivector_nth_from_list l i pf).
    congruence.
  Qed.

  Lemma ivector_nth_const {T} n (c:T) i pf : ivector_nth i pf (ivector_const n c) = c.
  Proof.
    revert i pf.
    induction n.
    - now simpl.
    - intros; simpl.
      match_destr.
  Qed.

  Lemma ivec_nth_cons {T} {n} (x : ivector T n) (val : T) (x0 : nat) (l : (S x0 < S n)%nat) :
    ivector_nth (S x0) l (val, x) = ivector_nth x0 (le_S_n _ _ l) x.
  Proof.
    destruct n.
    - lia.
    - simpl.
      match_destr.
      match_destr.
      now apply ivector_nth_ext.
  Qed.

  Lemma ivector_take_cons {T} {N} (n : nat) (v : ivector T N)(val : T) 
        (le : (S n <= S N)%nat) :
    ivector_take (S N) (S n) le (val, v) = 
    (val, ivector_take N n (le_S_n _ _ le) v).
  Proof.
    apply ivector_eq2.
    now simpl.
  Qed.

  Definition vector_to_ivector {A} {n} (vec : vector A n) : ivector A n .
  Proof.
    destruct vec.
    pose (v := ivector_from_list x).
    rewrite e in v.
    exact v.
  Defined.

  Fixpoint ivector_to_vector {A} {n} : ivector A n -> vector A n :=
    match n with
    | 0%nat => fun _ => vector0
    | S n' => fun '(hd,tl) => vector_cons hd (ivector_to_vector tl)
    end.

  Lemma vector_to_ivector_nth {A} {n} (vec : vector A n) i pf :
    vector_nth i pf vec = ivector_nth i pf (vector_to_ivector vec).
  Proof.
    unfold vector_to_ivector.
    destruct vec.
    unfold eq_rect.
    match_destr.
    unfold vector_nth, proj1_sig, vector_nth_packed.
    simpl.
    match_destr.
    rewrite (ivector_nth_from_list _ i pf) in e.
    now invcs e.
  Qed.
    
  Lemma vector_nth_cons_0 {A} {n} a (vec : vector A n) pf :
    vector_nth 0 pf (vector_cons a vec) = a.
  Proof.
    unfold vector_cons, vector_nth.
    now simpl.
  Qed.

  Lemma vector_nth_cons_S {A} {n} a (vec : vector A n) i pf :
    vector_nth (S i) pf (vector_cons a vec) = 
    vector_nth i (lt_S_n i n pf) vec.
  Proof.
    unfold vector_cons, vector_nth, proj1_sig.
    destruct vec.
    match_destr.
    match_destr.
    unfold proj1_sig in *.
    simpl in e0.
    rewrite <- e1 in e0.
    now invcs e0.
  Qed.

  Lemma ivector_to_vector_nth {A} {n} (ivec : ivector A n) i pf :
    ivector_nth i pf ivec = vector_nth i pf (ivector_to_vector ivec).
  Proof.
    unfold ivector_to_vector.
    revert i pf.
    induction n.
    - lia.
    - intros.
      destruct ivec.
      destruct i.
      + simpl.
        now rewrite vector_nth_cons_0.
      + rewrite vector_nth_cons_S.
        simpl.
        apply IHn.
   Qed.

  Program Instance vec_to_ivec_encoder {A} {n} :
    Isomorphism (vector A n) (ivector A n)
    := {
    iso_f := vector_to_ivector;
    iso_b := ivector_to_vector }.
  Next Obligation.
    apply ivector_nth_eq.
    intros.
    rewrite <- vector_to_ivector_nth.
    now rewrite ivector_to_vector_nth.
  Qed.
  Next Obligation.
    apply vector_nth_eq.
    intros.
    rewrite <- ivector_to_vector_nth.
    now rewrite vector_to_ivector_nth.
  Qed.

    Fixpoint ivector_add_to_end {n : nat} {T : Type} (x:T) : ivector T n -> ivector T (S n)
    := match n with
       | 0%nat => fun _ => (x, tt)
       | S n => fun '(hd,tl) => (hd, ivector_add_to_end x tl)
       end.

  Fixpoint ivector_rev {n : nat} {T : Type} : ivector T n -> ivector T n
    := match n with
       | 0%nat => fun _ => tt
       | S n => fun '(hd,tl) => ivector_add_to_end hd (ivector_rev tl)
       end.

  Lemma ivector_rev_add_to_end {n : nat} {T : Type} x (v:ivector T n) :
    ivector_rev (ivector_add_to_end x v) = (x, ivector_rev v).
  Proof.
    revert x.
    induction n; [simpl; trivial; intros |].
    intros.
    destruct v.
    replace (ivector_rev (ivector_add_to_end (n:=S n) x (t, i))) with
      (ivector_add_to_end t (ivector_rev (ivector_add_to_end x i))) by reflexivity.
    now rewrite IHn.
  Qed.
    
  Lemma ivector_rev_involutive {n : nat} {T : Type} (v:ivector T n) :
    ivector_rev (ivector_rev v) = v.
  Proof.
    induction n; [destruct v; simpl; trivial |].
    destruct v.
    replace (ivector_rev (ivector_rev (n:=S n) (t, i))) with
      (ivector_rev (ivector_add_to_end t (ivector_rev i))) by reflexivity.
    now rewrite ivector_rev_add_to_end, IHn.
  Qed.

  Lemma ivector_const_add_to_end {T} n (a:T) :
    ivector_add_to_end a (ivector_const n a) = (a, ivector_const n a).
  Proof.
    induction n; simpl; trivial.
    now rewrite IHn.
  Qed.
    
  Lemma ivector_rev_const {T} n (a:T) : ivector_rev (ivector_const n a) = ivector_const n a.
  Proof.
    induction n; simpl; trivial.
    now rewrite IHn, ivector_const_add_to_end.
  Qed.
  Lemma ivector_rev_ind {i} {n} :
  i < n -> (n - S i) < n.
Proof.
  lia.
Qed.

Lemma ivector_nth_add_to_end1  {T} {n} i pf t (v : ivector T n) (pf2:i < n):
  ivector_nth i pf (ivector_add_to_end t v) = ivector_nth i pf2 v.
Proof.
  revert i pf pf2.
  induction n; simpl; intros; [lia |].
  destruct i; destruct v; trivial.
  apply IHn.
Qed.

Lemma ivector_nth_add_to_end2  {T} {n} pf t (v : ivector T n):
  ivector_nth n pf (ivector_add_to_end t v) = t.
Proof.
  induction n; simpl; trivial.
  destruct v.
  apply IHn.
Qed.

Lemma ivector_nth_rev {T} {n} (v : ivector T n) :
  forall i pf,
    ivector_nth i pf (ivector_rev v) = 
    ivector_nth (n - S i) (ivector_rev_ind pf) v.
Proof.
  induction n; intros.
  - now simpl.
  - destruct v; simpl ivector_rev.
    destruct (i == n); unfold equiv, complement in *.
    + subst.
      rewrite ivector_nth_add_to_end2.
      assert (eqq:(S n - S n = 0)%nat) by lia.
      generalize (ivector_rev_ind pf).
      now rewrite eqq.
    + assert (pf2:(i < n)%nat) by lia.
      rewrite (ivector_nth_add_to_end1 _ _ _ _ pf2).
      rewrite IHn.
      assert (eqq:S n - S i = S (n - S i)) by lia.
      generalize (ivector_rev_ind pf).
      rewrite eqq; simpl; intros.
      now apply ivector_nth_ext.
Qed.    

  Lemma ivector_nth_create
    {T : Type}
    (len : nat)
    (i : nat)
    (pf2: i < len)
    (f:(forall m, m < len -> T)%nat) :
    ivector_nth i pf2 (ivector_create len f) = f i pf2.
  Proof.
    revert i pf2.
    induction len; simpl; intros; try lia.
    match_destr.
    - now rewrite (digit_pf_irrel _ _ _ pf2).
    - rewrite IHlen.
      f_equal; apply digit_pf_irrel.
  Qed.
  
End ivector.
Section Sequence.
    Fixpoint sequence_to_ivector {T} (x : nat -> T) j h : ivector T h
    := match h with
       | 0 => tt
       | S n => (x j, sequence_to_ivector x (S j) n)
       end.

  Definition sequence_cons {T} (x : T) (xs : nat -> T) : nat -> T :=
    fun n0 =>
      match n0 with
      | 0 => x
      | S n => xs n
      end.

  Definition ivector_to_sequence {T} {n} (v : ivector T n) (default : T) 
    : nat -> T :=
    (fun i => 
       match lt_dec i n with
       | left pf => ivector_nth i pf v
       | right _ => default
       end).

   Lemma sequence_to_ivector_cons_shift {T} {n} (j : nat) (x : nat -> T) (val : T) :
     sequence_to_ivector (sequence_cons val x) (S j) n = sequence_to_ivector x j n.
   Proof.
     revert j.
     induction n.
     - intros.
       now simpl.
     - intros.
       simpl.
       f_equal.
       apply IHn.
   Qed.

   Lemma sequence_to_ivector_cons {T} {n} (x : nat -> T) (val : T) :
    sequence_to_ivector (sequence_cons val x) 0%nat (S n) =
    (val, sequence_to_ivector x 0%nat n).
  Proof.
    apply ivector_eq2.
    split.
    - now simpl.
    - apply sequence_to_ivector_cons_shift.
  Qed.


  Lemma ivec_sequence_cons {T} {n} (x : ivector T n) (val : T) (default : T) :
    ivector_to_sequence (n := S n) (val, x) default =
    sequence_cons val (ivector_to_sequence x default).
  Proof.
    apply FunctionalExtensionality.functional_extensionality.
    destruct x0.
    - simpl.
      unfold ivector_to_sequence.
      match_destr.
      lia.
    - simpl.
      unfold ivector_to_sequence.
      match_destr; try lia.
      match_destr; try lia.
      + rewrite ivec_nth_cons.
        now apply ivector_nth_ext.
      + match_destr; try lia.
  Qed.

  Lemma ivec_to_seq_to_ivec {T} {n} (v : ivector T n) (default : T)  :
    v = sequence_to_ivector (ivector_to_sequence v default) 0%nat n.
  Proof.
    induction n.
    - simpl.
      now destruct v.
    - destruct v.
      rewrite ivec_sequence_cons.
      rewrite sequence_to_ivector_cons.
      specialize (IHn i).
      now rewrite <- IHn.
   Qed.

  
  Lemma ivector_take_sequence {T} (x : nat -> T) (s n m : nat) 
        (lt : (n <= m)%nat) :
    sequence_to_ivector x s n =
    ivector_take m n lt (sequence_to_ivector x s m).
  Proof.
    revert n s lt.
    induction m; simpl; intros.
    - now destruct n; [| lia]; simpl.
    - destruct n; [simpl; trivial |].
      now rewrite <- IHm.
   Qed.


   Lemma sequence_to_ivector_shift {T} (x : nat -> T) (j N : nat) :
     sequence_to_ivector x (S j) N = sequence_to_ivector (fun n0 : nat => x (S n0)) j N.
   Proof.
     revert j.
     induction N.
     - now simpl.
     - intros.
       simpl.
       f_equal.
       now rewrite IHN.
   Qed.

   Lemma cons_sequence_to_ivector {T} (w : nat -> T) (x2 s : nat) :
     (w s, sequence_to_ivector w (S s) x2) = sequence_to_ivector w s (S x2).
   Proof.
     reflexivity.
   Qed.

   Lemma sequence_to_ivector_ext {T} (f g : nat -> T) start len :
     CMorphisms.pointwise_relation _ eq f g ->
     sequence_to_ivector f start len = sequence_to_ivector g start len.
   Proof.
     revert start.
     induction len; simpl; trivial; intros start eqq.
     now rewrite eqq, IHlen.
   Qed.


   Fixpoint sequence_prefix {T} (pre w : nat -> T) (N : nat) : nat -> T :=
      match N with
      | 0 => w
      | S n => sequence_cons (pre 0%nat) (sequence_prefix (fun n => pre (S n)) w n)
      end.
   
   Lemma sequence_prefix_ivector_append {T} (x1 x2 : nat -> T) (n1 n2 : nat) :
     sequence_to_ivector (sequence_prefix x1 x2 n1) 0 (n1 + n2)%nat =
     ivector_append (sequence_to_ivector x1 0 n1) (sequence_to_ivector x2 0 n2).
   Proof.
     revert x1 n2.
     induction n1; trivial; intros; simpl.
     rewrite sequence_to_ivector_cons_shift.
     f_equal.
     rewrite IHn1.
     f_equal.
     now rewrite sequence_to_ivector_shift.
   Qed.     

  Lemma sequence_to_ivector_Forall2 {T1 T2} (RR:T1->T2->Prop) (f:nat->T1) (g:nat->T2) s N :
    (forall n : nat, (s <= n <= N + s)%nat -> RR (f n) (g n)) ->
    ivector_Forall2 RR (sequence_to_ivector f s N) (sequence_to_ivector g s N).
  Proof.
    revert s.
    induction N; simpl; trivial; intros.
    split.
    - apply H; lia.
    - apply IHN.
      intros.
      apply H; lia.
  Qed.
  
  Lemma sequence_prefix_cons {T} (x x0 : nat -> T) (N : nat) :
    sequence_prefix x x0 (S N) =
    sequence_prefix x (sequence_cons (x N) x0) N.
  Proof.
    revert x x0.
    induction N.
    - now simpl.
    - intros.
      simpl.
      f_equal.
      now rewrite <- IHN.
  Qed.


  Lemma sequence_cons_prefix_shift {T} (x x0 : nat -> T) (N : nat) :
    sequence_cons (x 0%nat) 
                  (sequence_prefix (fun n => x (S n)) x0 N) =
    sequence_prefix x x0 (S N).
  Proof.
    easy.
  Qed.

  Lemma sequence_to_ivector_prefix {T} (x x0 : nat -> T) (N : nat) :
    sequence_to_ivector (sequence_prefix x x0 N) 0 N =
    sequence_to_ivector x 0 N.
  Proof.
    revert x.
    induction N; trivial; intros; simpl.    
    f_equal.
    rewrite sequence_to_ivector_cons_shift.
    rewrite IHN.
    now rewrite sequence_to_ivector_shift.
  Qed.     

  Lemma sequence_to_ivector_nth {T} (x : nat -> T) (idx idx2 s : nat) pf :
     x (idx + s)%nat  = ivector_nth idx pf (sequence_to_ivector x s idx2).
   Proof.
     revert idx pf s.
     induction idx2; intros.
     - lia.
     - rewrite <- cons_sequence_to_ivector.
       destruct idx.
       + now simpl.
       + rewrite ivec_nth_cons.
         rewrite <- IHidx2.
         f_equal.
         lia.
    Qed.

  Lemma ivector_to_sequence_nth  {T} (idx1 xx : nat)
        (default : T)
        (vec : ivector T (S xx)) 
        pf :
    ivector_to_sequence vec default idx1 = ivector_nth idx1 pf vec.
  Proof.
    unfold ivector_to_sequence.
    match_destr; try lia.
    apply ivector_nth_prf_irrelevance.
  Qed.

  Lemma sequence_to_ivector_take {T} (x1 xx : nat)
        (default : T)
        (vec : ivector T xx) 
        pf :
    sequence_to_ivector (ivector_to_sequence vec default) 0 x1 = 
    ivector_take xx x1 pf vec.
  Proof.
    revert x1 pf.
    induction xx.
    - intros.
      simpl.
      assert (x1 = 0)%nat by lia.
      destruct x1; try lia.
      now simpl.
    - intros.
      destruct vec.
      rewrite ivec_sequence_cons.
      specialize (IHxx i).
      destruct x1.
      + now simpl.
      + rewrite sequence_to_ivector_cons.
        specialize (IHxx x1 (le_S_n x1 xx pf)).
        rewrite IHxx.
        now simpl.
   Qed.

End Sequence.
