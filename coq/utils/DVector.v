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

(*
Program Lemma vector_nth_map_onto
  {A B:Type}
  {n:nat} (v:vector A n) (f:forall a, In a v->B)
  i
  (pf:i<n) :
  exists pfin, vector_nth i pf (vector_map_onto v f) = f (vector_nth i pf v) pfin.
Proof.
  unfold vector_map_onto.
  unfold vector_nth, proj1_sig.
  match_destr.
  simpl in *.
  destruct v; simpl.
  destruct x0; simpl in *; try lia.
  revert x x0 e e0 f.
  induction i; simpl; intros.
  - invcs e.
    eauto.
  - match_destr.
    simpl in *.
    assert (pfi:i < n) by lia.
    specialize (IHi pfi).
    specialize (

    specialize (

  
  cut (exists pfin, Some x = Some (f (let (a, _) := vector_nth_packed i pf v in a) (vector_nth_In v i pf)))
  ; [now intros; invcs H |].
  rewrite e; clear e.
  destruct v; simpl.
  subst.
  destruct x0; simpl in *; try lia.
  induction i.
  - simpl.
    unfold map_onto_oib
    repeat f_equal.
    
  
  


  
  
  match_destr.
  simpl in *.
  induction i; simpl.

Qed.
 *)

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
