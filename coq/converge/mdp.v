Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy Coquelicot.SF_seq.
Require Import pmf_monad Permutation fixed_point Finite LibUtils. 
Require Import Sums Coq.Reals.ROrderedType.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Equivalence RelationClasses EquivDec Morphisms.
Require Import Streams StreamAdd. 


Import ListNotations. 
Set Bullet Behavior "Strict Subproofs".


(*
****************************************************************************************
This file defines Markov Decision Processes (MDP) and proves various properties about 
them. Included are definitions of long-term values (LTVs), proofs that LTVs are convergent
and proofs that they satisfy the Bellman equation. 
We also include definitions of V* and proofs about them. The goal is to prove 
policy and value iteration algorithms correct. 
****************************************************************************************
*)
Import ListNotations. 

Section extra.
  (* 
     This section contains preliminary results which should go back into a Utils file.
     In their appropriate directories.
   *)
Open Scope list_scope. 
Lemma ne_symm {A} (x y : A) : x <> y <-> y <> x.
Proof.
  split; intros.
  * intros Hxy ; symmetry in Hxy ; firstorder.
  * intros Hxy ; symmetry in Hxy ; firstorder.
Qed.

Lemma map_nil {A B} (f : A -> B) (l : list A) :
    List.map f l = (@nil B) <-> l = (@nil A).
Proof.
    split; intros.
    - induction l; try reflexivity; simpl in *.
    congruence.
    - rewrite H; reflexivity.
Qed.

Lemma map_not_nil {A B} (l : list A) (f : A -> B):
  [] <> List.map f l <-> [] <> l.  
Proof.
   rewrite ne_symm ; rewrite (ne_symm _ l).
   split ; intros.
   * intro Hl. rewrite <-(map_nil f) in Hl ; firstorder.
   * intro Hl. rewrite (map_nil f) in Hl ; firstorder.
Qed.

Lemma not_nil_exists {A} (l : list A) :
  [] <> l <-> exists a, In a l.
Proof.
  split.
  * intros Hl. 
    induction l.
    - firstorder.
    - destruct l.
      -- exists a. simpl; now left. 
      -- set (Hnc := @nil_cons _ a0 l). specialize (IHl Hnc).
         destruct IHl as [a1 Ha1]. 
         exists a1. simpl in * ; intuition.
  * intros [a Ha] not. rewrite <-not in Ha ; firstorder. 
Qed.

Lemma list_prod_not_nil {A B} {la : list A} {lb : list B}(Hla : [] <> la) (Hlb : [] <> lb) :
  [] <> list_prod la lb.
Proof.
  rewrite not_nil_exists.
  rewrite not_nil_exists in Hla.
  rewrite not_nil_exists in Hlb.
  destruct Hla as [a Hla].
  destruct Hlb as [b Hlb].
  exists (a,b). now apply in_prod. 
Qed.

Lemma abs_convg_implies_convg : forall (a : nat -> R), ex_series (fun n => Rabs(a n)) -> ex_series a. 
Proof.
intros a Habs.   
refine (ex_series_le_Reals a (fun n => Rabs(a n)) _ Habs).
intros n. now right.
Qed.

(* Applies a function to an initial argument n times *)
Fixpoint applyn {A} (init : A) (g : A -> A) (n : nat) : A :=
  match n with
  | 0 => init
  | S k => g (applyn init g k)
  end.

End extra.


Section list_sum.
  (* Dump this into RealAdd in Utils. *)
  Lemma list_sum_map_zero {A} (s : list A)  :
  list_sum (List.map (fun _ => 0) s) = 0. 
Proof.
  induction s.
  - simpl; reflexivity.
  - simpl. rewrite IHs ; lra. 
Qed.


Lemma list_sum_le {A} (l : list A) (f g : A -> R) :
  (forall a, f a <= g a) ->
  list_sum (List.map f l) <= list_sum (List.map g l).
Proof.
  intros Hfg.
  induction l.
  - simpl ; right ; trivial.
  - simpl. specialize (Hfg a). 
    apply Rplus_le_compat ; trivial. 
Qed.

Lemma list_sum_mult_const (c : R) (l : list R) :
  list_sum (List.map (fun z => c*z) l) = c*list_sum (List.map (fun z => z) l).
Proof. 
  induction l.
  simpl; lra.
  simpl in *. rewrite IHl. 
  lra. 
Qed.   

Lemma list_sum_const_mult_le {x y : R} (l : list R) (hl : list_sum l = R1) (hxy : x <= y) :
  list_sum (List.map (fun z => x*z) l) <= y.
Proof.
  rewrite list_sum_mult_const. rewrite map_id. 
  rewrite hl. lra. 
Qed. 

Lemma list_sum_fun_mult_le {x y D : R} {f g : R -> R}(l : list R)(hf : forall z, f z <= D) (hg : forall z , 0 <= g z) :
  list_sum (List.map (fun z => (f z)*(g z)) l) <= D*list_sum (List.map (fun z => g z) l).
Proof.
  induction l.
  simpl. lra.
  simpl. rewrite Rmult_plus_distr_l.
  assert (f a * g a <= D * g a). apply Rmult_le_compat_r. exact (hg a). exact (hf a).
  exact (Rplus_le_compat _ _ _ _ H IHl).   
Qed. 

End list_sum.

(* Move this to Finite. *)
Class NonEmpty (A : Type) :=
  ex : A.

Section Rmax_list.

  (* 
   Definition and properties about the maximum element of a list of real numbers.
   Dump this into RealAdd.
   *)
  
Open Scope list_scope.
Open Scope R_scope.

Instance EqDecR : @EqDec R eq _ := Req_EM_T. 

Import ListNotations.

Fixpoint Rmax_list (l : list R) : R :=
  match l with
  | nil => 0
  | a :: nil => a
  | a :: l1 => Rmax a (Rmax_list l1)
  end.


Lemma Rmax_spec_map {A} (l : list A) (f : A -> R) : forall a:A, In a l -> f a <= Rmax_list (List.map f l).
Proof.
  intros a Ha. 
  induction l.
  - simpl ; firstorder.
  - simpl in *. intuition.
    + rewrite H. destruct l. simpl. right; reflexivity. 
      simpl. apply Rmax_l. 
    + destruct l. simpl in *; firstorder.
      simpl in *. eapply Rle_trans ; eauto. apply Rmax_r.
Qed.

Lemma Rmax_spec {l : list R} : forall a:R, In a l -> a <= Rmax_list l.
Proof.
  intros a Ha. 
  induction l.
  - simpl ; firstorder.
  - simpl in *. intuition.
    + rewrite H. destruct l. simpl. right; reflexivity. 
      simpl. apply Rmax_l. 
    + destruct l. simpl in *; firstorder.
      simpl in *. eapply Rle_trans ; eauto. apply Rmax_r.
Qed.

Lemma Rmax_list_map_const_mul {A} (l : list A) (f : A -> R) {r : R} (hr : 0 <= r) :
  Rmax_list (List.map (fun a => r*f(a)) l) = r*(Rmax_list (List.map f l)).
Proof.
  induction l. 
  - simpl ; lra.
  - simpl. rewrite IHl.
    rewrite RmaxRmult ; trivial.
    destruct l.  
    + simpl ; reflexivity.
    + simpl in *. f_equal ; trivial. 
Qed.


Lemma Rmax_list_const_add (l : list R) (d : R) :
  Rmax_list (List.map (fun x => x + d) l) =
  if (l <> []) then ((Rmax_list l) + d) else 0. 
Proof.
  induction l. 
  - simpl ; reflexivity.
  - simpl in *.
    destruct l.
    + simpl ; reflexivity.
    + simpl in * ; rewrite IHl. 
      now rewrite Rcomplements.Rplus_max_distr_r.
Qed.

Lemma Rmax_list_zero {A} (l : list A) :
  Rmax_list (List.map (fun x => 0) l) = 0.
Proof.
  induction l.
  -- simpl ; reflexivity.
  -- simpl in *. rewrite IHl.
     replace (Rmax 0 0) with 0. 
     destruct l ; [simpl ; reflexivity | simpl ; reflexivity] .
     symmetry. apply Rmax_left ; lra. 
Qed. 
 
Lemma Rmax_list_ge (l : list R) (r : R) :
  forall x, In x l -> r <= x -> r <= Rmax_list l.
Proof.
  intros x Hx Hrx. 
  eapply Rle_trans ; eauto.
  now apply Rmax_spec.
Qed.

Lemma Rmax_list_le (l : list R) (r : R) :
  Rmax_list l <= r -> forall x, In x l -> x <= r.
Proof.
  intros H x Hx.
  set (Rmax_spec x Hx). 
  eapply Rle_trans; eauto.
Qed.


Lemma Rmax_list_In (l : list R):
  ([] <> l) -> In (Rmax_list l) l. 
Proof.
  induction l.
  - simpl ; firstorder.
  - intros H. simpl in *.
    destruct l.
    -- now left. 
    -- assert ([] <> r :: l)  by apply nil_cons. 
       specialize (IHl H0) ; clear H0.
       destruct (Rle_dec a (Rmax_list (r :: l))).
       ++ rewrite Rmax_right. now right ; assumption. assumption. 
       ++ rewrite Rmax_left. now left.
          left ; apply ROrder.not_ge_lt ; assumption. 
Qed.

Lemma Rmax_list_lub (l : list R) (r : R):
  ([] <> l) -> (forall x, In x l -> x <= r) -> Rmax_list l <= r. 
Proof.
  intros Hl H.
  apply H. eapply Rmax_list_In ; auto.
Qed.

Lemma Rmax_list_le_iff {l : list R} (hl : [] <> l) (r : R):
  Rmax_list l <= r <-> (forall x, In x l -> x <= r)  .
Proof.
  split. 
  apply Rmax_list_le.
  apply Rmax_list_lub ; auto.
Qed.

Lemma Rmax_list_lt_iff {l : list R} (hl : [] <> l) (r : R):
  Rmax_list l < r <-> (forall x, In x l -> x < r)  .
Proof.
  split. 
  -- intros Hr x Hx.
     eapply Rle_lt_trans. eapply Rmax_spec ; eauto. assumption. 
  -- intro H. apply H ; auto. now apply Rmax_list_In. 
Qed.

Definition Rmax_list_incl l1 l2 : nil <> l1 -> incl l1 l2 -> Rmax_list l1 <= Rmax_list l2.
Proof.
  unfold Proper, respectful, incl
  ; intros.
  apply Rmax_list_le_iff; trivial.
  intros.
  apply Rmax_spec; auto.
Qed.

Global Instance Rmax_list_equivlist : Proper (equivlist ==> eq) Rmax_list.
Proof.
  unfold Proper, respectful; intros x y equivs.
  destruct x.
  - symmetry in equivs.
    apply equivlist_nil in equivs.
    subst; simpl; trivial.
  - destruct y.
    + apply equivlist_nil in equivs.
      discriminate.
    + apply equivlist_incls in equivs.
      destruct equivs.
      generalize (Rmax_list_incl (r::x) (r0::y)); intros HH1.
      generalize (Rmax_list_incl (r0::y) (r::x)); intros HH2.
      cut_to HH1; trivial; try discriminate.
      cut_to HH2; trivial; try discriminate.
      lra.
Qed.

Lemma Rmax_list_sum {A B} {la : list A} (lb : list B) (f : A -> B -> R) (Hla : [] <> la):
  Rmax_list (List.map (fun a => list_sum (List.map (f a) lb)) la) <=
  list_sum (List.map (fun b => Rmax_list (List.map (fun a => f a b) la)) lb). 
Proof.
  rewrite Rmax_list_le_iff. 
  * intro x. rewrite in_map_iff. 
    intros [x0 [Hlsx Hin]].
    rewrite <-Hlsx. apply list_sum_le. 
    intro b. apply (Rmax_spec_map la (fun a => f a b) x0 Hin). 
  * now rewrite map_not_nil. 
Qed.


Lemma Rmax_list_cons_cons (l : list R) (a b : R) :
  Rmax_list (a :: b :: l) = Rmax a (Rmax_list (b :: l)).
Proof.
  constructor.
Qed.

Lemma Rmax_list_Rmax_swap (l : list R) (a b : R) :
  Rmax a (Rmax_list (b :: l)) = Rmax b (Rmax_list (a :: l)).
Proof.
  induction l.
  - simpl ; apply Rmax_comm.
  - do 2 rewrite Rmax_list_cons_cons.
    do 2 rewrite Rmax_assoc. 
    now rewrite (Rmax_comm _ b).
Qed. 
 
Lemma Rmax_list_cons (x0 : R)  (l1 l2 : list R) :
  Permutation l1 l2 -> (Rmax_list l1 = Rmax_list l2) -> Rmax_list (x0 :: l1) = Rmax_list(x0 :: l2).
Proof.
  intros Hpl Hrl. 
  case_eq l1.
  * intro Hl. rewrite Hl in Hpl. set (Permutation_nil Hpl).
    now rewrite e.
  * case_eq l2.
    ++ intro Hl2. rewrite Hl2 in Hpl. symmetry in Hpl. set (Permutation_nil Hpl).
       now rewrite e.
    ++ intros r l H r0 l0 H0. 
       rewrite <-H0, <-H. simpl ; rewrite Hrl.
       now rewrite H0, H.  
Qed.

Lemma Rmax_list_cons_swap (x0 y0 : R)  (l1 l2 : list R) :
  Permutation l1 l2 -> (Rmax_list l1 = Rmax_list l2) ->
  Rmax_list (x0 :: y0 :: l1) = Rmax_list(y0 :: x0 :: l2).
Proof.
  intros Hpl Hrl.
  rewrite Rmax_list_cons_cons. rewrite Rmax_list_Rmax_swap.
  rewrite <-Rmax_list_cons_cons.  
  case_eq l1.
  * intro Hl. rewrite Hl in Hpl. set (Permutation_nil Hpl).
    now rewrite e.
  * case_eq l2.
    ++ intro Hl2. rewrite Hl2 in Hpl. symmetry in Hpl. set (Permutation_nil Hpl).
       now rewrite e.  
    ++ intros r l H r0 l0 H0.  rewrite <-H0, <-H. simpl ; rewrite Hrl.
       now rewrite H0, H.
Qed.

Global Instance Rmax_list_Proper : Proper (@Permutation R ++> eq) Rmax_list.
Proof.
  unfold Proper. intros x y H. 
  apply (@Permutation_ind_bis R (fun a b => Rmax_list a = Rmax_list b)). 
  - simpl ; lra. 
  - intros x0. apply Rmax_list_cons.  
  - intros x0 y0 l l' H0 H1. apply Rmax_list_cons_swap ; trivial. 
  - intros l l' l'' H0 H1 H2 H3. rewrite H1. rewrite <-H3. reflexivity. 
  - assumption. 
Qed.

Definition Rmax_list_map {A} (l : list A) (f : A -> R) := Rmax_list (List.map f l).  

Declare Scope rmax_scope.
Notation "Max_{ l } ( f )" := (Rmax_list (List.map f l)) (at level 50) : rmax_scope.

Open Scope rmax_scope.
Delimit Scope rmax_scope with rmax.

(* This is very important. *)
Lemma Rmax_list_map_exist {A} (f : A -> R) (l : list A) :
  [] <> l -> exists a:A, In a l /\ f a = Max_{l}(f). 
Proof.
  intro Hne. 
  set (Hmap := Rmax_list_In (List.map f l)).
  rewrite <-(map_not_nil l f) in Hne.
  specialize (Hmap Hne).
  rewrite in_map_iff in Hmap.
  destruct Hmap as  [a [Hfa Hin]].
  now exists a. 
Qed.

Lemma exists_in_strengthen_dec {A} (P:A->Prop) l (dec:forall x, {P x} + {~ P x})
      (ex:exists x, In x l /\ P x) : {x | In x l /\ P x}.
Proof.
  induction l; simpl.
  - elimtype False.
    destruct ex ; intuition.
  - destruct (dec a).
    + exists a ; eauto.
    + destruct IHl as [x [inx px]].
      * destruct ex as [x [inx px]].
        destruct inx.
        -- congruence.
        -- eauto.
      * eauto.
Qed.

(* This is very important too. *)
Lemma Rmax_list_map_exist_sig {A} (f : A -> R) {l : list A} :
  [] <> l -> { a:A | In a l /\ f a = Max_{l}(f)}. 
Proof.
  intro Hne.
  apply exists_in_strengthen_dec.
  - intro x. apply Req_EM_T.
  - now apply Rmax_list_map_exist.
Qed.

Definition argmax {A} {l : list A} (hl : [] <> l)(f : A -> R) : A :=
  proj1_sig (Rmax_list_map_exist_sig f hl).

Lemma argmax_is_max {A} {l : list A} (hl : [] <> l) (f : A->R) :
  f (argmax hl f) = Max_{l}(f).
Proof.
  unfold argmax.
  destruct (Rmax_list_map_exist_sig f hl).
  simpl. now destruct a. 
Qed.

Lemma argmax_in_list {A} {l : list A} (hl : [] <> l) (f : A -> R):
  In (argmax hl f) l.
Proof.
  unfold argmax.
  destruct (Rmax_list_map_exist_sig f hl).
  simpl. now destruct a.
Qed.

Global Instance Rmax_eq_Proper {A} {l : list A} (hl : [] <> l) :
  Proper (pointwise_relation _ eq ++> eq) (@Rmax_list_map A l).
Proof.
  unfold Proper, respectful, pointwise_relation.
  intros f g H.
  unfold Rmax_list_map.
  induction l.
  -- simpl. reflexivity.
  -- simpl. destruct l.
     ++ simpl. apply H.
     ++ simpl. rewrite H. simpl in IHl. rewrite IHl. reflexivity.
        apply nil_cons. 
Qed.

Lemma Rmax_list_prod_le {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
  Max_{la}(fun a => Max_{lb} (fun b => f a b)) =
  Max_{list_prod la lb} (fun ab => f (fst ab) (snd ab)). 
Proof.
  apply Rle_antisym.
  ++  rewrite Rmax_list_le_iff.
      -- intros x Hx. eapply (@Rmax_list_ge _ _ x).
         ** rewrite in_map_iff in *. 
            destruct Hx as [a [Hx' HInx']]. 
            set (Hmax := Rmax_list_map_exist (fun b => f a b) lb). 
            specialize (Hmax Hlb).
            destruct Hmax as [b Hb].
            exists (a,b). simpl. split; [now rewrite <-Hx' |].
            apply in_prod ; trivial; intuition.
         ** now right.
      -- now rewrite map_not_nil.
  ++ rewrite Rmax_list_le_iff.
     * intros x Hx.
       rewrite in_map_iff in Hx.
       destruct Hx as [ab [Hab HInab]].
       eapply (@Rmax_list_ge _ _ (Rmax_list (List.map (fun b : B => f (fst ab) b) lb))).
       --- rewrite in_map_iff. 
           exists (fst ab). split ; trivial.
           setoid_rewrite surjective_pairing in HInab. 
           rewrite in_prod_iff in HInab. destruct HInab ; trivial.
       --- eapply (Rmax_list_ge _ _ (f (fst ab) (snd ab))).
           +++ rewrite in_map_iff. exists (snd ab). split ; trivial.
               setoid_rewrite surjective_pairing in HInab. 
               rewrite in_prod_iff in HInab. destruct HInab ; trivial.
           +++ rewrite <-Hab. right ; trivial.
     * rewrite map_not_nil. now apply list_prod_not_nil. 
Qed.

(* There has to be a better way of doing this... *)
Lemma Rmax_list_prod_le' {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
   Max_{lb}(fun b => Max_{la} (fun a => f a b))  =
   Max_{list_prod la lb} (fun ab => f (fst ab) (snd ab)).
Proof.
  apply Rle_antisym.
  ++  rewrite Rmax_list_le_iff.
      -- intros x Hx. eapply (@Rmax_list_ge _ _ x).
         ** rewrite in_map_iff in *. 
            destruct Hx as [b [Hx' HInx']]. 
            set (Hmax := Rmax_list_map_exist (fun a => f a b) la). 
            specialize (Hmax Hla).
            destruct Hmax as [a Ha].
            exists (a,b). simpl. split; [now rewrite <-Hx' |].
            apply in_prod ; trivial; intuition.
         ** now right.
      -- now rewrite map_not_nil.
  ++ rewrite Rmax_list_le_iff.
     * intros x Hx.
       rewrite in_map_iff in Hx.
       destruct Hx as [ab [Hab HInab]].
       eapply (@Rmax_list_ge _ _ (Rmax_list (List.map (fun a : A  => f a (snd ab)) la))).
       --- rewrite in_map_iff. 
           exists (snd ab). split ; trivial.
           setoid_rewrite surjective_pairing in HInab. 
           rewrite in_prod_iff in HInab. destruct HInab ; trivial.
       --- eapply (Rmax_list_ge _ _ (f (fst ab) (snd ab))).
           +++ rewrite in_map_iff. exists (fst ab). split ; trivial.
               setoid_rewrite surjective_pairing in HInab. 
               rewrite in_prod_iff in HInab. destruct HInab ; trivial.
           +++ rewrite <-Hab. right ; trivial.
     * rewrite map_not_nil. now apply list_prod_not_nil. 
Qed.

Lemma Rmax_list_map_comm {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
  Max_{la}(fun a => Max_{lb} (fun b => f a b)) = Max_{lb}(fun b => Max_{la} (fun a => f a b)) .
Proof.
  etransitivity; [|symmetry].
  - apply Rmax_list_prod_le ; trivial. 
  - apply Rmax_list_prod_le'; trivial.   
Qed.



Lemma Rmax_list_minus_le {A} {B : A -> Type} (f g : forall a, B a -> R) (la : forall a, list (B a)):
 forall a:A, (Max_{la a}(f a) - Max_{la a}(g a)) <= Max_{la a}(fun x => f a x - g a x).
Proof.
  intro a0. 
  destruct (is_nil_dec (la a0)).
  - setoid_rewrite e. simpl. lra.
  - rewrite Rle_minus_l.
    rewrite Rmax_list_le_iff. intros x Hin.
    rewrite in_map_iff in Hin.
    destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
    replace (f a0 a) with ((f a0 a - g a0 a) + g a0 a) by ring. 
    apply Rplus_le_compat.
    -- apply Rmax_spec. rewrite in_map_iff.
       exists a ; split ; trivial. 
    -- apply Rmax_spec. rewrite in_map_iff.
       exists a ; split ; trivial.
    -- rewrite map_not_nil. congruence.
Qed.


Lemma Rmax_list_minus_le_abs {A} (f g : A -> R) (la : list A):
  Rabs (Max_{la}(f) - Max_{la}(g)) <= Max_{la}(fun a => Rabs(f a - g a)).
Proof.
   destruct (is_nil_dec la).
  - subst; simpl. replace (0-0) with 0 by ring. right. now apply Rabs_R0.
  - rewrite Rabs_le_between'.
    split.
    -- rewrite Rle_minus_l. rewrite Rmax_list_le_iff ; [| apply map_not_nil ; congruence].
       intros x Hin.
       rewrite in_map_iff in Hin.
       destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
       replace (g a) with (f a + (g a - f a)) by ring.
       apply Rplus_le_compat.
       --- apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
       --- eapply Rle_trans ; first apply Rle_abs.
           rewrite Rabs_minus_sym. apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
    -- rewrite Rmax_list_le_iff ; [| apply map_not_nil ; congruence].
       intros x Hin.
       rewrite in_map_iff in Hin.
       destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
       replace (f a) with (g a + (f a - g a)) by ring.
       apply Rplus_le_compat.
       --- apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
       --- eapply Rle_trans ; first apply Rle_abs.
           rewrite Rabs_minus_sym. apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial. apply Rabs_minus_sym.
Qed.


Lemma Rmax_list_minus_le_abs' {A} {B : A -> Type} (f g : forall a, B a -> R) (la : forall a, list (B a)):
 forall a:A, Rabs (Max_{la a}(f a) - Max_{la a}(g a)) <= Max_{la a}(fun x => Rabs(f a x - g a x)).
Proof.
  intro a0. 
  destruct (is_nil_dec (la a0)).
  - setoid_rewrite e. simpl. replace (0-0) with 0 by ring. right. now apply Rabs_R0.
  - rewrite Rabs_le_between'.
    split.
    -- rewrite Rle_minus_l. rewrite Rmax_list_le_iff ; [| apply map_not_nil ; congruence].
       intros x Hin.
       rewrite in_map_iff in Hin.
       destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
       replace (g a0 a) with (f a0 a + (g a0 a - f a0 a)) by ring.
       apply Rplus_le_compat.
       --- apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
       --- eapply Rle_trans ; first apply Rle_abs.
           rewrite Rabs_minus_sym. apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
    -- rewrite Rmax_list_le_iff ; [| apply map_not_nil ; congruence].
       intros x Hin.
       rewrite in_map_iff in Hin.
       destruct Hin as [a [Ha Hina]]. rewrite <-Ha.
       replace (f a0 a) with (g a0 a + (f a0 a - g a0 a)) by ring.
       apply Rplus_le_compat.
       --- apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial.
       --- eapply Rle_trans ; first apply Rle_abs.
           rewrite Rabs_minus_sym. apply Rmax_spec. rewrite in_map_iff.
           exists a ; split ; trivial. apply Rabs_minus_sym.
Qed.

    
(* max_{x:A} (max_{f:A->B}(g (f a) f)) = max_{f:A->B} (max_{a:map f A} (g (a,f))) *)

Lemma Rmax_list_fun_swap {A B} {lf : list(A -> B)}{la : list A}
      (g :B -> (A -> B) -> R)
      (hl : [] <> lf) (hla : [] <> la)  :
      Max_{la} (fun s => Max_{lf} (fun f => g (f s) f))  =
      Max_{lf} (fun f => Max_{List.map f la} (fun b => g b f)).
Proof. 
  rewrite Rmax_list_map_comm; trivial.
  f_equal. apply map_ext.
  intros a.  
  now rewrite map_map.
Qed.

Lemma Rmax_list_le_range {A B} (f : A -> B) (g : B -> R) {la : list A} {lb : list B}
      (hla : [] <> la)
      (hf : forall {a}, In a la -> In (f a) lb) :
  Max_{la} (fun a => g(f a)) <= Max_{lb} (fun b => g b).
Proof.   
  rewrite Rmax_list_le_iff. 
  intros x Hx.
  rewrite in_map_iff in Hx.
  -- destruct Hx as [a [Ha Hina]].
     eapply Rmax_list_ge.
     rewrite in_map_iff. exists (f a). split;eauto.
     now right.
  -- now rewrite map_not_nil.
Qed.

Lemma Rmax_list_le_range' {A B} (g : B -> R) lf {lb : list B}
      (hlf : [] <> lf){a : A}
      (hfa : forall f, In (f a) lb)  :
  Max_{lf} (fun f => g(f a)) <= Max_{lb} (fun b => g b).
Proof.
  destruct (Rmax_list_map_exist (fun f => g (f a)) lf hlf) as [f [Hf Hinf]].
  rewrite <-Hinf.
  eapply Rmax_spec_map. apply hfa. 
Qed.

Lemma Rmax_list_fun_le {A} {la : list A}
      (f : A -> R) (g : A -> R) :
      (forall a, f a <= g a) ->
      Max_{la} (fun a => f a) <= Max_{la} (fun a => g a).
Proof.
  intros Hfg.
  destruct (is_nil_dec la) ; [subst ; simpl ; lra|].
  rewrite ne_symm in n. 
  destruct (Rmax_list_map_exist (fun a => g a) la n) as [a1 [Ha1 Hina1]].
  destruct (Rmax_list_map_exist (fun a => f a) la n) as [a2 [Ha2 Hina2]].
  rewrite <-Hina1.
  rewrite Rmax_list_le_iff.
  intros x Hx. rewrite in_map_iff in Hx.
  destruct Hx as [a0 [ha0 hina0]]. rewrite <-ha0.
  enough (f a0 <= f a2).
  assert (f a2 <= g a2) by (apply Hfg).
  enough (g a2 <= g a1).
  lra.
  rewrite Hina1. apply Rmax_spec. rewrite in_map_iff. exists a2 ; split ; trivial.
  rewrite Hina2. apply Rmax_spec. rewrite in_map_iff. exists a0 ; split ; trivial.
  now rewrite map_not_nil.
Qed.

Lemma Rmax_list_fun_le' {A B} {la : list A} {lb : list B}
      (f : A -> R) (g : B -> R)
      (hla : [] <> la) (hlb : [] <> lb)  :
      (forall a b, f a <= g b) ->
      Max_{la} (fun a => f a) <= Max_{lb} (fun b => g b).
Proof.
  intros Hfg.
  destruct (Rmax_list_map_exist (fun b => g b) lb hlb) as [b [Hb Hinb]].
  destruct (Rmax_list_map_exist (fun a => f a) la hla) as [a [Ha Hina]].
  rewrite <-Hinb, <-Hina.
  apply Hfg.
Qed.

Lemma Rmax_list_map_transf {A B} (l : list A) (f : A -> R) (f' : B -> R) (g : A -> B) :
 (List.Forall (fun x => f x = f'(g x)) l) -> Max_{l}(f) = Max_{List.map g l}(f').
Proof.
  intros H.
  rewrite Forall_forall in H.
  rewrite map_map. f_equal.
  apply List.map_ext_in. 
  assumption.
Qed.
 
Lemma Rmax_list_pairs {A} (ls : list (Stream A)) (f : Stream A -> R) (f':A*Stream A -> R) :
  (List.Forall(fun x => f x = f'(hd x, tl x)) ls) -> Max_{ls}(f) = Max_{(List.map (fun x => (hd x, tl x)) ls)}(fun x => f'(x)).
Proof.
  apply Rmax_list_map_transf. 
Qed.

End Rmax_list.

Notation "Max_{ l } ( f )" := (Rmax_list (List.map f l)) (at level 50).

Section MDPs.

  (* 
   Definition of Markov Decision Processes. We crucially use the Giry monad in the 
   definition. 
 *)
Open Scope monad_scope.
Open Scope R_scope.

Record MDP := mkMDP {
 (* State and action spaces. *)
 state : Type;
 act  : forall s: state, Type;
 
 (* The state space has decidable equality.*)
 st_eqdec :> EqDec state eq;

 (* The state and action spaces are finite. *)
 fs :> Finite (state) ;
 fa :> forall s, Finite (act s);

 (* The state space and the fibered action spaces are nonempty. *)
 ne : NonEmpty (state) ;
 na : forall s, NonEmpty (act s);
 (* Probabilistic transition structure. 
    t(s,a,s') is the probability that the next state is s' given that you take action a in state s.
    One can also consider to to be an act-indexed collection of Kliesli arrows of Pmf. 
 *)
 t :  forall s : state, act s -> Pmf state;
 (* Reward when you move to s' from s by taking action a. *)
 reward : forall s : state, act s -> state -> R                                
}.

Arguments outcomes {_}.
Arguments t {_}.
Arguments reward {_}.

(* 
   A decision rule is a mapping from states to actions.
*)
Definition dec_rule (M : MDP) := forall s : M.(state), (M.(act)) s.

Global Instance dec_rule_finite (M : MDP) : Finite (dec_rule M).
Proof.
  eapply Finite_fun_dep ; eauto.
  - apply fs.
  - apply fa.
 Unshelve.
 apply st_eqdec.
Qed.

Global Instance nonempty_dec_rule (M : MDP) : NonEmpty (dec_rule M)
  := fun s => na M s.

(* For every s, we get a list of all actions available at that state. *)
Definition act_list (M : MDP) : forall s, list (act M s) :=
  fun s => let (la, Hla) := fa M s in la.

(* For every s, we get a proof that the list of actions is not nil. *)
Lemma act_list_not_nil (M : MDP) : forall s, [] <> act_list M s.
Proof. 
  intros s.
  apply not_nil_exists.
  unfold act_list.
  destruct (fa M s). now exists (na M s).
Qed.  

(*
   In general,a policy is a *stream* of decision rules. 
   A stream of constant decision rules is called a *stationary policy*. 
   Henceforth, we shall only work with stationary policies. 
 *)

Definition policy (M : MDP) := Stream (dec_rule M).
 

Context {M : MDP}.
Context (σ : dec_rule M).

(* Constructing a Kliesli arrow out of a stationary policy by n-iterated binds.
   This can be interpreted as as n-multiplications of an
   |S| × |S| stochastic matrix. 
   We don't explicitly construct a stationary stream -- for that we would have to 
   update the σ after each bind.
*)

Definition bind_stoch_iter (n : nat) (init : M.(state)) : Pmf M.(state):=
  applyn (Pmf_pure init) (fun y => Pmf_bind y (fun s => t s (σ s))) n.

Definition bind_stoch_iter_str (π : Stream(dec_rule M)) (n : nat) (init : M.(state)) 
  : Pmf M.(state):=
  applyn (Pmf_pure init) (fun y => Pmf_bind y (fun s => t s (Str_nth n π s))) n.

(* 
   It is helpful to see what happens in the above definition for n=1, and starting at init.
   We get the transition probability structure applied to the initial state, init, and upon
   taking the action σ(init) as prescribed by the policy sigma. So we recover the entire 
   transition structure after one step. Similar remarks apply for n-steps.
*)

Lemma bind_stoch_iter_1 (init : M.(state)) :
  bind_stoch_iter 1 init = t init (σ init).
Proof. 
  unfold bind_stoch_iter.
  simpl. rewrite Pmf_bind_of_ret.
  reflexivity.
Qed.

(* Expected immediate reward for performing action (σ s) when at state s. *)
Definition step_expt_reward : state M -> R :=
  (fun s => expt_value (t s (σ s)) (reward s (σ s))).


(* Expected reward after n-steps, starting at initial state, following policy sigma. *)
Definition expt_reward (init : M.(state)) (n : nat) : R :=
 expt_value (bind_stoch_iter n init) (step_expt_reward).

  
(* Expected reward at time 0 is equal to the reward. *)
Lemma expt_reward0_eq_reward : forall init : M.(state), expt_reward init 0 = (step_expt_reward init).
Proof.
  intros init.
  unfold expt_reward. unfold bind_stoch_iter ; simpl.
  now rewrite expt_value_pure. 
Qed.

(*
 With every iteration, the reward changes to the average of the rewards of the previous transition states.
*)
Lemma expt_reward_succ (n : nat) : forall init : M.(state), expt_reward init (S n) =  expt_value (bind_stoch_iter n init) (fun s : state M => expt_value (t s (σ s)) (step_expt_reward)).
Proof.
  intros init. 
  unfold expt_reward. unfold bind_stoch_iter. 
  simpl. rewrite expt_value_bind.
  f_equal.
Qed.


(* Bounded rewards (in absolute value) imply bounded expected rewards for all iterations and all states. *)
Lemma expt_reward_le_max_Rabs {D : R} (init : M.(state)) :
  (forall s s': M.(state), Rabs (reward s (σ s) s') <= D)  ->
  (forall n:nat, Rabs (expt_reward init n) <= D). 
Proof. 
  intros H. 
  unfold expt_reward. intros n. apply expt_value_Rle.
  unfold step_expt_reward. intros s.
  apply expt_value_Rle. apply H. 
Qed.


End MDPs.

(*Section egs.

(* This defines a "unit reward" MDP.*)
Definition unitMDP {st0 act0 : Type} (t0 : st0 -> act0 -> Pmf st0) : MDP :=
{|
    state := st0;
    act := _ ;
    
    t := t0;
    reward := fun s a s' => R0
|}.

(* The expected reward for an arbitrary initial state and arbitrary policy is unity for a unit MDP. *)
Lemma expt_reward_unitMDP {t0 : R -> R -> Pmf R} :
  let M0 := unitMDP t0 in
  forall (σ0 : dec_rule M0) (init0 : M0.(state)) (n:nat), expt_reward σ0 init0 n = R0. 
Proof.
  intros M0 σ0 init0 n.
  assert (expt_value (bind_stoch_iter σ0 n init0) (fun s => R0) = R0). apply expt_value_zero.
  rewrite <-H.
  unfold expt_reward.
  unfold step_expt_reward. simpl.
  f_equal. apply functional_extensionality. intros x.
  apply expt_value_zero. 
Qed.

End egs.*)

Section Rfct_AbelianGroup.

 (* 
    Additive abelian group structure on the function space A -> R. 
    Here we assume A is a finite set.
    To talk about equality we use functional extensionality.
    Put this into it's own file.
  *)
Definition Rfct (A : Type) {fin : Finite A} := A -> R.

Context (A : Type) {finA : Finite A}. 
                                
Definition Rfct_zero : Rfct A := fun x => 0. 

Definition Rfct_plus (f : Rfct A) (g : Rfct A) := fun x => (f x) + (g x).  

Definition Rfct_opp (f : Rfct A) := fun x => opp (f x).

Definition Rfct_scal (r : R) (f : Rfct A) := fun x => scal r (f x).

Definition Rfct_le (f g : Rfct A) := forall a : A, f a <= g a.

Definition Rfct_ge (f g : Rfct A) := forall a : A, f a >= g a.

Lemma Rfct_not_ge_lt (f g  : Rfct A) : not (Rfct_ge f g) <-> (exists a : A, f a < g a).
Proof.
  unfold Rfct_ge.
  split.
  - intro H. apply Classical_Pred_Type.not_all_not_ex.
    intro H'. apply H. intro a. specialize (H' a). now apply Rnot_gt_ge.
  - intro H. apply Classical_Pred_Type.ex_not_not_all.
    destruct H as [a Ha]. exists a. 
    now apply Rlt_not_ge.
Qed.

Lemma Rfct_not_le_gt (f g  : Rfct A) : not (Rfct_le f g) <-> (exists a : A, f a > g a).
Proof.
  unfold Rfct_le.
  split.
  - intro H. apply Classical_Pred_Type.not_all_not_ex.
    intro H'. apply H. intro a. specialize (H' a). now apply Rnot_gt_le.
  - intro H. apply Classical_Pred_Type.ex_not_not_all.
    destruct H as [a Ha]. exists a. 
    now apply Rgt_not_le.
Qed.

Lemma Rfct_ge_not_lt (f g  : Rfct A) : (Rfct_ge f g) <-> not (exists a : A, f a < g a).
Proof.
  unfold Rfct_ge.
  split.
  - intro H. apply Classical_Pred_Type.all_not_not_ex.
    intro a. specialize (H a). apply Rle_not_lt.
    lra.
  - intro H. apply Classical_Pred_Type.not_ex_not_all.
    intro H'. destruct H' as [a Ha]. apply H. exists a. 
    now apply Rnot_ge_lt.
Qed.   

Lemma Rfct_le_not_gt (f g  : Rfct A) : (Rfct_le f g) <-> not (exists a : A, f a > g a).
Proof.
  unfold Rfct_le.
  split.
  - intro H. apply Classical_Pred_Type.all_not_not_ex.
    intro a. specialize (H a). now apply Rle_not_gt.
  - intro H. apply Classical_Pred_Type.not_ex_not_all.
    intro H'. apply H.
    destruct H' as [a Ha]. exists a. 
    now apply Rnot_le_gt.
Qed.

Lemma Rfct_le_ge_symm (f g : Rfct A) : Rfct_le f g <-> Rfct_ge g f.
Proof.
  split; intros.
  - intro a. specialize (H a). now apply Rle_ge.
  - intro a. specialize (H a). now apply Rge_le.
Qed.  

Definition monotone_le (F : Rfct A -> Rfct A) := forall f g, Rfct_le f g -> Rfct_le (F f) (F g). 

Definition monotone_ge (F : Rfct A -> Rfct A) := forall f g, Rfct_ge f g -> Rfct_ge (F f) (F g). 

Lemma Rfct_eq_ext (f g:Rfct A) : (forall x, f x = g x) -> f = g.
Proof.
  apply functional_extensionality.
Qed.

Lemma Rfct_le_antisym (f g : Rfct A) : f = g <-> Rfct_le f g /\ Rfct_le g f.
Proof.
  split ; intros.
  - split. 
    ++ intros a. set (equal_f H).
       specialize (e a). now right.
    ++ intros a. set (equal_f H).
       specialize (e a). now right.
  - destruct H as [Hl Hr]. apply Rfct_eq_ext.
    intro a. specialize (Hl a). specialize (Hr a).
    apply Rle_antisym ; auto.
Qed.
    
Lemma Rfct_plus_comm (f g:Rfct A) : Rfct_plus f g = Rfct_plus g f.
Proof.
  apply Rfct_eq_ext. intros x.
  unfold Rfct_plus. lra.
Qed.

Lemma Rfct_plus_assoc (x y z:Rfct A) : Rfct_plus x (Rfct_plus y z) = Rfct_plus (Rfct_plus x y) z.
Proof.
  apply Rfct_eq_ext.
  intro a. unfold Rfct_plus.
  lra.
Qed.

Lemma Rfct_plus_zero_r (x:Rfct A) : Rfct_plus x Rfct_zero = x.
Proof.
  unfold Rfct.
  apply Rfct_eq_ext ; intros.
  unfold Rfct_plus.
  unfold Rfct_zero. lra.
Qed.

Lemma Rfct_plus_opp_r (f:Rfct A) : Rfct_plus f (Rfct_opp f) = Rfct_zero.
Proof.
  unfold Rfct.
  apply Rfct_eq_ext ; intros.
  unfold Rfct_plus.
  unfold Rfct_opp. unfold Rfct_zero.
  apply (plus_opp_r (f x)).
Qed.


Definition Rfct_AbelianGroup_mixin :=
  AbelianGroup.Mixin (Rfct A) Rfct_plus Rfct_opp Rfct_zero Rfct_plus_comm
   Rfct_plus_assoc Rfct_plus_zero_r Rfct_plus_opp_r.

Canonical Rfct_AbelianGroup :=
  AbelianGroup.Pack (Rfct A) (Rfct_AbelianGroup_mixin) (Rfct A).

End Rfct_AbelianGroup.

Section Rfct_ModuleSpace.

  (* 
     The function type A -> R is also a module over the Real numbers.
     Here we assume A is a finite set.     
   *)
Context (A : Type) {finA : Finite A}.
  
Lemma Rfct_scal_assoc (x y : R) (u: Rfct A) :
   Rfct_scal A x (Rfct_scal A y u) = Rfct_scal A (x*y) u.
Proof.
  unfold Rfct_scal.
  eapply Rfct_eq_ext.
  intro x0. unfold scal ; simpl. now rewrite Rmult_assoc.
Qed.

Lemma Rfct_scal_one (u:Rfct A) : Rfct_scal A R1 u = u.
Proof.
  unfold Rfct_scal.
  eapply Rfct_eq_ext.
  intro x0. unfold scal ; simpl. apply Rmult_1_l.
Qed.

Lemma Rfct_scal_distr_l x (u v:Rfct A) : Rfct_scal A x (Rfct_plus A u v)
        = Rfct_plus A (Rfct_scal A x u) (Rfct_scal A x v).
Proof.
  unfold Rfct_scal.
  eapply Rfct_eq_ext.
  intro x0. unfold Rfct_plus.
  apply Rmult_plus_distr_l.
Qed.

Lemma Rfct_scal_distr_r (x y:R) (u:Rfct A) : Rfct_scal A (Rplus x y) u
         = Rfct_plus A (Rfct_scal A x u) (Rfct_scal A y u).
Proof.
  unfold Rfct_scal.
  eapply Rfct_eq_ext.
  intro x0. unfold Rfct_plus.
  apply Rmult_plus_distr_r.
Qed.

Definition Rfct_ModuleSpace_mixin :=
  ModuleSpace.Mixin R_Ring (Rfct_AbelianGroup A) (Rfct_scal A) Rfct_scal_assoc
     Rfct_scal_one Rfct_scal_distr_l Rfct_scal_distr_r.

Canonical Rfct_ModuleSpace :=
  ModuleSpace.Pack R_Ring (Rfct A)
   (ModuleSpace.Class R_Ring (Rfct A) _ Rfct_ModuleSpace_mixin) (Rfct A).

End Rfct_ModuleSpace.

Section Rfct_UniformSpace.
 
(* 
   Definition of a Uniformspace structure on functionals f : A -> R where 
   the ecart is defined as Max_{ls}(fun s => Rabs (f s - g s)) where ls is a list of 
   all elements of A. It exists since here we assume A is a finite set.
*)
  
Context (A : Type) {finA : Finite A}.


Definition Rmax_norm : Rfct A -> R := let (ls,_) := finA in fun (f:Rfct A) => Max_{ls}(fun s => Rabs (f s)).

Definition Rmax_ball :=  fun (f: Rfct A) eps g => Rmax_norm (fun s => minus (g s) (f s)) < eps.

Lemma Rmax_ball_le (f g : Rfct A) {eps1 eps2 : R} :
  eps1 <= eps2 -> Rmax_ball f eps1 g -> Rmax_ball f eps2 g.
Proof. 
  intros Heps Hball.
  unfold Rmax_ball in *. 
  eapply Rlt_le_trans ; eauto.
Qed.

Lemma Rmax_ball_center (f : Rfct A) (e : posreal) : Rmax_ball f e f.
Proof.
  unfold Rmax_ball. unfold Rmax_norm.
  destruct finA as [ls Hls]. 
  eapply Rle_lt_trans ; last apply cond_pos.
  destruct (is_nil_dec ls).
  - subst ; simpl. now right. 
  - rewrite Rmax_list_le_iff.
    intros x Hx. rewrite in_map_iff in Hx.
    destruct Hx as [a [Ha Hina]].
    rewrite minus_eq_zero in Ha. rewrite <-Ha. 
    right. unfold zero. simpl.
    apply Rabs_R0.
    rewrite map_not_nil. now apply ne_symm.
Qed.

Lemma Rmax_ball_sym (f g : Rfct A) (e : R) : Rmax_ball f e g -> Rmax_ball g e f.
Proof.
  unfold Rmax_ball in *. unfold Rmax_norm in *.
  destruct finA as [ls Hls]. 
  enough (Max_{ls}(fun s => Rabs (minus (f s) (g s))) = Max_{ls}(fun s => Rabs(minus (g s) (f s)))). 
  now rewrite H.
  f_equal. apply List.map_ext_in.
  intros a H0.
  now rewrite Rabs_minus_sym.
Qed.


Lemma Rmax_ball_triangle (f g h : Rfct A) (e1 e2 : R) :
    Rmax_ball f e1 g -> Rmax_ball g e2 h -> Rmax_ball f (e1 + e2) h.
Proof.
  intros H1 H2.
  unfold Rmax_ball in *. unfold Rmax_norm in *.
  destruct finA as [ls Hls]. 
  destruct (is_nil_dec ls).
  - subst. simpl in *. lra. 
  - assert (Hfg : forall s f g, In s ls -> Rabs (minus (f s) (g s)) <= Max_{ ls}(fun s : A => Rabs (minus (f s) (g s)))).
  {
    intros s f1 f2 Hs.
    apply Rmax_spec.
    rewrite in_map_iff.
    exists s ; split; trivial.
  }
  eapply Rle_lt_trans. 
  2 : apply (Rplus_lt_compat _ _ _ _ H1 H2).
  rewrite Rmax_list_le_iff. 
  intros x Hx. rewrite in_map_iff in Hx. 
  destruct Hx as [a [Ha Hina]].
  rewrite <-Ha.
  eapply Rle_trans.
  assert (minus (h a) (f a) = (minus (h a) (g a)) + (minus (g a) (f a))).
  rewrite (minus_trans (g a)). reflexivity.
  rewrite H. apply Rabs_triang. rewrite Rplus_comm.
  apply Rplus_le_compat.
  apply Rmax_spec. rewrite in_map_iff. exists a. split ; trivial. 
  apply Rmax_spec. rewrite in_map_iff. exists a. split ; trivial. 
  rewrite map_not_nil. now rewrite ne_symm.  
Qed.

  
Definition Rfct_UniformSpace_mixin :=
  UniformSpace.Mixin (Rfct A) Rmax_ball Rmax_ball_center Rmax_ball_sym Rmax_ball_triangle.

(* 
   There seems to be a problem defining a `Canonical` version of this, 
   since it is picking up the Uniformspace 
   structure inherited from R. Maybe this isn't even necessary...?
*)
Definition Rfct_UniformSpace : UniformSpace :=
  UniformSpace.Pack (Rfct A) Rfct_UniformSpace_mixin (Rfct A).


End Rfct_UniformSpace.


Section Rfct_NormedModule.

  (* 
     The function type A -> R is a normed module. The ball is defined using the norm.
   *)
Context (A : Type) {finA : Finite A}.

Canonical Rfct_NormedModuleAux :=
  NormedModuleAux.Pack R_AbsRing (Rfct A)
   (NormedModuleAux.Class R_AbsRing (Rfct A)
     (ModuleSpace.class _ (Rfct_ModuleSpace A))
        (Rfct_UniformSpace_mixin A)) (Rfct A).

Lemma Rfct_norm_triangle f g: 
      (Rmax_norm A (Rfct_plus A f g)) <= (Rmax_norm A f) + (Rmax_norm A g).
Proof.
  unfold Rmax_norm. unfold Rfct_plus.
  destruct finA as [ls Hls]. 
   destruct (is_nil_dec ls).
  - subst. simpl in *. lra. 
  -  rewrite Rmax_list_le_iff. 
  intros x Hx. rewrite in_map_iff in Hx. 
  destruct Hx as [a [Ha Hina]].
  rewrite <-Ha.
  eapply Rle_trans.
  apply Rabs_triang. 
  apply Rplus_le_compat.
  apply Rmax_spec. rewrite in_map_iff. exists a. split ; trivial. 
  apply Rmax_spec. rewrite in_map_iff. exists a. split ; trivial. 
  rewrite map_not_nil. now rewrite ne_symm.  
Qed.


(* These proofs are trivial since the ball is defined using the norm. *)
Lemma Rfct_norm_ball1 : forall (f g : Rfct A) (eps : R),
     Rmax_norm A (minus g f) < eps -> @Hierarchy.ball (NormedModuleAux.UniformSpace R_AbsRing Rfct_NormedModuleAux)  f eps g.
Proof.
  intros f g eps H.
  unfold ball ; simpl. apply H.
Qed.

Lemma Rfct_norm_ball2 (f g : Rfct A) (eps : posreal) :
    @Hierarchy.ball (NormedModuleAux.UniformSpace R_AbsRing Rfct_NormedModuleAux) f eps g ->
    Rmax_norm A (minus g f) < 1 * eps.
Proof.
  intros Hball. repeat red in Hball.
  rewrite Rmult_1_l. apply Hball. 
Qed.


Lemma Rfct_norm_scal_aux:
  forall (l : R) (f : Rfct A), Rmax_norm A (scal l f) <= Rabs l * Rmax_norm A f .
Proof.
  intros r f.
  unfold Rmax_norm.
  unfold scal. simpl. unfold Rfct_scal.
  destruct finA as [ls Hls]. 
  destruct (is_nil_dec ls).
  - subst ; simpl. lra.  
  - rewrite Rmax_list_le_iff.
    intros x Hx. rewrite in_map_iff in Hx.
    destruct Hx as [a [Ha Hina]].
    rewrite <-Ha. rewrite Rabs_mult.
    apply Rmult_le_compat.
    -- apply Rabs_pos.
    -- apply Rabs_pos.
    -- now right.
    -- apply Rmax_spec. rewrite in_map_iff. exists a ; split ; trivial.
    -- rewrite map_not_nil. now apply ne_symm.
Qed.
  
Lemma Rfct_norm_eq_0: forall (f:Rfct A), (Rmax_norm A f) = 0 -> f = zero.
Proof.
  intros f H.
  apply Rfct_eq_ext.  
  intro x. unfold Rmax_norm in H.
  destruct finA as [ls Hls].
  assert (forall s : A, Rabs (f s) <= 0).
  intros a. 
  rewrite <- H. simpl. apply Rmax_spec.
  rewrite in_map_iff. exists a. split ; trivial.
  assert (forall s : A, 0 <= Rabs (f s)). intro s. apply Rabs_pos.
  assert (forall s : A, Rabs (f s) = 0). intro s. apply Rle_antisym ; eauto.
  apply Rabs_eq_0 ; auto.
Qed.



Definition Rfct_NormedModule_mixin :=
  NormedModule.Mixin R_AbsRing Rfct_NormedModuleAux (Rmax_norm A) 1%R Rfct_norm_triangle Rfct_norm_scal_aux 
  Rfct_norm_ball1 Rfct_norm_ball2 Rfct_norm_eq_0.

Canonical Rfct_NormedModule :=
  NormedModule.Pack R_AbsRing (Rfct A)
     (NormedModule.Class _ _ _ Rfct_NormedModule_mixin) (Rfct A).

End Rfct_NormedModule.


Section Rfct_open_closed.

  (* 
     Note: this section uses Classical reasoning. In particular, the theorems
     Classical_Pred_Type.not_ex_not_all and its variants. 
     This arises since in order to prove a set closed, we prove it's complement open. 
     The sets in question are {g | g >= f} and {g | g <= f}. We use classical reasoning
     to construct the existential from the negated forall. 
     The alternative is to use filters to prove sets closed. (I don't know if this is 
     entirely intuitionistic.)
  *)
  Context (A : Type) {finA : Finite A}.

  (* The Max norm topology is compatible with the Euclidean topology induced from R.*)
  Lemma Rmax_ball_compat (f g : Rfct A) (eps : posreal) :
  ball f eps g <-> Rmax_ball A f eps g.
  Proof.
    split. 
    -- intros Hball. unfold Rmax_ball. unfold Rmax_norm.
       destruct finA as [ls Hls]. 
       destruct (is_nil_dec ls).
    - subst ; simpl. apply cond_pos.
    - rewrite Rmax_list_lt_iff.
      intros x Hx.
      rewrite in_map_iff in Hx.
      destruct Hx as [a [Ha Hina]].
      specialize (Hball a). rewrite <-Ha.
      apply Hball.  
      rewrite map_not_nil. now rewrite ne_symm.
      -- intros Hball. unfold Rmax_ball in Hball. unfold Rmax_norm in Hball.
         destruct finA as [ls Hls]. intro a.
         destruct (is_nil_dec ls).
    - subst ; simpl. unfold Rfct in f,g.  specialize (Hls a).
      simpl in Hls. now exfalso.
    - repeat red. eapply Rle_lt_trans ; last apply Hball.     
      apply Rmax_spec. rewrite in_map_iff. exists a.
      split ; trivial.                             
  Qed.

  Lemma Rmax_open_compat (ϕ : Rfct A -> Prop) :
    open ϕ <-> @open (Rfct_UniformSpace A) ϕ.
  Proof.
    unfold open, locally, ball, fct_ball. simpl.
    setoid_rewrite Rmax_ball_compat.
    split ; trivial. 
  Qed.
  
  Lemma forall_lt {f g} {ne : NonEmpty A} : (forall a : A, g a < f a) -> (0 < Rmax_norm A (fun a => minus (f a) (g a))).
  Proof.
    intros Ha.
    setoid_rewrite Rminus_lt_0 in Ha.
    unfold Rmax_norm. destruct finA as [ls Hls]. 
    destruct (Rmax_list_map_exist (fun a => Rabs (minus (f a) (g a))) ls) as [a' [Hina' Ha']].
    - rewrite not_nil_exists. exists ne ; trivial. 
    - rewrite <-Ha', Rabs_pos_eq. specialize (Ha a').
      ++ apply Ha.
      ++ now left.              
  Qed.       

  Lemma le_max {f h} : (forall a : A, h a > Rmax_norm A f) -> (forall a : A, h a > f a).
  Proof.
    intros Ha a.
    destruct finA as [ls Hls]. 
    eapply Rle_lt_trans. apply Rle_abs.
    eapply Rle_lt_trans ; last apply Ha.
    unfold Rmax_norm. apply Rmax_spec.
    rewrite in_map_iff.  exists a.
    split ; trivial.
  Qed.

  
  Global Instance closed_Proper :
    Proper (pointwise_relation (Rfct_UniformSpace A) iff ==> Basics.impl) closed.
  Proof.
  intros x y H H0.
  eapply closed_ext ; eauto.
  Qed.
  
  Global Instance closed_Proper_flip :
    Proper (pointwise_relation (Rfct_UniformSpace A) iff ==> Basics.flip Basics.impl) closed.
  Proof.
  intros x y H H0.
  eapply closed_ext ; eauto. symmetry.
  apply H.
  Qed.

   Global Instance open_Proper :
    Proper (pointwise_relation (Rfct_UniformSpace A) iff ==> Basics.impl) open.
  Proof.
  intros x y H H0.
  eapply open_ext ; eauto.
  Qed.
  
  Global Instance open_Proper_flip :
    Proper (pointwise_relation (Rfct_UniformSpace A) iff ==> Basics.flip Basics.impl) open.
  Proof.
  intros x y H H0.
  eapply open_ext ; eauto. symmetry.
  apply H.
  Qed.

  Theorem lt_open (f : Rfct A) : @open (Rfct_UniformSpace A) (fun g => (exists a, g a < f a)). 
  Proof.
    rewrite <-Rmax_open_compat.
    unfold open, locally, ball. simpl.
    unfold fct_ball, ball. simpl.
    intros g Hgf. unfold AbsRing_ball. simpl.
    setoid_rewrite Rminus_lt_0 in Hgf.
    destruct Hgf as [a0 Ha0].
    pose (eps := mkposreal _ Ha0).
    exists (mkposreal _ (is_pos_div_2 eps)).
    simpl.  intros y Hyg.
    exists a0. rewrite Rminus_lt_0. 
    assert (h1 : (f a0 - g a0)  = ((f a0 - y a0) + (y a0 - g a0))) by ring.
    clear eps. 
    rewrite h1 in Ha0.
    assert (h2 : (f a0 - y a0) + (y a0 - g a0) <= (f a0 - y a0) + Rabs(y a0 - g a0)).
    {
      apply Rplus_le_compat_l. apply Rle_abs.
    }
    assert (h3 : (f a0 - y a0) +  Rabs (y a0 - g a0) <= (f a0 - y a0) + (f a0 - g a0) / 2).
    {
      apply Rplus_le_compat_l. left. apply Hyg.
    }
    assert (h4 : f a0 - g a0  <= f a0 - y a0 + (f a0 - g a0) / 2).
    {
      eapply Rle_trans. rewrite h1. apply h2.
      apply h3. 
    }
    assert (h5 : (f a0 - g a0)/2 <= f a0 - y a0).
    {
      rewrite <-Rle_minus_l in h4. 
      now field_simplify in h4. 
    }
    specialize (Hyg a0). eapply Rlt_le_trans ; last apply h5.
    eapply Rle_lt_trans ; last apply Hyg.
    apply Rabs_pos.
  Qed.

  Theorem ge_closed (f : Rfct A) :
    @closed (Rfct_UniformSpace A) (fun g => Rfct_ge A g f).
  Proof.
    unfold Rfct_ge.
    setoid_rewrite Rfct_ge_not_lt.
    apply closed_not. apply lt_open.
  Qed. 

    Theorem gt_open (f : Rfct A) : @open (Rfct_UniformSpace A) (fun g => (exists a, g a > f a)). 
  Proof.
    rewrite <-Rmax_open_compat.
    unfold open, locally, ball. simpl.
    unfold fct_ball, ball. simpl.
    intros g Hgf. unfold AbsRing_ball.
    setoid_rewrite Rminus_lt_0 in Hgf.
    destruct Hgf as [a0 Ha0].
    pose (eps := mkposreal _ Ha0).
    exists (mkposreal _ (is_pos_div_2 eps)).
    simpl.  intros y Hyg.
    exists a0. apply Rminus_gt. 
    assert (h1 : (g a0 - f a0)  = ((g a0 - y a0) + (y a0 - f a0))) by ring.
    clear eps. 
    rewrite h1 in Ha0.
    assert (h2 : (g a0 - y a0) + (y a0 - f a0) <= Rabs(g a0 - y a0) + (y a0 - f a0)).
    {
      apply Rplus_le_compat_r. apply Rle_abs.
    }
    assert (h3 : Rabs(g a0 - y a0) + (y a0 - f a0) <= ((g a0 - f a0) / 2) + (y a0 - f a0)).
    {
      rewrite Rabs_minus_sym. apply Rplus_le_compat_r. left. apply Hyg.
    }
    assert (h4 : (g a0 - f a0)  <= (g a0 - f a0) / 2 + (y a0 - f a0)).
    {
      eapply Rle_trans. rewrite h1. apply h2.
      apply h3. 
    }
    assert (h5 : (g a0 - f a0)/2 <= y a0 - f a0).
    {
      rewrite Rplus_comm in h4.
      rewrite <-Rle_minus_l in h4. 
      field_simplify in h4. lra.
    }
    specialize (Hyg a0). eapply Rlt_le_trans ; last apply h5.
    eapply Rle_lt_trans ; last apply Hyg.
    apply Rabs_pos.
  Qed.

    Theorem le_closed (f : Rfct A) :
    @closed (Rfct_UniformSpace A) (fun g => Rfct_le A g f).
  Proof.
    unfold Rfct_le.
    setoid_rewrite Rfct_le_not_gt.
    apply closed_not. apply gt_open.
  Qed. 

End Rfct_open_closed.


Global Instance Filter_prop {A} (fin : Finite A) (F : (Rfct_UniformSpace A -> Prop) -> Prop) (ff : Filter F) :
Proper (pointwise_relation (Rfct_UniformSpace A) iff ==> Basics.flip Basics.impl) F.
  Proof.
    intros A' B' Ha.
    unfold Basics.flip, Basics.impl.
    apply filter_imp.
    intro a. specialize (Ha a).
    now destruct Ha.
  Qed.
  
Section Rfct_CompleteSpace.

  (* The function type A -> R is a complete uniform space.  *)

  Context (A : Type) {finA : Finite A}.

  Lemma close_lim_Rfct :
    forall F1 F2, filter_le F1 F2 -> filter_le F2 F1 -> @close (Rfct_UniformSpace A) (lim_fct F1) (lim_fct F2).
  Proof.
    intros F1 F2 H H0. unfold close. intros eps.
    apply Rmax_ball_compat.
    apply (close_lim_fct F1 F2 H H0 eps).
  Qed.

  Lemma complete_cauchy_Rfct : forall F : (Rfct_UniformSpace A -> Prop) -> Prop,
      ProperFilter F ->
      (forall (eps : posreal), exists f, F (Rmax_ball A f eps))
      -> forall eps : posreal, F (Rmax_ball A (lim_fct F) eps).
  Proof.   
    intros F ProperF CauchyF eps.
    eapply filter_imp.
    - intro f. now rewrite <-Rmax_ball_compat. 
    - setoid_rewrite <-Rmax_ball_compat.
      set (complete_cauchy_fct F). apply f ; trivial.
      intros eps'. destruct (CauchyF eps') as [f' Hf'].
      exists f'. 
      eapply filter_imp ; last apply Hf'.
      intros h Hmax. now apply Rmax_ball_compat.
  Qed.
  
  Definition Rfct_CompleteSpace_mixin :=
  CompleteSpace.Mixin (Rfct_UniformSpace A) lim_fct complete_cauchy_Rfct close_lim_Rfct.

  Canonical Rfct_CompleteSpace :=
  CompleteSpace.Pack (Rfct A) (CompleteSpace.Class _ _ Rfct_CompleteSpace_mixin) (Rfct A).

  Canonical Rfct_CompleteNormedModule :=
  CompleteNormedModule.Pack _  (Rfct A) (CompleteNormedModule.Class R_AbsRing _ (NormedModule.class _ (Rfct_NormedModule A)) Rfct_CompleteSpace_mixin) (Rfct A).

End Rfct_CompleteSpace.

Section fixpt.

  (* Properties about fixed points of contractive maps in complete normed modules.
     In this section we use the banach fixed point theorem as proven in the 
     Elfic library which proved the Lax-Milgram theorem. 
     Remove this into it's own metric_coinduction.v file.
   *)
  Context {K : AbsRing}{X : CompleteNormedModule K}.
  
  Definition fixpt (F : X -> X) (init : X) :=
    lim (fun P => eventually (fun n => P (fixed_point.iter F n init))).
  
  Context {F : X -> X} (hF : is_contraction F) (phi : X -> Prop)
          (fphi : forall x : X, phi x -> phi (F x))
          (phic : closed phi).
  
  Lemma fixpt_init_unique {init1 init2 : X} (Hphi1 : phi init1) (Hphi2 : phi init2):
    fixpt F init1 = fixpt F init2.
  Proof.
    assert (my_complete phi) by (now apply closed_my_complete).
    destruct (FixedPoint K F phi fphi (ex_intro _ _ Hphi1) H hF) as [? [? [? [? Hsub]]]].
    unfold fixpt.
    rewrite Hsub ; auto. rewrite Hsub ; auto.
  Qed.

  (* The subset ϕ is nonempty. *)
  Context (init: NonEmpty X) (init_phi: phi init).
  
  Lemma fixpt_is_fixpt : F (fixpt F init) = fixpt F init.
  Proof.
    assert (my_complete phi) by (now apply closed_my_complete).
    destruct (FixedPoint K F phi fphi (ex_intro _ _ init_phi) H hF) as [? [? [? [? Hsub]]]].
    specialize (Hsub init init_phi).
    unfold fixpt. now rewrite Hsub.
  Qed.
  
  Lemma fixpt_is_unique :
    forall g : X, phi g -> F g = g -> g = fixpt F init.
  Proof.
    assert (my_complete phi) by (now apply closed_my_complete).
    destruct (FixedPoint K F phi fphi (ex_intro _ _ init_phi) H hF) as [? [? [? [? Hsub]]]].
    specialize (Hsub init init_phi).    
    unfold fixpt. now rewrite Hsub.
  Qed.

  (* 
     Kozen's metric coinduction principle. 
     Equation (2.1) of https://arxiv.org/pdf/0908.2793.pdf
   *)
  Theorem metric_coinduction : phi (fixpt F init).
  Proof. 
    assert (my_complete phi) by (now apply closed_my_complete).
    destruct (FixedPoint K F phi fphi (ex_intro _ _ init_phi) H hF) as [? [Hin [? [? Hsub]]]].
    specialize (Hsub init init_phi).
    rewrite <-Hsub in Hin.
    unfold fixpt.
    apply Hin. 
  Qed.
  
End fixpt. 


Section contraction_coinduction. 

  (* 
     We specialize Kozen's metric coinduction principle to our ordered uniform space
     Rfct_Uniformspace. Our subset ϕ will be the nonempty closed sets {g | g <= f} or
     {g | g >= f}. The operator F being monotonic also means that it preserves these
     sets. 
  *)
  Context (A : Type) {finm : Finite A}.

  Lemma monotone_le_preserv (F : Rfct A -> Rfct A) (f : Rfct A) :
      monotone_le A F -> (Rfct_le A (F f) f) -> (forall g, Rfct_le A g f -> Rfct_le A (F g) f).
  Proof.
    intros Hm Hle g Hgf.
    unfold monotone_le in Hm.
    unfold Rfct_le in *.
    specialize (Hm g f Hgf) ; clear Hgf.
    intro a. specialize (Hm a). specialize (Hle a).
    eapply Rle_trans ; first apply Hm. assumption.
  Qed.

  Lemma monotone_ge_preserv (F : Rfct A -> Rfct A) (f : Rfct A) :
      monotone_ge A F -> (Rfct_ge A (F f) f) -> (forall g, Rfct_ge A g f -> Rfct_ge A (F g) f).
  Proof.
    intros Hm Hge g Hgf.
    unfold monotone_ge in Hm.
    unfold Rfct_ge in *.
    specialize (Hm g f Hgf) ; clear Hgf.
    intro a. specialize (Hm a). specialize (Hge a).
    eapply Rge_trans ; first apply Hm. assumption.
  Qed.

  (* 
     Contraction coinduction proof principles.
     Theorem 1 in https://homepage.tudelft.nl/c9d1n/papers/cmcs-2018.pdf
   *)
  Theorem contraction_coinduction_Rfct_le
          {F} (hF : @is_contraction (Rfct_CompleteSpace A) (Rfct_CompleteSpace A) F)
          (hM : monotone_le A F)    
    : forall f init, Rfct_le A (F f) f -> Rfct_le A (fixpt F init) f. 
  Proof.
    intros f init Hfle.
    replace (fixpt F init) with (fixpt F f).
    apply (metric_coinduction hF (fun g => Rfct_le _ g f)).
    - now apply monotone_le_preserv. 
    - apply le_closed.
    - intro a. now right.
    - apply (fixpt_init_unique hF (fun _ => True)) ; trivial.
      apply closed_true.
  Qed.

  Theorem contraction_coinduction_Rfct_ge
          {F} (hF : @is_contraction (Rfct_CompleteSpace A) (Rfct_CompleteSpace A) F)
          (hM : monotone_ge A F)    
    : forall f init, Rfct_ge A (F f) f -> Rfct_ge A (fixpt F init) f. 
  Proof.
    intros f init Hfle.
    replace (fixpt F init) with (fixpt F f).
    apply (metric_coinduction hF (fun g => Rfct_ge _ g f)).
    - now apply monotone_ge_preserv. 
    - apply ge_closed.
    - intro a ; now right.
    - apply (fixpt_init_unique hF (fun _ => True)) ; trivial.
      apply closed_true.
  Qed.
 
End contraction_coinduction. 


Section ltv.

  (* 
     We specialize the above theory to MDPs and long-term values. 
     This section formalizes page 4 of 
     https://homepage.tudelft.nl/c9d1n/papers/cmcs-2018.pdf
   *)
Open Scope R_scope. 
Context {M : MDP} (γ : R).
Context (σ : dec_rule M) (init : M.(state)) (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.


Global Instance Series_proper :
  Proper (pointwise_relation _ eq  ==> eq) (Series).
Proof.
  unfold Proper, pointwise_relation, respectful.
  apply Series_ext.
Qed.

Definition ltv_part (N : nat) := sum_n (fun n => γ^n * (expt_reward σ init n)) N. 

Lemma ltv_part0_eq_reward : ltv_part 0 = (step_expt_reward σ init).
Proof.
  unfold ltv_part. rewrite sum_n_Reals. simpl.  
  rewrite expt_reward0_eq_reward. lra.
Qed.

Lemma sum_mult_geom (D : R) : infinite_sum (fun n => D*γ^n) (D/(1 - γ)).
Proof.
  rewrite infinite_sum_infinite_sum'.
  apply infinite_sum'_mult_const.
  rewrite <- infinite_sum_infinite_sum'.
  apply is_series_Reals. apply is_series_geom.
  rewrite Rabs_pos_eq. lra. lra. 
Qed.

Lemma ex_series_mult_geom (D:R) : ex_series (fun n => D*γ^n).
Proof.
  exists (D/(1-γ)). 
  rewrite is_series_Reals. 
  apply sum_mult_geom.
Qed.


Lemma ltv_part_le_norm {D : R} (N : nat) :
   (forall s s': M.(state), Rabs (reward s (σ s) s') <= D) -> Rabs(ltv_part N) <= sum_f_R0 (fun n => γ^n * D) N.
Proof.
  intros Hd.
  unfold ltv_part. rewrite sum_n_Reals.
  refine (Rle_trans _ _ _ _ _ ).
  apply sum_f_R0_triangle. 
  apply sum_Rle. 
  intros n0 Hn0. 
  rewrite Rabs_mult.
  enough (Hγ : Rabs (γ^n0) = γ^n0). rewrite Hγ.
  apply Rmult_le_compat_l.
  apply pow_le ; firstorder.
  apply expt_reward_le_max_Rabs ; try assumption.
  apply Rabs_pos_eq. apply pow_le. firstorder. 
Qed.

Theorem ex_series_ltv {D : R} :
   (forall s s': M.(state), Rabs (reward s (σ s) s') <= D) -> (forall s0, ex_series (fun n => γ^n * (expt_reward σ s0 n))).
Proof.
  intros Hbdd s0. 
  refine (ex_series_le_Reals _ _ _ _). 
  intros n. rewrite Rabs_mult.
  enough (Rabs (γ ^ n) * Rabs (expt_reward σ s0 n) <= D*γ^n). apply H.
  enough (Hγ : Rabs (γ^n) = γ^n). rewrite Hγ.
  rewrite Rmult_comm. apply Rmult_le_compat_r.
  apply pow_le; firstorder.
  apply (expt_reward_le_max_Rabs) ; try assumption. 
  apply Rabs_pos_eq ; apply pow_le; firstorder.
  apply (ex_series_mult_geom D). 
Qed.

Definition ltv : M.(state) -> R:= fun s => Series (fun n => γ^n * (expt_reward σ s n)).
  
Definition expt_ltv (p : Pmf M.(state)) : R :=
  expt_value p ltv.

Lemma Pmf_bind_comm_stoch_bind (n : nat) :
  Pmf_bind (bind_stoch_iter σ n init) (fun a : state M => t a (σ a)) =
  Pmf_bind (t init (σ init)) (fun a : state M => bind_stoch_iter σ n a).
Proof.
    induction n.
  * unfold bind_stoch_iter. simpl. rewrite Pmf_bind_of_ret.  now rewrite Pmf_ret_of_bind.
  * unfold bind_stoch_iter in *. simpl.  setoid_rewrite IHn.
    rewrite Pmf_bind_of_bind. reflexivity.
Qed.


(* Long-Term Values satisfy the Bellman equation.
   Proposition 3 of http://researchers.lille.inria.fr/~lazaric/Webpage/MVA-RL_Course14_files/notes-lecture-02.pdf
 *)
Lemma ltv_corec {D : R} :
   (forall s s': M.(state), Rabs (reward s (σ s) s') <= D) ->
  ltv init = (step_expt_reward σ init) + γ*expt_value (t init (σ init)) ltv. 
Proof.
  intros bdd. 
  rewrite <-(@expt_reward0_eq_reward _ σ init).
  unfold ltv.
  rewrite Series_incr_1. simpl. rewrite Rmult_1_l. setoid_rewrite Rmult_assoc.   
  rewrite Series_scal_l. f_equal. 
  setoid_rewrite expt_reward_succ. 
  rewrite expt_value_Series. f_equal.  
  apply Series_ext. intros n.
  rewrite expt_value_const_mul. f_equal. 
  rewrite <-expt_value_bind. rewrite Pmf_bind_comm_stoch_bind.
  unfold expt_reward. 
  rewrite expt_value_bind.  reflexivity.
  apply (ex_series_ltv bdd).
  apply (ex_series_ltv bdd). 
Qed.



End ltv.

Section operator.


  (* 
     Proofs that the bellman operator and maximal bellman operator are contractions 
     in the Complete Normed Module M.(state) -> R. 
     Some proofs are from 
     http://researchers.lille.inria.fr/~lazaric/Webpage/MVA-RL_Course14_files/notes-lecture-02.pdf
   *)
  
Open Scope R_scope. 
Context {M : MDP} (γ D : R).
Context (hγ : (0 <= γ < 1)%R).

Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Context (bdd :  (forall s s': M.(state), forall σ : dec_rule M, Rabs (reward s (σ s) s') <= D)).

Definition bellman_op (π : dec_rule M) : @Rfct M.(state) (fs M) -> @Rfct M.(state) (fs M) :=
  fun W => fun s => (step_expt_reward π s + γ*(expt_value (t s (π s)) W)). 


Theorem is_contraction_bellman_op (π : dec_rule M) :
 @is_contraction (Rfct_UniformSpace M.(state)) (Rfct_UniformSpace M.(state)) (bellman_op π).
Proof.
  unfold is_contraction.
  destruct (Req_EM_T γ 0). 
  ++ unfold bellman_op.
     exists (1/2). split ; [lra | ].
     unfold is_Lipschitz. split ; trivial ; [lra | ].
     destruct (fs M) as [ls Hls].
     intros f g. intros r Hr Hfgr.
     rewrite e. unfold ball_x,ball_y, Rmax_norm.
     simpl. unfold Rmax_ball. simpl. 
     replace (fun s : state M => Rabs
     (minus (step_expt_reward π s + 0 * expt_value (t s (π s)) g)
            (step_expt_reward π s + 0 * expt_value (t s (π s)) f))) with (fun x:state M => 0).
     rewrite Rmax_list_zero. replace 0 with (1/2 * 0) by lra.
     apply Rmult_lt_compat_l ; [lra |trivial].
     apply functional_extensionality. intro x.
     do 2 rewrite Rmult_0_l. rewrite Rplus_0_r.
     rewrite minus_eq_zero.
     symmetry. apply Rabs_R0.
  ++
    exists γ ; split.
  - now destruct hγ.
  - unfold is_Lipschitz.
    unfold ball_x,ball_y. simpl.
    destruct (fs M) as [ls Hls].
    split.
    -- now destruct hγ. 
    -- intros f g r Hr Hx.
       repeat red in Hx. repeat red.
       unfold Rmax_norm in *. 
       destruct (is_nil_dec ls).
       --- rewrite e ; simpl. apply Rmult_lt_0_compat; [firstorder |trivial].
       ---
         assert (h1 :  Max_{ ls}(fun s => Rabs (minus (bellman_op π g s) (bellman_op π f s))) =  γ*Max_{ ls}(fun s => Rabs (expt_value (t s (π s)) (fun s => g s - f s)))).
       {
         rewrite <-Rmax_list_map_const_mul ; [| now destruct hγ].
         f_equal.
         apply map_ext. rewrite <-(Rabs_pos_eq γ) ; [ | now destruct hγ].
         intro s. 
         rewrite <-Rabs_mult.
         f_equal. unfold bellman_op,minus,plus,opp ; simpl.
         rewrite expt_value_sub. ring.
       }
       rewrite h1.
       apply Rmult_lt_compat_l ; [firstorder|].
       rewrite Rmax_list_lt_iff ; [| rewrite map_not_nil ; congruence].
       intros r0 Hin. rewrite in_map_iff in Hin.
       destruct Hin as [a0 [Ha0 Hina0]].
       rewrite <-Ha0. eapply Rle_lt_trans ; last apply Hx.
       eapply Rle_trans. apply expt_value_Rabs_Rle.
       simpl. apply expt_value_bdd.
       intro s. apply Rmax_spec.
       rewrite in_map_iff. exists s ; split ; trivial.
Qed.

Lemma ltv_bellman_eq_ltv : forall π, ltv γ π = bellman_op π (ltv γ π).
Proof.
  intro π.
  unfold bellman_op. simpl.
  apply functional_extensionality.
  intro init.
  eapply ltv_corec ; eauto.
Qed.

Lemma ltv_bellman_op_fixpt : forall π init, ltv γ π = fixpt (bellman_op π) init.
Proof.
  intros π init.
  apply (fixpt_is_unique (is_contraction_bellman_op π) (fun x => True)) ; trivial.
  - apply closed_true.
  - now rewrite <-ltv_bellman_eq_ltv.
Qed.


Lemma bellman_op_monotone_le (π : dec_rule M) : monotone_le M.(state) (bellman_op π). 
Proof.
  intros W1 W2 HW1W2 s.
  unfold bellman_op. 
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l ; intuition.
  apply expt_value_le ; eauto.
Qed.

Lemma bellman_op_monotone_ge (π : dec_rule M) : monotone_ge M.(state) (bellman_op π). 
Proof.
  intros W1 W2 HW1W2 s.
  unfold bellman_op.
  apply Rle_ge.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l ; intuition.
  apply expt_value_le ; eauto.
  intros a. apply Rge_le. apply HW1W2.
Qed.

Definition bellman_max_op : @Rfct M.(state) (fs M) -> @Rfct M.(state) (fs M)
  := 
    fun W => fun s => let (la,_) := fa M s in
                Max_{la}( fun a => expt_value (t s a) (reward s a) + γ*(expt_value (t s a) W)). 


Lemma bellman_max_op_monotone_le :
  (monotone_le M.(state) (bellman_max_op)).
Proof.
  intros W1 W2 HW1W2 s.
  unfold bellman_max_op. destruct (fa M s) as [la Hla]. 
  apply Rmax_list_fun_le ; auto. 
  intro a.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l ; intuition.
  apply expt_value_le ; eauto.
Qed.

Lemma bellman_max_op_monotone_ge :
  (monotone_ge M.(state) bellman_max_op).
Proof.
  intros W1 W2 HW1W2 s.
  rewrite <-Rfct_le_ge_symm in HW1W2.
  apply Rle_ge.
  unfold bellman_max_op. destruct (fa M s) as [la Hla].
  apply Rmax_list_fun_le ; auto. 
  intro a.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l ; intuition.
  apply expt_value_le ; eauto.
Qed.


Lemma bellman_op_bellman_max_le (π : dec_rule M) :
  forall W, Rfct_le M.(state) (bellman_op π W) (bellman_max_op W).
Proof.
  intros W s.  
  unfold bellman_op. 
  unfold bellman_max_op.
  unfold step_expt_reward. destruct (fa M s) as [la Hla]. 
  apply Rmax_spec.
  rewrite in_map_iff. exists (π s). split ; trivial.
Qed.


 (*
   Proposition 5 of http://researchers.lille.inria.fr/~lazaric/Webpage/MVA-RL_Course14_files/notes-lecture-02.pdf
  *)
Theorem is_contraction_bellman_max_op
        :
 @is_contraction (Rfct_UniformSpace M.(state)) (Rfct_UniformSpace M.(state)) bellman_max_op.
Proof.
  unfold is_contraction.
  destruct (Req_EM_T γ 0).
   +++ unfold bellman_max_op.
     exists (1/2). split ; [lra | ].
     unfold is_Lipschitz. split ; trivial ; [lra | ].
     destruct (fs M) as [ls Hls].
     intros f g. intros r Hr Hfgr.
     rewrite e. unfold ball_x,ball_y, Rmax_norm.
     simpl. unfold Rmax_ball. simpl.
     replace _ with 0. 
     replace 0 with (1/2 * 0) by lra.
     apply Rmult_lt_compat_l ; [lra |trivial].
     symmetry. rewrite <-(Rmax_list_zero ls).
     f_equal. apply map_ext. intro s0.
     destruct (fa M s0) as [la Hla]. rewrite <-Rabs_R0.
     f_equal. rewrite Rabs_R0. rewrite Rmax_list_zero.
     unfold minus,plus,opp ; simpl. apply Rminus_diag_eq.
     f_equal. apply map_ext.
     intro a. ring.
  +++ exists γ ; split.
  - now destruct hγ.
  - unfold is_Lipschitz. split.
    ++ now destruct hγ.
    ++ intros f g r Hr Hfg.
       repeat red in Hfg. repeat red.
       unfold Rmax_norm in *. destruct (fs M) as [ls Hls].
       destruct (is_nil_dec ls).
       --- subst ; simpl in *. exfalso. apply Hls.
           apply ne.  
       --- rewrite Rmax_list_lt_iff ; [ | apply map_not_nil ; congruence].
           intros r' Hr'.
           rewrite in_map_iff in Hr'. destruct Hr' as [s [Hs Hins]].
           rewrite <-Hs. unfold minus,plus,opp,bellman_max_op ; simpl.
           destruct (fa M s) as [la Hla]. 
           eapply Rle_lt_trans ; first apply Rmax_list_minus_le_abs.
           simpl. repeat red in f,g.
           assert
             (h1 : Max_{ la }(fun a => Rabs (expt_value (t s a) (reward s a) + γ * expt_value (t s a) g - (expt_value (t s a) (reward s a) + γ * expt_value (t s a) f))) = Max_{ la } (fun a => γ*Rabs ((expt_value (t s a) g - expt_value (t s a) f)))).
           {
           f_equal. apply List.map_ext_in.
           intros a H. replace (γ * Rabs (expt_value (t s a) g - expt_value (t s a) f)) with
            (Rabs (γ) * Rabs (expt_value (t s a) g - expt_value (t s a) f)).
           rewrite <-Rabs_mult. f_equal. ring. 
           f_equal. apply Rabs_pos_eq. now destruct hγ.
           }
           rewrite h1; clear h1.
           rewrite Rmax_list_map_const_mul ; [|now destruct hγ].
           assert (h2: Max_{ la }(fun a : act M s => Rabs (expt_value (t s a) g - expt_value (t s a) f))
             = Max_{ la}(fun a : act M s => Rabs (expt_value (t s a)(fun s => g s - f s)))).
           {
             symmetry. f_equal. apply List.map_ext_in.
             intros. f_equal. apply expt_value_sub. 
           }
           rewrite h2 ; clear h2.
           assert (h3 : γ * (Max_{ la }(fun a : act M s => Rabs (expt_value (t s a) (fun s0 : state M => g s0 - f s0)))) <= γ*(Max_{ la }(fun a : act M s => (expt_value (t s a) (fun s0 : state M => Rabs (g s0 - f s0)))))).
           {
           apply Rmult_le_compat_l; [now destruct hγ| ].
           apply Rmax_list_fun_le. intro a. apply expt_value_Rabs_Rle.
           }
           eapply Rle_lt_trans; first apply h3. clear h3.
           apply Rmult_lt_compat_l ; [firstorder|]. (* Have to use γ <> 0 here.*)
           destruct (is_nil_dec (la)) ;[ rewrite e ; simpl ; assumption |]. 
           rewrite Rmax_list_lt_iff ; [| rewrite map_not_nil ; congruence].
           intros r0 Hin. rewrite in_map_iff in Hin.
           destruct Hin as [a0 [Ha0 Hina0]].
           rewrite <-Ha0. eapply Rle_lt_trans ; last apply Hfg.
           apply expt_value_bdd. intro s0. apply Rmax_spec.
           rewrite in_map_iff. exists s0 ; split ; trivial.
Qed. 

(*
  Fixed Point of the maximal bellman operator is an upper bound of all long-term value
  functions. Lemma 1 from http://researchers.lille.inria.fr/~lazaric/Webpage/MVA-RL_Course14_files/notes-lecture-02.pdf
  The proof uses a contraction coinductive proof rule. 
 *)
Lemma ltv_Rfct_le_fixpt (π : dec_rule M) :
 forall init, Rfct_le M.(state) (ltv γ π) (fixpt (bellman_max_op) init). 
Proof.
  intros init.
  set (Hπ' := bellman_op_bellman_max_le π (ltv γ π)).
  rewrite <-ltv_bellman_eq_ltv in Hπ'. rewrite Rfct_le_ge_symm in Hπ'.
  rewrite Rfct_le_ge_symm.
  apply (contraction_coinduction_Rfct_ge).
  - apply is_contraction_bellman_max_op ; eauto.
  - apply bellman_max_op_monotone_ge.
  - assumption.
Qed.

Definition greedy init: dec_rule M :=
  fun s => let V' := fixpt bellman_max_op in
        let (la,Hla) := fa M s in
        let pt := na M s in  
        @argmax (act M s) la (proj2 (not_nil_exists _) (ex_intro _ pt (Hla pt)))
                (fun a => expt_value (t s a) (reward s a) +
                       γ*(expt_value (t s a) (V' init))).

Lemma exists_fixpt_policy_aux :
  forall init,
  let V' :=  fixpt bellman_max_op in
  let σ' := greedy init in
  bellman_op σ' (V' init) = V' init.
Proof.
  intros init V' σ'.
  apply functional_extensionality.
  intro s0.
  unfold σ', greedy, bellman_op, step_expt_reward,V'.
  destruct (M s0). 
   rewrite (argmax_is_max _ (fun a =>  expt_value (t s0 a) (reward s0 a) + γ * expt_value (t s0 a) (fixpt (bellman_max_op) init))). 
  replace ( Max_{elms} (fun a => expt_value (t s0 a) (reward s0 a) + γ * expt_value (t s0 a) (fixpt (bellman_max_op) init))) with (bellman_max_op (fixpt (bellman_max_op) init) s0).
  apply equal_f. apply (fixpt_is_fixpt (is_contraction_bellman_max_op) (fun _ => True)) ; trivial.
  apply closed_true.
  unfold bellman_max_op. destruct (M s0).
  assert (H : equivlist elms elms0) by (intros ; split ; trivial).
  now rewrite H.
Qed.

(*
  The greedy policy is optimal.
  Proposition 1 from http://researchers.lille.inria.fr/~lazaric/Webpage/MVA-RL_Course14_files/notes-lecture-02.pdf
  The proof uses a contraction coinductive proof rule. 
 *)
Lemma exists_fixpt_policy  : forall init,
  let V' :=  fixpt (bellman_max_op) in
  let σ' := greedy init in
  ltv γ σ' = V' init.
Proof.
  intros init V' σ'. apply functional_extensionality.
  intro s0. 
  apply Rle_antisym.
  - eapply ltv_Rfct_le_fixpt ; eauto.
  - revert s0.
    change _ with (Rfct_le _ (fixpt (bellman_max_op) init) (ltv γ (greedy init))).
    rewrite Rfct_le_ge_symm.
    rewrite (ltv_bellman_op_fixpt _ init).
    apply contraction_coinduction_Rfct_ge.
    ++ apply is_contraction_bellman_op.
    ++ apply bellman_op_monotone_ge.
    ++ intro init0. 
       right. apply equal_f.
       eapply exists_fixpt_policy_aux ; eauto.
Qed.

End operator.


Section order.
  
Open Scope R_scope. 
Context {M : MDP} (γ D : R).
Context (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Context (bdd :  (forall s s': M.(state), forall σ : dec_rule M, Rabs (reward s (σ s) s') <= D)).

Definition policy_eq (σ τ : forall s : state M ,act M s) : Prop
  := forall s, (@ltv M γ σ s) = (@ltv M γ τ s).

Global Instance policy_eq_equiv : Equivalence policy_eq.
Proof.
  constructor; repeat red; intros.
  reflexivity.
  now symmetry.
  etransitivity; eauto.
Qed.

Definition policy_le (σ τ : forall s : state M ,act M s) : Prop
  := forall s, (ltv γ σ s) <= (ltv γ τ s).

Global Instance policy_equiv_sub : subrelation policy_eq policy_le.
Proof.
  unfold policy_eq, policy_le, subrelation; intros.
  specialize (H s); lra.
Qed.

(* Shift this to RealAdd. *)
Global Instance Rle_trans : Transitive Rle.
Proof.
  repeat red; intros.
  eapply Rle_trans; eauto.
Qed.

Global Instance policy_le_pre : PreOrder policy_le.
Proof.
  unfold policy_eq, policy_le.
  constructor; red; intros.
  - lra.
  - etransitivity; eauto. 
Qed.

Global Instance policy_le_part : PartialOrder policy_eq policy_le.
Proof.
  unfold policy_eq, policy_le.
  unfold PartialOrder, relation_equivalence, predicate_equivalence, relation_conjunction, Basics.flip, predicate_intersection; simpl.
  intuition.
Qed.


(* Optimal value of an MDP, given a list of policies
   (stationary policy determined by a decision rule)
   Denoted V*(s). We explicitly include the list of decision rules we take the 
   max over. 
 *)
Definition max_ltv : M.(state) -> R :=
  fun s => let (ld,_) := dec_rule_finite M in
        Max_{ld} (fun σ => ltv γ σ s).

(* The optimal value function satisfies the optimal Bellman equation. *)
Theorem max_ltv_eq_fixpt :
  forall init, fixpt (bellman_max_op γ) init = max_ltv.
Proof.
  intros init.
  apply functional_extensionality.
  intros s0. 
  apply Rle_antisym.
  - unfold max_ltv. destruct (dec_rule_finite M) as [ld Hld].
    apply Rmax_spec. rewrite in_map_iff.
    exists (greedy γ init).
    split. erewrite exists_fixpt_policy ; trivial.
    ++ apply Hld.
  - unfold max_ltv. destruct (dec_rule_finite M) as [ld Hld].
    rewrite Rmax_list_le_iff.
    ++ intros r Hr.
       rewrite in_map_iff in Hr. destruct Hr as [π [Hπ Hin]].
       rewrite <-Hπ. clear Hπ. revert s0. 
       change _ with (Rfct_le M.(state) (ltv γ π) (fixpt (bellman_max_op γ) init)).
       eapply ltv_Rfct_le_fixpt ; eauto.
    ++ rewrite map_not_nil. apply not_nil_exists.
       exists (nonempty_dec_rule M). 
       apply Hld.
Qed.  


Theorem bellman_iterate :
  forall init,
    lim (fun P => eventually (fun n : nat => P (@fixed_point.iter (CompleteNormedModule.UniformSpace R_AbsRing (@Rfct_CompleteNormedModule (state M) (fs M)))
 (bellman_max_op γ) n init))) = max_ltv.
Proof.
  intros init.
  assert (h1 : forall x : Rfct M.(state), (fun _ => True) x -> (fun _ => True) (bellman_max_op γ x)) by trivial. 
  assert (h2 : exists a : @Rfct M.(state) (fs M), (fun _ => True) a) by (split ; trivial).
  assert (h3 : my_complete (fun _ : @Rfct_CompleteNormedModule (state M) (fs M) => True)) by (apply closed_my_complete ; apply closed_true).
  destruct (FixedPoint _ (bellman_max_op γ) (fun _ => True) h1 h2 h3 (is_contraction_bellman_max_op γ hγ)) as [? [? [? [? Hsub]]]].
  specialize (Hsub init I).
  rewrite Hsub.
  assert (x = fixpt (bellman_max_op γ) init).
  eapply (fixpt_is_unique (is_contraction_bellman_max_op γ hγ) (fun _ => True)) ; eauto.
  apply closed_true.
  now rewrite <-(max_ltv_eq_fixpt init).
Qed.

End order.


Section improve.



Context {M : MDP} (γ : R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.



Context {D : R} (hγ : 0<=γ<1)
        (bdd : forall s s': M.(state), forall σ, Rabs (reward s (σ s) s') <= D).

Theorem policy_improvement_1 (σ τ : dec_rule M) :
  (forall s, bellman_op γ τ (ltv γ σ) s >= bellman_op γ σ (ltv γ σ) s)
  -> forall s, ltv γ τ s >= ltv γ σ s.
Proof.
  intros Hexpt. unfold bellman_op in Hexpt. unfold step_expt_reward in Hexpt.
  set (Hτ := ltv_bellman_op_fixpt γ D hγ bdd τ (ltv γ τ)).
  rewrite Hτ.
  apply contraction_coinduction_Rfct_ge.
  - apply is_contraction_bellman_op ; auto.
  - apply bellman_op_monotone_ge ; auto.
  - unfold Rfct_ge. intros s.
    replace (ltv γ σ s) with (bellman_op γ σ (ltv γ σ) s)
      by (now rewrite <-(ltv_bellman_eq_ltv γ D hγ bdd σ)).
    apply Hexpt.
Qed.

Theorem policy_improvement_2 (σ τ : dec_rule M) :
  (forall s, bellman_op γ τ (ltv γ σ) s <= bellman_op γ σ (ltv γ σ) s)
  -> forall s, ltv γ τ s <= ltv γ σ s.
Proof.
  intros Hexpt.
  set (Hτ := ltv_bellman_op_fixpt γ D hγ bdd τ (ltv γ τ)).
  rewrite Hτ.
  apply contraction_coinduction_Rfct_le.
  - apply is_contraction_bellman_op ; auto.
  - apply bellman_op_monotone_le ; auto.
  - unfold Rfct_le. intros s.
    replace (ltv γ σ s) with (bellman_op γ σ (ltv γ σ) s)
      by (now rewrite <-(ltv_bellman_eq_ltv γ D hγ bdd σ)).
    apply Hexpt.
Qed.

(* In this definition we explicitly list the action space. *)
(* π'(s) = argmax_{a ∈ A(s)} (Q^{π}(s,a)) *)
Definition improved (σ : dec_rule M) {la : forall s, list (act M s)} (hla : forall s, [] <> la s) : dec_rule M :=
  fun s => argmax (hla s) (fun a => expt_value (t s a) (fun s' => reward s a s' + γ*(ltv γ σ s'))). 


Lemma improved_is_better_aux (σ : dec_rule M) la (hla : forall s, [] <> la s) :
 forall s, bellman_op γ (improved σ hla) (ltv γ σ) s = Max_{ la s}(fun a : act M s => expt_value (t s a) (fun s' : state M => reward s a s' + γ * ltv γ σ s')).
Proof.
  intros s.
  unfold bellman_op.
  unfold step_expt_reward.
  rewrite <-expt_value_const_mul.
  rewrite <-expt_value_add.
  unfold improved.
  set (argmax_is_max (hla s)(fun a : act M s => expt_value (t s a) (fun s' : state M => reward s a s' + γ * ltv γ σ s'))). simpl in e. now rewrite e.
Qed.

Lemma improved_is_better (σ : dec_rule M) la (hla : forall s, [] <> la s)
      (H : forall σ : dec_rule M, forall s, In (σ s) (la s)):
  forall s, bellman_op γ (improved σ hla) (ltv γ σ) s >= bellman_op γ σ (ltv γ σ) s.
Proof.
  intros s.
  rewrite improved_is_better_aux.
  apply Rle_ge. unfold bellman_op.
  unfold step_expt_reward.
  rewrite <-expt_value_const_mul.
  rewrite <-expt_value_add.
  apply Rmax_spec.
  rewrite in_map_iff. exists (σ s).
  split ; trivial.
Qed.


Lemma improved_tot (σ : dec_rule M) : forall s, 
    bellman_op γ (improved σ (act_list_not_nil M)) (ltv γ σ) s >= bellman_op γ σ (ltv γ σ) s.
Proof.
  apply improved_is_better.
  unfold act_list. intros σ0 s.
  now destruct (M s).
Qed.

End improve.
