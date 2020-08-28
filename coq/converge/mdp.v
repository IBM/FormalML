Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy Coquelicot.SF_seq.
Require Import pmf_monad Permutation fixed_point continuous_linear_map.
Require Import Sums Coq.Reals.ROrderedType.
Require Import micromega.Lra.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Equivalence RelationClasses EquivDec Morphisms.
Require Import ExtLib.Structures.Monad LibUtils.
Require Import Streams StreamAdd. 


Import MonadNotation.
Import ListNotations. 
Set Bullet Behavior "Strict Subproofs".


(*
****************************************************************************************
This file defines Markov Decision Processes (MDP) and proves various properties about 
them. Included are definitions of long-term values (LTVs), proofs that LTVs are convergent
and proofs that they satisfy the Bellman equation. 
We also include definitions of V* and Q* and proofs about them. The goal is to prove 
policy and value iteration algorithms correct. 
****************************************************************************************
*)
Import ListNotations. 

Section extra.
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

Class NonEmpty (A : Type) :=
  ex : A.
    
Class Finite (A:Type) :=
 { elms  : list A ;
  finite : forall x:A, In x elms
 }.

Global Declare Scope rmax_scope. 

Section Rmax_list.
  
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


Fixpoint Rmax_list' (l : list R) : R :=
  match l with
    | nil => 0
    | a :: l1 =>
      match l1 with
        | nil => a
        | a' :: l2 => Rmax a (Rmax_list' l1)
      end
  end.

Lemma Rmax_list_Rmax_list' (l : list R) :
  Rmax_list l = Rmax_list' l.
Proof.
  induction l. 
  - simpl ; trivial.
  - simpl. rewrite IHl.
    trivial. 
Qed.

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

Lemma Rmax_list_const_mul (l : list R) {r : R} (hr : 0 <= r) :
  Rmax_list (List.map (fun x => r*x) l) = r*(Rmax_list l).
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

Notation "Max_{ l } ( f )" := (Rmax_list (List.map f l)) (at level 50).

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

Definition Rmax_list_map {A} (l : list A) (f : A -> R) := Rmax_list (List.map f l).  

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
      (f : A -> R) (g : A -> R)
      (hla : [] <> la)  :
      (forall a, f a <= g a) ->
      Max_{la} (fun a => f a) <= Max_{la} (fun a => g a).
Proof.
  intros Hfg.
  destruct (Rmax_list_map_exist (fun a => g a) la hla) as [a1 [Ha1 Hina1]].
  destruct (Rmax_list_map_exist (fun a => f a) la hla) as [a2 [Ha2 Hina2]].
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


Definition bind_iter {M:Type->Type} {Mm:Monad M} {A:Type} (unit:A) (f : A -> M A) :=
  applyn (ret unit) (fun y => Monad.bind y f).

Notation "Max_{ l } ( f )" := (Rmax_list (List.map f l)) (at level 50).

Section MDPs.

Open Scope monad_scope.
Open Scope R_scope.
Open Scope rmax_scope. 
Record MDP := mkMDP {
 (* State and action spaces. *)
 state : Type;
 act  : forall s: state, Type;
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
  applyn (ret init) (fun y => Pmf_bind y (fun s => t s (σ s))) n.

Definition bind_stoch_iter_str (π : Stream(dec_rule M)) (n : nat) (init : M.(state)) 
  : Pmf M.(state):=
  applyn (ret init) (fun y => Pmf_bind y (fun s => t s (Str_nth n π s))) n.

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
  unfold bind_iter. 
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

Section egs.

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

End egs.

Section ltv.

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

Definition ltv : M.(state) -> R := fun s => Series (fun n => γ^n * (expt_reward σ s n)).
  
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


(* Long-Term Values satisfy the Bellman equation. *)
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


Section ltv_gen.


Open Scope R_scope. 
Context {M : MDP} (γ : R).
Context (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Lemma const_stream_eq {A} (a : A) : forall n : nat, a = Str_nth n (const a).
Proof.
  unfold Str_nth ; induction n ; trivial.
Qed.

Lemma str_nth_cons_zero {A} (a : A) (π : Stream A) : Str_nth 0 (Cons a π) = a.
Proof.
  now unfold Str_nth ; simpl. 
Qed.


Lemma str_nth_cons_one {A} (a : A) (π : Stream A) : Str_nth 1 (Cons a π) = hd π.
Proof.
  now unfold Str_nth ; simpl. 
Qed.

Definition ltv_gen (π : Stream (dec_rule M)) : M.(state) -> R :=
  fun s => Series (fun n => γ^n * expt_value (bind_stoch_iter_str π n s)
                                       (fun s => step_expt_reward (hd π) s)).

(* Fix this proof to remove funext axiom. *)
Theorem ltv_gen_ltv : forall s : M.(state), forall σ : dec_rule M, ltv γ σ s = ltv_gen (const σ) s.
Proof. 
  intros s σ.
  apply Series_ext. unfold bind_stoch_iter_str. simpl.
  intro n. f_equal. unfold expt_reward.
  assert (forall n, forall s,  t s (Str_nth n (const σ) s)  = t s (σ s)).
  intros n0 s0. f_equal. now erewrite <-const_stream_eq. 
  f_equal. unfold bind_stoch_iter. simpl. f_equal. apply functional_extensionality.
  intro x. f_equal. apply functional_extensionality. intros x0 ; eauto.
Qed.

Lemma Str_nth_succ_cons {A} (n : nat) (d : A) (π : Stream A) :
  Str_nth (S n) (Cons d π) = Str_nth n π.
Proof.
  induction n.
  - unfold Str_nth. simpl. reflexivity.
  - unfold Str_nth. simpl. reflexivity.
Qed.

Lemma Str_nth_hd_tl {A} (n : nat) (π : Stream A) :
  Str_nth (S n) π = Str_nth n (tl π).
Proof.
  induction n ; unfold Str_nth ; trivial. 
Qed.

Lemma Pmf_bind_comm_stoch_bind_str (n : nat) (π : Stream (dec_rule M)) (init : state M):
  Pmf_bind (bind_stoch_iter_str π n init) (fun a : state M => t a (Str_nth n π a)) =
  Pmf_bind (t init (Str_nth n π init)) (fun a : state M => bind_stoch_iter_str π n a).
Proof.
  revert π. 
  induction n. 
  * unfold bind_stoch_iter_str. simpl. intros π. rewrite Pmf_bind_of_ret.
    now rewrite Pmf_ret_of_bind.
  * unfold bind_stoch_iter_str in *. simpl. intro π. rewrite Str_nth_hd_tl. 
    setoid_rewrite (IHn (tl π)).
    now rewrite Pmf_bind_of_bind.
Qed.


Definition expt_ltv_gen (π : Stream (dec_rule M)) (p : Pmf M.(state)) : R :=
  expt_value p (ltv_gen π).

(* Expected reward at time 0 is equal to the reward for a nonstationary policy. *)

Lemma expt_reward0_eq_reward_gen (π : Stream(dec_rule M)) : forall init : M.(state), expt_reward (hd π) init 0 = (step_expt_reward (hd π) init).
Proof.
  intros init.
  unfold expt_reward. unfold bind_stoch_iter. simpl.
  now rewrite expt_value_pure.
Qed.


Lemma expt_reward_gen_succ (n : nat) (π : Stream (dec_rule M)) (init: state M) :
  expt_reward (Str_nth (S n) π) init (S n) = expt_value (t init (Str_nth n (tl π) init)) (fun s => expt_reward (Str_nth n (tl π)) s n).
Proof.
  rewrite expt_reward_succ.
  rewrite <-expt_value_bind. rewrite Pmf_bind_comm_stoch_bind. 
  rewrite Str_nth_hd_tl.
  rewrite expt_value_bind.
  unfold expt_reward. reflexivity.
Qed.

        
 (*Long-Term Values satisfy the Bellman equation.
Lemma ltv_gen_corec {D : R} (π : Stream (dec_rule M)) :
  (forall s s': M.(state), forall σ, Rabs (reward s (σ s) s') <= D) ->
  forall init : M.(state), 
  ltv_gen π init = (step_expt_reward (hd π) init) + γ*expt_value (t init (hd π init)) (ltv_gen (tl π)). 
Proof.
  intros bdd init. 
  rewrite <-(@expt_reward0_eq_reward). 
  unfold ltv_gen. 
  rewrite Series_incr_1. simpl. rewrite Rmult_1_l. setoid_rewrite Rmult_assoc.   
  rewrite Series_scal_l. f_equal. f_equal.
  rewrite expt_value_Series.
  apply Series_ext. intros n. rewrite expt_value_const_mul. f_equal.
  simpl.
  rewrite <-expt_value_bind. unfold bind_stoch_iter_str.
  rewrite Str_nth_hd_tl. setoid_rewrite  Pmf_bind_comm_stoch_bind_str.
  rewrite expt_value_bind. rewrite expt_value_bind.
  
Qed.*)


End ltv_gen.


Section order.
  
Open Scope R_scope. 
Context {M : MDP} (γ : R).
Context (hγ : (0 <= γ < 1)%R).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

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

Notation "Max_{ l } ( f )" := (Rmax_list (List.map f l)) (at level 50).

(* Optimal value of an MDP, given a list of policies
   (stationary policy determined by a decision rule)
   Denoted V*(s). We explicitly include the list of decision rules we take the 
   max over. 
*)
Definition max_ltv_on (l : list (dec_rule M)) : M.(state) -> R :=
  fun s => Max_{l} (fun σ => ltv γ σ s).

(* Proceed with the assumption that rewards are bounded for any policy and 
   that the set of actions is finite. *)
Context {D : R}.
Context (fina : forall s : M.(state), Finite (M.(act) s)). 
Context (bdd :  (forall s s': M.(state), forall σ : dec_rule M, Rabs (reward s (σ s) s') <= D)).

Lemma max_ltv_aux1 (l : list (dec_rule M)): 
  forall s : M.(state),
    max_ltv_on l s =
    Max_{l} (fun σ => (step_expt_reward σ s) + γ*expt_value (t s (σ s)) (ltv γ σ)).
Proof.
  intros s. unfold step_expt_reward. 
  unfold max_ltv_on.
  f_equal. apply List.map_ext.
  intros π.
  eapply ltv_corec ; eauto.
Qed.


Lemma max_ltv_aux2 (l : list (dec_rule M)): 
  forall s : M.(state),
    max_ltv_on l s =
    Max_{List.map (fun σ => (σ s,σ)) l} (fun σ => (step_expt_reward (snd σ) s) + γ*expt_value (t s (fst σ)) (ltv γ (snd σ))).
Proof.
  intro s.
  rewrite max_ltv_aux1.  
  apply Rmax_list_map_transf.
  rewrite Forall_forall.
  intros x Hx. simpl. reflexivity. 
Qed.

Lemma Rmax_list_split {A B} (f : A*B -> R) (l : list (A*B)) (eqA : EqDec A eq) :
  Max_{l}(f) = Max_{List.map fst l} (fun a:A => Max_{List.map snd (filter (fun pi' => a ==b fst pi') l)} (fun pi' => f (a,pi'))).
Proof.
  rewrite map_map.
  apply Rle_antisym.
  - rewrite Rmax_list_le_iff.
    intros x H.
    rewrite in_map_iff in H.
    destruct H as [ab [Hab Hinab]]. 
Admitted.

Lemma max_ltv_aux3 (l : list (dec_rule M)) (eqA : forall s : M.(state), EqDec (act M s) eq): 
  forall s : M.(state),
    Max_{List.map (fun σ => (σ s,σ)) l} (fun σ => (step_expt_reward (snd σ) s) + γ*expt_value (t s (fst σ)) (ltv γ (snd σ))) =  Max_{ List.map (fun σ => (σ s, σ)) l}
  (fun x =>Max_{List.map snd (filter (fun pi' => fst x ==b fst pi')(List.map (fun σ => (σ s, σ)) l))} (fun pi' => step_expt_reward pi' s + γ * expt_value (t s (fst x)) (ltv γ pi'))).
Proof.
  intro s. erewrite Rmax_list_split. simpl. rewrite map_map. simpl.
  reflexivity.
Qed.


(* TODO(Kody): 
   Get rid of the `In foo bar` hypotheses by adding in the Finite typeclass. *)

(* V*(s) <= max_{a ∈ A} (r(x,a) + Σ_{y ∈ S} p(y | x,a) V*(y) *)
Lemma bellman_opt_1 {la : forall s: state M, list(act M s)} {ld : list(dec_rule M)} {ls : list (state M)}
      (hla : forall s, [] <> la s) (hld : [] <> ld)
       (hp : forall π s, In π ld -> In s ls -> In (π s) (la s)):
  forall s : M.(state), In s ls ->
    max_ltv_on ld s <= Max_{la s}(fun a => expt_value (t s a) (reward s a) + γ * expt_value (t s a) (max_ltv_on ld)). 
Proof.
  intros s hs. unfold step_expt_reward.
  destruct (Rmax_list_map_exist (fun σ => ltv γ σ s) ld hld) as [π' [Hπ' Hinπ']].
  destruct (Rmax_list_map_exist (fun a => expt_value (t s a) (reward s a) + γ * expt_value (t s a) (max_ltv_on ld)) (la s) (hla s)) as [a' [Ha' Hina']].
  unfold max_ltv_on.
  rewrite <-Hinπ'.  
  erewrite ltv_corec ; eauto. unfold step_expt_reward.
  assert(
      γ*expt_value(t s (π' s)) (ltv γ π') <= γ*expt_value(t s (π' s)) (max_ltv_on ld)
    ).
  {
    apply Rmult_le_compat_l ; intuition.
    apply expt_value_le. intros s0. 
    unfold max_ltv_on. apply Rmax_spec.
    rewrite in_map_iff. exists π' ; split ; trivial.
  }
  eapply Rle_trans.
  -- apply Rplus_le_compat_l ; eauto.
  -- apply Rmax_spec.
     rewrite in_map_iff. exists (π' s). split ; trivial.
  apply hp ; trivial.
Qed.        

Lemma Rle_lt : forall r1 r2 : R, not (r1 >= r2) <-> r2 > r1.
Proof.
  split.
  - apply Rnot_ge_gt.
  - intros H1 H2. apply (Rgt_irrefl r2).
    eapply Rgt_ge_trans ; eauto.
Qed.


Lemma bell_opt_aux {A} {B : forall a : A, Type} {la : forall a : A, list (B a)}
      {lf : list (forall a:A, B a)} (hlf : [] <> lf)
      (hla : forall a, [] <> la a)
      (hp : forall π s, In π lf -> In (π s) (la s))
      (* For every state and every action available at that state, there is atleast one
         decision rule mapping the state to that action. *)
      (surj : forall (a : A) (b : B a), exists f, In f lf /\ f a = b)
      r : forall a : A, 
    Max_{lf}(fun σ => r a (σ a)) = Max_{la a}(fun b => r a b).
Proof.
  intros a. 
  apply Rle_antisym.
  - apply Rmax_spec.
    rewrite in_map_iff.
    destruct (Rmax_list_map_exist (fun σ : forall x0 : A, B x0 => r a (σ a)) (lf)) as [ex Hex].
    assumption.
    exists (ex a). intuition.
  - rewrite Rmax_list_le_iff.
    intros x Hx.
    rewrite in_map_iff in Hx.
    destruct Hx as [b [Hb Hinb]].
    rewrite <-Hb.
    apply Rmax_spec. rewrite in_map_iff.  
    specialize (surj a b). destruct surj as [f [Hfin Hfab]]. 
    exists f. rewrite Hfab. split ; trivial.
    rewrite map_not_nil. apply hla. 
Qed.

Lemma bell_opt_aux' {A} {B : forall a : A, Type} {la : forall a : A, list (B a)}
      (eqA : forall a : A, EqDec (B a) eq)
      {lf : list (forall a:A, B a)} (hlf : [] <> lf)
      (hla : forall a, [] <> la a)
      (hp : forall π s, In π lf -> In (π s) (la s))
      (* For every state and every action available at that state, there is atleast one
         decision rule mapping the state to that action. *)
      (surj : forall (a : A) (b : B a), exists f, In f lf /\ f a = b)
      r : forall a : A, 
    Max_{lf}(fun σ => r a (σ a) σ) = Max_{la a}(fun b => Max_{filter (fun σ => σ a ==b b) lf}(fun σ => r a b σ)).
Proof.
  intros a. 
  apply Rle_antisym.
  - apply Rmax_spec.
    rewrite in_map_iff.
    destruct (Rmax_list_map_exist (fun σ : forall x0 : A, B x0 => r a (σ a) σ) (lf)) as [ex Hex].
    assumption.
    exists (ex a). intuition.
    rewrite <-H2. 
Admitted.

(* This is killing me. *)
Lemma bellman_optimality {la : forall s: state M, list(act M s)} {ld : list(dec_rule M)} {ls : list (state M)} (hla : forall s, [] <> la s) (hld : [] <> ld)
      (hp : forall π s, In π ld -> In (π s) (la s))
  (Hsurj :(forall (a : state M) (b : act M a), exists f : forall a0 : state M, act M a0, In f ld /\ f a = b)): forall s : M.(state), In s ls -> max_ltv_on ld s = Max_{la s}(fun a => expt_value (t s a) (reward s a) + γ * expt_value (t s a) (max_ltv_on ld)).
Proof.
  intros s0 Hs0. rewrite max_ltv_aux1. unfold step_expt_reward.
  unfold dec_rule. unfold step_expt_reward. 
Admitted.

End order.


Section operator.
Open Scope R_scope. 
Context {M : MDP} (γ D : R).
Context (hγ : (0 <= γ < 1)%R).

Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Context (bdd :  (forall s s': M.(state), forall σ : dec_rule M, Rabs (reward s (σ s) s') <= D)).


Definition bellman_op (π : dec_rule M) : (M.(state) -> R) -> (M.(state) -> R) :=
  fun W => fun s => (step_expt_reward π s + γ*(expt_value (t s (π s)) W)). 

Lemma ltv_bellman_op_fixpoint : forall π, bellman_op π (ltv γ π) = ltv γ π.
Proof.
  intro π.
  unfold bellman_op. simpl.
  apply functional_extensionality.
  intro init. symmetry.
  eapply ltv_corec ; eauto.
Qed.

Lemma bellman_op_monotone (π : dec_rule M) W1 W2: (forall s, W1 s <= W2 s) -> (forall s, bellman_op π W1 s <= bellman_op π W2 s). 
Proof.
  intros HW1W2 s.
  unfold bellman_op. 
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l ; intuition.
  apply expt_value_le ; eauto.
Qed.


Definition bellman_max_op (π : dec_rule M) (la : forall s, list (M.(act) s)) : (M.(state) -> R) -> (M.(state) -> R) :=
  fun W => fun s => Max_{la s}( fun a => expt_value (t s a) (reward s a) + γ*(expt_value (t s a) W)). 



Lemma bellman_max_op_monotone (π : dec_rule M) {la : forall s, list (M.(act) s)} (hla : forall s, [] <> la s) W1 W2: (forall s, W1 s <= W2 s) -> (forall s, bellman_max_op π la W1 s <= bellman_max_op π la W2 s). 
Proof.
  intros HW1W2 s.
  unfold bellman_max_op.
  apply Rmax_list_fun_le ; auto. 
  intro a.
  apply Rplus_le_compat_l.
  apply Rmult_le_compat_l ; intuition.
  apply expt_value_le ; eauto.
Qed.

End operator.



Section Rfct_AbelianGroup.

 
Definition Rfct {A : Type} (fin : Finite A) := A -> R.

Context {A : Type} (finA : Finite A). 
                                
Definition Rfct_zero : Rfct finA := fun x => 0. 

Definition Rfct_plus (f : Rfct finA) (g : Rfct finA) := fun x => (f x) + (g x).  

Definition Rfct_opp (f : Rfct finA) := fun x => opp (f x).

Definition Rfct_scal (r : R) (f : Rfct finA) := fun x => scal r (f x).

Lemma Rfct_eq_ext: forall (f g:Rfct finA), (forall x, f x = g x) -> f = g.
Proof.
  intros f g. apply functional_extensionality.
Qed.

Lemma Rfct_plus_comm: forall (f g:Rfct finA), Rfct_plus f g = Rfct_plus g f.
Proof.
  intros f g.
  apply Rfct_eq_ext. intros x.
  unfold Rfct_plus. lra.
Qed.

Lemma Rfct_plus_assoc:
  forall (x y z:Rfct finA), Rfct_plus x (Rfct_plus y z) = Rfct_plus (Rfct_plus x y) z.
Proof.
  intros f g h.
  apply Rfct_eq_ext.
  intro x. unfold Rfct_plus.
  lra.
Qed.

Lemma Rfct_plus_zero_r: forall x:Rfct finA, Rfct_plus x Rfct_zero = x.
Proof.
  intro x ; unfold Rfct.
  apply Rfct_eq_ext ; intros.
  unfold Rfct_plus.
  unfold Rfct_zero. lra.
Qed.

Lemma Rfct_plus_opp_r: forall x:Rfct finA, Rfct_plus x (Rfct_opp x) = Rfct_zero.
Proof.
  intro f ; unfold Rfct.
  apply Rfct_eq_ext ; intros.
  unfold Rfct_plus.
  unfold Rfct_opp. unfold Rfct_zero.
  apply (plus_opp_r (f x)).
Qed.


Definition Rfct_AbelianGroup_mixin :=
  AbelianGroup.Mixin (Rfct finA) Rfct_plus Rfct_opp Rfct_zero Rfct_plus_comm
   Rfct_plus_assoc Rfct_plus_zero_r Rfct_plus_opp_r.

Canonical Rfct_AbelianGroup :=
  AbelianGroup.Pack (Rfct finA) (Rfct_AbelianGroup_mixin) (Rfct finA).

End Rfct_AbelianGroup.

Section Rfct_ModuleSpace.

Context {A : Type} (finA : Finite A).
  
Lemma Rfct_scal_assoc: forall (x y : R) (u: Rfct finA),
   Rfct_scal finA x (Rfct_scal finA y u) = Rfct_scal finA (x*y) u.
Proof.
  intros x y f.
  unfold Rfct_scal.
  eapply Rfct_eq_ext.
  intro x0. unfold scal ; simpl. now rewrite Rmult_assoc.
Qed.

Lemma Rfct_scal_one: forall (u:Rfct finA), Rfct_scal finA R1 u = u.
Proof.
  intros f.
  unfold Rfct_scal.
  eapply Rfct_eq_ext.
  intro x0. unfold scal ; simpl. apply Rmult_1_l.
Qed.

Lemma Rfct_scal_distr_l: forall x (u v:Rfct finA), Rfct_scal finA x (Rfct_plus finA u v)
        = Rfct_plus finA (Rfct_scal finA x u) (Rfct_scal finA x v).
Proof.
  intros x f g.
  unfold Rfct_scal.
  eapply Rfct_eq_ext.
  intro x0. unfold Rfct_plus.
  apply Rmult_plus_distr_l.
Qed.

Lemma Rfct_scal_distr_r: forall (x y:R) (u:Rfct finA), Rfct_scal finA (Rplus x y) u
         = Rfct_plus finA (Rfct_scal finA x u) (Rfct_scal finA y u).
Proof.
  intros x f g.
  unfold Rfct_scal.
  eapply Rfct_eq_ext.
  intro x0. unfold Rfct_plus.
  apply Rmult_plus_distr_r.
Qed.

Definition Rfct_ModuleSpace_mixin :=
  ModuleSpace.Mixin R_Ring (Rfct_AbelianGroup finA) (Rfct_scal finA) Rfct_scal_assoc
     Rfct_scal_one Rfct_scal_distr_l Rfct_scal_distr_r.

Canonical Rfct_ModuleSpace :=
  ModuleSpace.Pack R_Ring (Rfct finA)
   (ModuleSpace.Class R_Ring (Rfct finA) _ Rfct_ModuleSpace_mixin) (Rfct finA).

End Rfct_ModuleSpace.

Section Rfct_UniformSpace.
 
(* 
   Definition of a Uniformspace structure on functionals f : A -> R where 
   the ecart is defined as Max_{ls}(fun s => f s) where ls is a list of 
   elements of A.
*)
  
Context {A : Type} (finA : Finite A).

Definition Rmax_norm := let (ls,_) := finA in fun (f:Rfct finA) => Max_{ls}(fun s => Rabs (f s)).

Definition Rmax_ball :=  fun (f: Rfct finA) eps g => Rmax_norm (fun s => minus (g s) (f s)) < eps.


Lemma Rmax_ball_compat (f g : Rfct finA) (eps : posreal) :
  ball f eps g -> Rmax_ball f eps g.
Proof.
  intros Hball. unfold Rmax_ball. unfold Rmax_norm.
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
Qed.

Lemma Rmax_ball_le (f g : Rfct finA) {eps1 eps2 : R} :
  eps1 <= eps2 -> Rmax_ball f eps1 g -> Rmax_ball f eps2 g.
Proof. 
  intros Heps Hball.
  unfold Rmax_ball in *. 
  eapply Rlt_le_trans ; eauto.
Qed.

Lemma Rmax_ball_center : forall (f : Rfct finA) (e : posreal), Rmax_ball f e f.
Proof.
  intros f e. 
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

Lemma Rmax_ball_sym : forall (f g : Rfct finA) (e : R), Rmax_ball f e g -> Rmax_ball g e f.
Proof.
  intros f g e H.
  unfold Rmax_ball in *. unfold Rmax_norm in *.
  destruct finA as [ls Hls]. 
  enough (Max_{ls}(fun s => Rabs (minus (f s) (g s))) = Max_{ls}(fun s => Rabs(minus (g s) (f s)))). 
  now rewrite H0.
  f_equal. apply List.map_ext_in.
  intros a H0.
  now rewrite Rabs_minus_sym.
Qed.


Lemma Rmax_ball_triangle : forall (f g h : Rfct finA) (e1 e2 : R),
    Rmax_ball f e1 g -> Rmax_ball g e2 h -> Rmax_ball f (e1 + e2) h.
Proof.
  intros f g h e1 e2 H1 H2.
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
  UniformSpace.Mixin (Rfct finA) Rmax_ball Rmax_ball_center Rmax_ball_sym Rmax_ball_triangle.

(* 
   There seems to be a problem defining a `Canonical` version of this, 
   since it is picking up the Uniformspace 
   structure inherited from R. Maybe this isn't even necessary...?
*)
Definition Rfct_UniformSpace : UniformSpace :=
  UniformSpace.Pack (Rfct finA) Rfct_UniformSpace_mixin (Rfct finA).


End Rfct_UniformSpace.


Section Rfct_NormedModule.

Context (A : Type) (finA : Finite A).

Canonical Rfct_NormedModuleAux :=
  NormedModuleAux.Pack R_AbsRing (Rfct finA)
   (NormedModuleAux.Class R_AbsRing (Rfct finA)
     (ModuleSpace.class _ (Rfct_ModuleSpace finA))
        (Rfct_UniformSpace_mixin finA)) (Rfct finA).

Lemma Rfct_norm_triangle: 
      forall f g, (Rmax_norm finA (Rfct_plus finA f g)) <= (Rmax_norm finA f) + (Rmax_norm finA g).
Proof.
  intros f g.
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

Lemma Rfct_norm_ball2: forall (f g : Rfct finA) (eps : posreal),
          Hierarchy.ball f eps g -> Rmax_norm finA (minus g f) < 1 * eps.
Proof.
  intros f g eps Hball.
    unfold Rmax_ball. unfold Rmax_norm.
    destruct finA as [ls Hls]. 
    destruct (is_nil_dec ls).
     - subst ; simpl. rewrite Rmult_1_l. apply cond_pos. 
     - rewrite Rmax_list_lt_iff.
       intros x Hx.
       rewrite in_map_iff in Hx.
       destruct Hx as [a [Ha Hina]].
       specialize (Hball a). rewrite <-Ha. rewrite Rmult_1_l.
       apply Hball.  
       rewrite map_not_nil. now rewrite ne_symm.
Qed.


Lemma Rfct_norm_scal_aux:
  forall (l : R) (f : Rfct finA), Rmax_norm finA (scal l f) <= Rabs l * Rmax_norm finA f .
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
    
  
Lemma Rfct_norm_eq_0: forall (f:Rfct finA), real (Rmax_norm finA f) = 0 -> f = zero.
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

Print close. 

Lemma Rfct_norm_ball1 : forall (f g : Rfct finA) (eps : R),
     Rmax_norm finA (minus g f) < eps -> Hierarchy.ball f eps g.
Proof.
  intros f g eps H.
  unfold ball ; simpl. unfold fct_ball.
  unfold Rmax_norm in H. 
Admitted. 


Definition Rfct_NormedModule_mixin :=
  NormedModule.Mixin R_AbsRing Rfct_NormedModuleAux (Rmax_norm finA) 1%R Rfct_norm_triangle Rfct_norm_scal_aux Rfct_norm_ball1 Rfct_norm_ball2 _.

(* Rfct_norm_triangle Rfct_norm_scal_aux Rfct_norm_ball1 Rfct_norm_ball2 Rfct_norm_eq_0 *)
Canonical Rfct_NormedModule :=
  NormedModule.Pack R_AbsRing Rfct
     (NormedModule.Class _ _ _ Rfct_NormedModule_mixin) Rfct.
*)

End Rfct_NormedModule.

Section Rfct_CompleteSpace.

  Context {A : Type} (ls : list A).

  Lemma close_lim_Rfct :
    forall F1 F2, filter_le F1 F2 -> filter_le F2 F1 -> @close (Rfct_UniformSpace ls) (lim_fct F1) (lim_fct F2).
  Proof.
    intros F1 F2 H H0. unfold close. intros eps.
    apply Rmax_ball_compat.
    apply (close_lim_fct F1 F2 H H0 eps).
  Qed.

  Lemma complete_cauchy_Rfct : forall F : (Rfct_UniformSpace ls -> Prop) -> Prop,
      ProperFilter F ->
      (forall (eps : posreal), exists f, F (Rmax_ball ls f eps))
      -> forall eps : posreal, F (Rmax_ball ls (lim_fct F) eps).
  Proof.
    intros F ProperF CauchyF eps.
    assert ((eps/3) > 0) by (apply Rmult_gt_0_compat ; [apply cond_pos | lra]).
    destruct (CauchyF (mkposreal (eps/3) H)) as [f Hf]. simpl in *.
    eapply filter_imp ; last apply Hf.
    intros g Hg.  
    apply Rmax_ball_le with (eps/3+eps/3+eps/3). right ; lra.
    eapply Rmax_ball_triangle ; [ |apply Hg].
  Admitted.
  
  Definition Rfct_CompleteSpace_mixin :=
  CompleteSpace.Mixin (Rfct_UniformSpace ls) lim_fct complete_cauchy_Rfct close_lim_Rfct.

  Canonical Rfct_CompleteSpace :=
  CompleteSpace.Pack (Rfct finA) (CompleteSpace.Class _ _ Rfct_CompleteSpace_mixin) (Rfct finA).

End Rfct_CompleteSpace.

Section coinduction. 

Open Scope R_scope. 
Context {M : MDP} (ls : list (state M)).
Arguments reward {_}.
Arguments outcomes {_}.
Arguments t {_}.

Variable (f : Rfct M.(state) -> Rfct M.(state)).
Variable (ϕ : Rfct M.(state) -> Prop).
Check @FixedPoint_C _ f ϕ. (* Works! If we remove the above canonical instance, it falls back on fct_CompleteSpace. *)

Lemma phi_distanceable (ϕ : Rfct M.(state) -> Prop) :
  forall x y : Rfct M.(state), ϕ x -> ϕ y -> exists M0 : R, 0 <= M0 /\ Rmax_ball ls x M0 y. 
Proof.
Admitted. 

Check @FixedPoint_C. 
Theorem metric_coinduction_Rfct 
  {f : Rfct M.(state) -> Rfct M.(state)}
    (ϕ : Rfct M.(state) -> Prop) (phic : closed ϕ) (phin : exists a , ϕ a)
    (hf : is_contraction f)
    (phip : forall x, ϕ x -> ϕ (f x)):
  exists a', f a' = a' /\ ϕ a'.
Proof.
  assert (my_complete ϕ) by (now apply closed_my_complete).                       
  destruct (FixedPoint_C f ϕ phip phin H hf) as [a [Hphi [Hfix Hsub]]].
  exists a. split ; trivial.
Qed.

 
End coinduction. 
