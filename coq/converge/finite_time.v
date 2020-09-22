Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy Coquelicot.SF_seq.
Require Import pmf_monad mdp Permutation fixed_point Finite LibUtils. 
Require Import Sums Coq.Reals.ROrderedType.
Require Import micromega.Lra.
Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Equivalence RelationClasses EquivDec Morphisms.
Require Import ExtLib.Structures.Monad.

(*
****************************************************************************************
In this file we only consider a finite list of policies.  
****************************************************************************************
*)

Import ListNotations.


Section ltv_fin.
Open Scope R_scope. 
Context (M : MDP) (γ : R).
Context (hγ : (0 <= γ < 1)%R).

Arguments t {_}.
Arguments reward {_}.

Check step_expt_reward.

Definition kliesli_iter_left (Π : list(dec_rule M)) (init : M.(state)) : Pmf M.(state):=
  fold_left (fun p π => Pmf_bind p (fun s => t s (π s))) Π (ret init).

Definition kliesli_iter_left_vector (init : Pmf M.(state)) (Π : list(dec_rule M))  : Pmf M.(state):=
  fold_left (fun p π => Pmf_bind p (fun s => t s (π s))) Π init.


Lemma ff_left {A B: Type} (f: A -> B -> A) (π0: B) (πs: list B) (s: A):  fold_left f πs (f s π0) = fold_left f (π0::πs) s.
Proof.
  simpl. reflexivity.
Qed.


Lemma kliesli_iter_left_cons0 π πs: forall sv,
    kliesli_iter_left_vector  (Pmf_bind sv (fun s0 => t s0 (π s0))) πs
    = kliesli_iter_left_vector sv (π :: πs).
Proof.
  intros. 
  unfold kliesli_iter_left_vector. rewrite <- ff_left. reflexivity.
Qed.

Lemma Pmf_unity {A} (p: Pmf A): Pmf_bind p (fun s0: A => Pmf_pure s0) = p.
Proof.
  rewrite Pmf_ret_of_bind.
  reflexivity.
Qed.

Definition expt_reward_vector (sv : Pmf M.(state)) (Π : list(dec_rule M))  (σ : dec_rule M)
  : R :=
  expt_value (kliesli_iter_left_vector sv Π ) (step_expt_reward σ).


Definition ltv_gen (sv: Pmf M.(state)) (Π : list(dec_rule M)) :=
    match Π with
    | nil => 0
    | π :: Π' => sum_f_R0' (fun n =>
                            match nth_error Π n with
                            | Some σ => γ^n*expt_reward_vector sv (firstn n Π) σ
                            | None => 0
                            end) (length Π)
    end.

Lemma ltv_gen_cons_term1 sv π: expt_reward_vector sv [] π = expt_value sv (fun s : state M => expt_value (t s (π s)) (reward s (π s))).
Proof.
  unfold expt_reward_vector.
  unfold kliesli_iter_left_vector.
  unfold fold_left.
  unfold step_expt_reward.
  reflexivity.
Qed.


Lemma expt_reward_cons4 π πs σ vs:
  expt_reward_vector vs (π :: πs) σ =
  expt_reward_vector (Pmf_bind vs (fun s0 => t s0 (π s0))) πs σ.
Proof.
  unfold expt_reward_vector. rewrite kliesli_iter_left_cons0.
  reflexivity.
Qed.

Theorem ltv_gen_cons (π: dec_rule M) (πs: list(dec_rule M)) (sv: Pmf M.(state)):
  ltv_gen sv (π :: πs) = expt_value sv (step_expt_reward π) +
                         γ*(ltv_gen (Pmf_bind (sv) (fun s0 => (t s0 (π s0)))) πs).
Proof.
  intros.
  unfold step_expt_reward.
  unfold ltv_gen.
  assert (Hl: length (π :: πs) = S(length (πs))) by reflexivity.
  
  rewrite Hl.
  rewrite (sum_f_R0'_split _ _ 1) by lia.
  simpl.
  assert (HH: 0 + 1 * expt_reward_vector sv [] π =  expt_reward_vector sv [] π).
  { rewrite Rplus_comm.
    rewrite Rplus_0_r.
    rewrite Rmult_comm.
    rewrite Rmult_1_r.
    reflexivity.
  }
  rewrite HH.
  rewrite <- ltv_gen_cons_term1.
  apply Rplus_eq_compat_l.
  assert (HH1: (length πs = length πs - 0)%nat) by lia.
  rewrite <- HH1.
  
  destruct πs.
  -  simpl. ring_simplify. reflexivity.
  -  rewrite <- sum_f_R0'_mult_const.
     apply sum_f_R0'_ext.
     intros.
     replace (x + 1)%nat with (S x) by lia.
     simpl.
     apply nth_error_Some in H.
     match_destr; [| congruence].

     rewrite <- Rmult_assoc.
     f_equal.

Qed.

Corollary ltv_gen_pure (π: dec_rule M) (πs: list(dec_rule M)) s:
  ltv_gen (Pmf_pure s) (π :: πs) = expt_value (Pmf_pure s) (step_expt_reward π) +
                                  γ*(ltv_gen (t s (π s)) πs).
Proof.
  now rewrite ltv_gen_cons, Pmf_bind_of_ret.
Qed.

Lemma Rmax_list_prod {A B} (f : A -> B -> R) {la : list A} {lb : list B}
      (Hla : [] <> la) (Hlb : [] <> lb) :
  equivlist (list_prod la lb) (combine la lb) ->
  Max_{la}(fun a => Max_{lb} (fun b => f a b))  =
  Max_{combine la lb} (fun ab => f (fst ab) (snd ab)).
Proof.
  intros. rewrite <- H.
  now apply Rmax_list_prod_le.
Qed.

Lemma combine_map_fst_snd {A B} (l:list (A*B)) : combine (map fst l) (map snd l) = l.
Proof.
  induction l; simpl; trivial.
  destruct a; rewrite IHl; simpl; trivial.
Qed.

Set Bullet Behavior "Strict Subproofs".

Theorem ltv_gen_28's_aux {A} (f:list A -> R) (l:list (A * list A)) :
  nil <> l ->
  equivlist (list_prod (map fst l) (map snd l)) l ->
  Max_{ l } (fun '(h,t) => f (h::t)) =
  Max_{ map fst l } (fun h => Max_{map snd l} (fun t => f (h::t)))  
.
Proof.
  intros.
  rewrite Rmax_list_prod; trivial.
  - rewrite combine_map_fst_snd.
    f_equal.
    apply map_ext; simpl; intros [??]; trivial.
  - now apply map_not_nil.
  - now apply map_not_nil.
  - now rewrite combine_map_fst_snd.
Qed.
  
Theorem ltv_gen_28's (l:list (dec_rule M * list (dec_rule M))) s :
  nil <> l ->
  equivlist (list_prod (map fst l) (map snd l)) l ->
  Max_{ l } (fun '(h,t) => ltv_gen (Pmf_pure s) (h::t)) =
  Max_{ map fst l } (fun h => Max_{map snd l} (fun t => ltv_gen (Pmf_pure s) (h::t))).
Proof.
  apply ltv_gen_28's_aux.
Qed.

Fixpoint all_lists_upto {A} (l:list A) (n:nat) : list (A * list A)
  := match n with
     | 0 => nil
     | 1 => map (fun x => (x,nil)) l
     | S m => (list_prod l (map (fun '(a,b) => a::b) (all_lists_upto l m)))
     end.

Lemma all_lists_upto_non_nil {A} (l:list A) n : nil <> l -> (n > 0)%nat -> nil <> all_lists_upto l n.
Proof.
  intros.
  induction n; simpl.
  - lia.
  - case_eq n; intros.
    + destruct l; simpl; congruence.
    + apply list_prod_not_nil; trivial.
      subst.
      destruct (all_lists_upto l (S n0)); simpl.
      * elim IHn; trivial.
        lia.
      * destruct p; simpl.
        congruence.
Qed.

Global Instance list_prod_equivlist {A B} :
  Proper (equivlist ==> equivlist ==> equivlist) (@list_prod A B).
Proof.
  cut (Proper (equivlist ==> equivlist ==> @incl _) (@list_prod A B))
  ; unfold Proper, respectful; intros.
  - apply equivlist_incls.
    split; apply H; trivial.
    + now symmetry.
    + now symmetry.
  - intros [a b] inn.
    apply in_prod_iff in inn.
    apply in_prod_iff.
    now rewrite <- H, <- H0.
Qed.

Lemma all_lists_upto_total {A} (l:list A) n :
  forall a' l', incl (a'::l') l -> length (a'::l') = n ->
           In (a',l') (all_lists_upto l n).
Proof.
  induction n; simpl; intros.
  - lia.
  - invcs H0.
    destruct l'; simpl; intros.
    + red in H.
      apply in_map_iff.
      eexists; split; [reflexivity | ].
      simpl in *.
      eauto.
    + apply in_prod_iff.
      split.
      * specialize (H a').
        simpl in H; eauto.
      * simpl in IHn.
        apply in_map_iff.
        exists (a,l').
        split; trivial.
        apply IHn; trivial.
        unfold incl in *; simpl in *.
        eauto.
Qed.

Lemma all_lists_upto_in {A} (l:list A) n x :
  In x (all_lists_upto l n) -> In (fst x) l /\ incl (snd x) l.
Proof.
  revert x.
  induction n; simpl; intros.
  - intuition.
  - destruct n.
    + apply in_map_iff in H.
      destruct H as [? [??]]; subst; simpl.
      split; trivial.
      intros ?; simpl; intuition.
    + destruct x; simpl.
      apply in_prod_iff in H.
      destruct H as [? inn].
      split; trivial.
      apply in_map_iff in inn.
      destruct inn as [[??] [? inn]]; subst.
      destruct (IHn _ inn).
      simpl in *.
      intros ?; simpl; intros inn2.
      destruct inn2; [congruence|].
      now specialize (H1 _ H2).
Qed.

Lemma all_lists_length {A} (l:list A) n x:
  In x (all_lists_upto l n) -> length (fst x :: snd x) = n.
Proof.
  revert x.
  induction n; simpl; intros [??] inn.
  - intuition.
  - f_equal.
    destruct n.
    + apply in_map_iff in inn.
      destruct inn as [? [??]]; subst; simpl; trivial.
      invcs H; simpl; trivial.
    + simpl.
      apply in_prod_iff in inn.
      destruct inn as [inn1 inn2].
      apply in_map_iff in inn2.
      destruct inn2 as [[??] [? inn2]].
      subst.
      specialize (IHn _ inn2).
      now simpl in *.
Qed.

Lemma all_lists_upto_prod {A} (l:list A) n :
  let l' := all_lists_upto l n in
  equivlist (list_prod (map fst l') (map snd l')) l'.
Proof.
  simpl.
  apply equivlist_incls.
  split; intros [??] inn.
  - apply in_prod_iff in inn.
    destruct inn as [inn1 inn2].
    apply in_map_iff in inn1.
    apply in_map_iff in inn2.
    destruct inn1 as [? [??]].
    destruct inn2 as [? [??]].
    subst.
    generalize (all_lists_length l n x0 H2); simpl; intros HH.
    apply all_lists_upto_in in H0.
    apply all_lists_upto_in in H2.
    apply all_lists_upto_total; simpl; trivial.
    apply incl_cons; intuition.
  - apply in_prod_iff.
    split.
    + apply in_map_iff.
      exists (a,l0); simpl; intuition.
    + apply in_map_iff.
      exists (a,l0); simpl; intuition.
Qed.      

Theorem ltv_gen_29s n p :
  (n > 0)%nat ->
  let l' := all_lists_upto (@elms _ (dec_rule_finite M)) n in
  Max_{ l' } (fun '(h,t) => ltv_gen p (h::t)) =
  Max_{ map fst l' } (fun h => Max_{map snd l'} (fun t => ltv_gen p (h::t)))  
.
Proof.
  intros.
  apply ltv_gen_28's_aux.
  - apply all_lists_upto_non_nil; trivial.
    destruct (dec_rule_finite M); simpl.
    generalize (nonempty_dec_rule M); intros e.
    destruct elms; [| congruence].
    elim (finite e).
  - apply all_lists_upto_prod.
Qed.

Lemma all_lists_upto_fsts {A} (l:list A) n :
  equivlist (map fst (all_lists_upto l (S n))) l.
Proof.
  simpl.
  induction n; simpl; intros.
  - rewrite map_map; simpl.
    rewrite map_id.
    reflexivity.
Admitted.

Lemma all_lists_upto_snds {A} (l:list A) n :
  equivlist (map snd (all_lists_upto l (S n))) (map (fun '(h,t) => (h::t)) (all_lists_upto l n)).
Proof.
Admitted.

Definition optimal_value_function (n:nat) p :=
  let l' := all_lists_upto (@elms _ (dec_rule_finite M)) n in
  Max_{ l' } (fun '(h,t) => ltv_gen p (h::t)).

Lemma ltv_gen_30s n p :
  optimal_value_function (S (S n)) p =
  Max_{(@elms _ (dec_rule_finite M))}
      (fun h => expt_value p (step_expt_reward h) + γ * optimal_value_function (S n) (Pmf_bind p (fun s0 => (t s0 (h s0))))).
Proof.
  unfold optimal_value_function.
  intros.
  generalize (ltv_gen_29s (S (S n)) p); intros HH.
  rewrite HH; [| lia].
  rewrite all_lists_upto_fsts.
  f_equal.
  apply map_ext; intros.
  rewrite all_lists_upto_snds.
  rewrite map_map.
  transitivity (
  (Max_{ all_lists_upto elms (S n)}
   (fun '(h, tl) => expt_value p (step_expt_reward a) +
                γ * ltv_gen (Pmf_bind p (fun s0 : state M => t s0 (a s0))) (h :: tl)))).
  - f_equal.
    apply map_ext; intros.
    destruct a0.
    apply ltv_gen_cons.
  - rewrite <- Rmax_list_map_const_mul by lra.
    rewrite Rplus_comm.
    generalize (Rmax_list_const_add
                  (@map (prod (dec_rule M) (list (dec_rule M))) R
                        (fun a0 : prod (dec_rule M) (list (dec_rule M)) =>
                           Rmult γ
                                 match a0 return R with
                                 | pair h tl =>
                                   ltv_gen (@Pmf_bind (state M) (state M) p (fun s0 : state M => @t M s0 (a s0)))
                                           (@cons (dec_rule M) h tl)
                                 end) (@all_lists_upto (dec_rule M) (@elms (dec_rule M) (dec_rule_finite M)) (S n)))
                  (expt_value p (step_expt_reward a))); intros HH2.

    case_eq ( map
            (fun a0 : dec_rule M * list (dec_rule M) =>
             γ * (let (h, tl) := a0 in ltv_gen (Pmf_bind p (fun s0 : state M => t s0 (a s0))) (h :: tl)))
            (all_lists_upto elms (S n))); intros.
    + generalize (all_lists_upto_non_nil (@elms _ (dec_rule_finite M)) (S n)); intros HH3.
      destruct ((all_lists_upto (@elms _ (dec_rule_finite M)) (S n))).
      * elim HH3; trivial.
        destruct (dec_rule_finite M); simpl.
        generalize (nonempty_dec_rule M); intros e.
        destruct elms; [| congruence].
        elim (finite e).
        lia.
      * simpl in H; congruence.
    + rewrite H in HH2.
      destruct (r :: l <> []); [| congruence].
      rewrite <- HH2.
      rewrite <- H.
      clear H HH2 c.
      rewrite map_map.
      f_equal.
      apply map_ext; intros [??].
      lra.
Qed.      
