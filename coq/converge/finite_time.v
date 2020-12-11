Require Import Reals Coq.Lists.List Coquelicot.Series Coquelicot.Hierarchy Coquelicot.SF_seq.
Require Import pmf_monad mdp Permutation fixed_point Finite LibUtils. 
Require Import Sums Coq.Reals.ROrderedType.
Require Import micromega.Lra.
Require Import micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Equivalence RelationClasses EquivDec Morphisms.
Require Import ExtLib.Structures.Monad.

Require Import ListAdd.

Set Bullet Behavior "Strict Subproofs".
(*
****************************************************************************************
In this file we only consider a finite list of policies.  
****************************************************************************************
*)

Import ListNotations.

Section all_lists.

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
Lemma all_lists_upto_fsts {A} (l:list A) n :
  equivlist (map fst (all_lists_upto l (S n))) l.
Proof.
  induction n; intros.
  - simpl.
    rewrite map_map; simpl.
    rewrite map_id.
    reflexivity.
  - simpl all_lists_upto.
    destruct l.
    + reflexivity.
    + apply list_prod_fst_equiv.
      intros eqq.
      apply map_nil' in eqq.
      destruct n.
      * simpl in eqq; congruence.
      * symmetry in eqq. revert eqq.
        apply list_prod_not_nil.
        -- congruence.
        -- intro eqq.
           symmetry in eqq.
           apply map_nil' in eqq.
           symmetry in eqq.
           revert eqq.
           apply all_lists_upto_non_nil.
           ++ congruence.
           ++ lia.
Qed.

Lemma all_lists_upto_snds {A} (l:list A) n :
  equivlist (map snd (all_lists_upto l (S (S n)))) (map (fun '(h,t) => (h::t)) (all_lists_upto l (S n))).
Proof.
  induction n; intros; simpl.
  - rewrite map_map.
    destruct l.
    + reflexivity.
    + rewrite list_prod_snd_equiv by congruence.
      reflexivity.
  - simpl in IHn.
    destruct l.
    + simpl; reflexivity.
    + rewrite list_prod_snd_equiv by congruence.
      rewrite list_prod_snd_equiv in IHn by congruence.
      apply map_equivlist_proper; [reflexivity | ].
      now apply list_prod_equivlist; [ reflexivity | ].
Qed.



End all_lists.

Section ltv_fin.
Open Scope R_scope. 
Context (M : MDP) (γ : R).
Context (hγ : (0 <= γ < 1)%R).

Arguments t {_}.
Arguments reward {_}.


Definition kliesli_iter_left (Π : list(dec_rule M)) (init : M.(state)) : Pmf M.(state):=
  fold_left (fun p π => Pmf_bind p (fun s => t s (π s))) Π (ret init).

Definition kliesli_iter_left_vector (init : Pmf M.(state)) (Π : list(dec_rule M))  : Pmf M.(state):=
  fold_left (fun p π => Pmf_bind p (fun s => t s (π s))) Π init.


Lemma ff_left {A B: Type} (f: A -> B -> A) (π0: B) (πs: list B) (s: A):  fold_left f πs (f s π0) = fold_left f (π0::πs) s.
Proof.
  simpl. reflexivity.
Qed.


Lemma kliesli_iter_left_cons0 π πs: forall p,
    kliesli_iter_left_vector  (Pmf_bind p (fun s0 => t s0 (π s0))) πs
    = kliesli_iter_left_vector p (π :: πs).
Proof.
  intros. 
  unfold kliesli_iter_left_vector. rewrite <- ff_left. reflexivity.
Qed.

Definition expt_reward_gen (p : Pmf M.(state)) (Π : list(dec_rule M))  (σ : dec_rule M)
  : R :=
  expt_value (kliesli_iter_left_vector p Π ) (step_expt_reward σ).


Definition ltv_fin (p: Pmf M.(state)) (Π : list(dec_rule M)) :=
    match Π with
    | nil => 0
    | π :: Π' => sum_f_R0' (fun n =>
                            match nth_error Π n with
                            | Some σ => γ^n*expt_reward_gen p (firstn n Π) σ
                            | None => 0
                            end) (length Π)
    end.

Lemma ltv_fin_cons_term1 p π:
  expt_reward_gen p [] π = expt_value p (fun s : state M => expt_value (t s (π s)) (reward s (π s))).
Proof.
  unfold expt_reward_gen.
  unfold kliesli_iter_left_vector.
  simpl. reflexivity.
Qed.


Lemma expt_reward_cons4 π πs σ vs:
  expt_reward_gen vs (π :: πs) σ =
  expt_reward_gen (Pmf_bind vs (fun s0 => t s0 (π s0))) πs σ.
Proof.
  unfold expt_reward_gen. rewrite kliesli_iter_left_cons0.
  reflexivity.
Qed.

Theorem ltv_fin_cons (π: dec_rule M) (πs: list(dec_rule M)) (p: Pmf M.(state)):
  ltv_fin p (π :: πs) = expt_value p (step_expt_reward π) +
                         γ*(ltv_fin (Pmf_bind (p) (fun s0 => (t s0 (π s0)))) πs).
Proof.
  intros.
  unfold step_expt_reward.
  unfold ltv_fin.
  assert (Hl: length (π :: πs) = S(length (πs))) by reflexivity.
  rewrite Hl.
  rewrite (sum_f_R0'_split _ _ 1) by lia.
  simpl.
  replace (0 + 1 * expt_reward_gen p [] π) with (expt_reward_gen p [] π) by lra.
  rewrite <- ltv_fin_cons_term1.
  apply Rplus_eq_compat_l.
  replace (length πs) with (length πs - 0)%nat by lia.  
  destruct πs.
  -  simpl. lra.
  -  rewrite <- sum_f_R0'_mult_const.
     apply sum_f_R0'_ext.
     intros.
     replace (x + 1)%nat with (S x) by lia.
     simpl.
     replace (length (d :: πs) - 0)%nat with (length (d :: πs)) in H by lia.
     apply nth_error_Some in H.
     match_destr; [| congruence].
     rewrite <- Rmult_assoc.
     f_equal.
Qed.

Corollary ltv_fin_pure (π: dec_rule M) (πs: list(dec_rule M)) s:
  ltv_fin (Pmf_pure s) (π :: πs) = expt_value (Pmf_pure s) (step_expt_reward π) +
                                  γ*(ltv_fin (t s (π s)) πs).
Proof.
  now rewrite ltv_fin_cons, Pmf_bind_of_ret.
Qed.

Lemma combine_map_fst_snd {A B} (l:list (A*B)) : combine (map fst l) (map snd l) = l.
Proof.
  induction l; simpl; trivial.
  destruct a; rewrite IHl; simpl; trivial.
Qed.

Theorem Rmax_list_prod_equivlist_split {A} (f:list A -> R) (l:list (A * list A)) :
  nil <> l ->
  equivlist (list_prod (map fst l) (map snd l)) l ->
  Max_{ l } (fun '(h,t) => f (h::t)) =
  Max_{ map fst l } (fun h => Max_{map snd l} (fun t => f (h::t)))  
.
Proof.
  intros.
  rewrite Rmax_list_prod_combine; trivial.
  - rewrite combine_map_fst_snd.
    f_equal.
    apply map_ext; simpl; intros [??]; trivial.
  - now apply map_not_nil.
  - now apply map_not_nil.
  - now rewrite combine_map_fst_snd.
Qed.
  
Theorem ltv_fin_28's (l:list (dec_rule M * list (dec_rule M))) s :
  nil <> l ->
  equivlist (list_prod (map fst l) (map snd l)) l ->
  Max_{ l } (fun '(h,t) => ltv_fin (Pmf_pure s) (h::t)) =
  Max_{ map fst l } (fun h => Max_{map snd l} (fun t => ltv_fin (Pmf_pure s) (h::t))).
Proof.
  apply Rmax_list_prod_equivlist_split.
Qed.

Theorem Rmax_list_dec_rule_split n p :
  (n > 0)%nat ->
  let l' := all_lists_upto (@elms _ (dec_rule_finite M)) n in
  Max_{ l' } (fun '(h,t) => ltv_fin p (h::t)) =
  Max_{ map fst l' } (fun h => Max_{map snd l'} (fun t => ltv_fin p (h::t)))  
.
Proof.
  intros.
  apply Rmax_list_prod_equivlist_split.
  - apply all_lists_upto_non_nil; trivial.
    destruct (dec_rule_finite M); simpl.
    generalize (nonempty_dec_rule M); intros e.
    destruct elms; [| congruence].
    elim (finite e).
  - apply all_lists_upto_prod.
Qed.

(* Optimal value function for a time n MDP. *)
Definition max_ltv_fin (n:nat) p :=
  let l' := all_lists_upto (@elms _ (dec_rule_finite M)) n in
  Max_{ l' } (fun '(h,t) => ltv_fin p (h::t)).

Theorem max_ltv_corec p n:
  max_ltv_fin (S (S n)) p =
  Max_{(@elms _ (dec_rule_finite M))}
      (fun h => expt_value p (step_expt_reward h) +
             γ * max_ltv_fin (S n) (Pmf_bind p (fun s0 => (t s0 (h s0))))).
Proof.
  unfold max_ltv_fin.
  intros.
  generalize (Rmax_list_dec_rule_split (S (S n)) p); intros HH.
  rewrite HH; [| lia].
  rewrite all_lists_upto_fsts.
  f_equal.
  apply map_ext; intros.
  rewrite all_lists_upto_snds.
  rewrite map_map.
  transitivity (
  (Max_{ all_lists_upto elms (S n)}
   (fun '(h, tl) => expt_value p (step_expt_reward a) +
                γ * ltv_fin (Pmf_bind p (fun s0 : state M => t s0 (a s0))) (h :: tl)))).
  - f_equal.
    apply map_ext; intros.
    destruct a0.
    apply ltv_fin_cons.
  - rewrite <- Rmax_list_map_const_mul by lra.
    rewrite Rplus_comm.
    generalize (Rmax_list_const_add
                  (@map (prod (dec_rule M) (list (dec_rule M))) R
                        (fun a0 : prod (dec_rule M) (list (dec_rule M)) =>
                           Rmult γ
                                 match a0 return R with
                                 | pair h tl =>
                                   ltv_fin (@Pmf_bind (state M) (state M) p (fun s0 : state M => @t M s0 (a s0)))
                                           (@cons (dec_rule M) h tl)
                                 end) (@all_lists_upto (dec_rule M) (@elms (dec_rule M) (dec_rule_finite M)) (S n)))
                  (expt_value p (step_expt_reward a))); intros HH2.

    case_eq ( map
            (fun a0 : dec_rule M * list (dec_rule M) =>
             γ * (let (h, tl) := a0 in ltv_fin (Pmf_bind p (fun s0 : state M => t s0 (a s0))) (h :: tl)))
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

End ltv_fin.
