Require Import Reals Coquelicot.Coquelicot.
Require Import Omega.

Set Bullet Behavior "Strict Subproofs".
(*

****************************************************************************************
This file is an attempt to prove the Banach Fixed Point theorem. We state it in terms of 
Kozen's coinductive proof rule.

This file roughly follows the same proof attempt as in Boldo et al's work in the Elfic 
library where they proved the Lax-Milgram Theorem. 

****************************************************************************************

 *)

(** Contractive Mappings in Complete Metric Spaces. **)

(* Note:  `ball x eps y` states that y lies in a ball of center x and radius eps.*)


Section iter_props.
Context {V : CompleteSpace}.


Definition is_lipschitz (f : V -> V) (k : R) (P : V -> Prop):= k >= 0 /\ forall x y eps, eps > 0 -> P x -> P y -> ball x eps y -> ball (f x) (k*eps) (f y).


Definition is_contractive (f : V -> V) (P : V -> Prop) := exists k0 , k0 < 1 /\ is_lipschitz f k0 P.


Fixpoint iter_fun (n : nat) (f : V -> V) (v : V) :=
  match n with
  | 0 => v
  | S k => f (iter_fun k f v)
  end.



(* Helper lemmas. *)

Lemma Rpow_gt_0 (n0 : nat) {k : R} (hk : k > 0) : k^n0 > 0.
Proof.
  induction n0 as [| n0 iH0].
  simpl. exact Rlt_0_1.
  simpl. exact (Rmult_gt_0_compat _ _ hk iH0).
Qed.

Lemma k_le_one_ne_one {k : R} (Hk : 0 < k < 1) : k - 1 <> 0 .
Proof.
  destruct Hk as [Hk1 Hk2].
  intros notk. assert (k=1) by exact (Rminus_diag_uniq _ _ notk); clear notk.
  rewrite H in Hk2.
  exact (Rlt_irrefl _ Hk2).
Qed.


Lemma Rinv_nonneg {k : R} (Hk : 0<k<1): 0 <= /(1-k).
Proof.
  left. apply Rinv_0_lt_compat.
  apply Rlt_Rminus. firstorder.
Qed.

Lemma Rminus_pow_le_one {k : R} (m : nat) (Hk : 0 < k <1) : 1 - k^m <= 1.
Proof.
  left.
  apply Rminus_lt. ring_simplify.
  apply Ropp_lt_gt_0_contravar. apply Rpow_gt_0. firstorder.
Qed.

Variable f: V -> V.
Variable phi: V -> Prop.
Hypothesis phi_f: forall x:V, phi x -> phi (f x).


Definition lim : ((V -> Prop) -> Prop) -> V := CompleteSpace.lim _ (CompleteSpace.class V).


Definition is_complete (phi : V -> Prop) :=
  forall (F : (V -> Prop) -> Prop), ProperFilter F -> cauchy F
                       -> (forall P, F P -> (exists x, P x /\ phi x)) -> phi (lim F).


Lemma phi_iter_f (a : V) (n : nat) : phi a -> phi (iter_fun n f a).
Proof.
  intros Hphi.
  induction n as [| n0 iH0].
  now simpl.
  simpl. now apply phi_f.
Qed.

Lemma dist_iter_fun_aux_1 {k eps : R} (x : V) (hk : 0 < k < 1) (Hf : is_lipschitz f k phi)  : forall (n : nat) , (eps > 0) -> phi x -> 
      ball x eps (f x) -> ball (iter_fun n f x) ((k^n)*eps) (iter_fun (n+1) f x).
Proof.
  intros n Heps HP Hxfx.
  destruct Hf as [Hk Hp].
  case Hk. clear Hk. intro Hkk.
  induction n as [| n0 iH].
  *
    simpl. assert (1*eps = eps) by ring. now rewrite H.
  *
    simpl. 
    specialize (Hp (iter_fun n0 f x) (iter_fun (n0+1) f x) ((k^n0 * eps))).
    assert (k * k^n0 * eps = k*(k^n0 * eps)) by ring. rewrite H. apply Hp.
    apply (Rmult_gt_0_compat _ _). exact (Rpow_gt_0 _ Hkk).
    assumption. exact (phi_iter_f x n0 HP). exact  (phi_iter_f x (n0+1) HP).
    apply iH.
  * intro Keq. intuition. rewrite Keq in H. exfalso. exact (Rlt_irrefl _ H).
Qed.


(*Helper lemma for the inductive step in the next proof.*)
Lemma geom_sum {k : R} (hk : 0 < k < 1)(m0 n : nat) : let D :=  k ^ n * (k ^ S (S m0) - 1) / (k - 1)  in D = k^n * (k^ (S m0) - 1)/(k-1)  + k^(n+ S m0).
Proof.
  intros D. 
  assert (Kne1 : k - 1 <> 0) by exact (k_le_one_ne_one hk).
  field_simplify ; try assumption.
  rewrite pow_add,<- tech_pow_Rmult. unfold D ; field_simplify_eq ; try assumption.
  assert (k ^ S (S m0) = k^2 * k^m0) by (rewrite <-tech_pow_Rmult, <- tech_pow_Rmult ; ring).
  rewrite H ; ring.
Qed.


Lemma dist_iter_fun_aux_2 {k eps : R} (x : V) (hk : 0 < k < 1)(Hf : is_lipschitz f k phi) :
  forall (m  n : nat), (m > 0)%nat -> (eps > 0) -> phi x ->
                let D := k^n * (k^m - 1)/(k-1) in
                ball x eps (f x) -> ball (iter_fun n f x) (D*eps) (iter_fun (n+m) f x).
Proof.
  intros m n Hm0 eps0 Hphi D Hxfx.
  induction m as [ | m0 IHm0].
  *
    exfalso. omega.
  *
    destruct m0. replace D with (k^n).
    exact (dist_iter_fun_aux_1 x hk Hf _ eps0 Hphi Hxfx).
    unfold D. field_simplify. reflexivity.
    exact (k_le_one_ne_one hk).
    rewrite Nat.add_succ_r.
    assert (S m0 > 0)%nat by omega. unfold D ; rewrite (geom_sum hk m0 n). 
    rewrite (Rmult_plus_distr_r). eapply (ball_triangle _ (iter_fun (n+ S m0) f x) _ _ _).
    (* `intuition` here simplifies the context*)
    exact (IHm0 H). assert (Heq : (S (n + S m0))%nat = (n + S m0 + 1)%nat) by ring.
    rewrite Heq. exact (dist_iter_fun_aux_1 x hk Hf _ eps0 Hphi Hxfx).
Qed.


Lemma dist_iter_fun {k eps : R}(x : V)(m n : nat)(hk : 0 < k < 1)(Hf : is_lipschitz f k phi):
  eps > 0 -> phi x ->
  ball x eps (f x) -> let D:= k^n /(1-k) in ball (iter_fun n f x) (D*eps) (iter_fun (n+m) f x).
Proof.  
  intros Heps Hphi Hxfx D.
  case_eq m.
  *
    intro Heq. assert ((n+0 = n)%nat) by omega. rewrite H.
    enough (HDeps : D*eps > 0).
    apply (ball_center (iter_fun n f x) (mkposreal _ HDeps)).
    refine (Rmult_gt_0_compat _ _ _ Heps). unfold D.
    refine (Rdiv_lt_0_compat _ _ _ _). apply Rpow_gt_0 ; firstorder.
    apply Rlt_Rminus ; firstorder.
  *
    intros n0 Hn0.
    eapply ball_le.
    enough (k^n * (k^m - 1)/(k-1) * eps <= D*eps). apply H.
    unfold D. apply Rmult_le_compat_r ; try (left ; assumption).
    unfold Rdiv. rewrite Rmult_assoc. apply Rmult_le_compat_l.
    left. apply (Rpow_gt_0); firstorder.
    enough ((k ^ m - 1) * / (k - 1)  = (1 - k ^ m ) * / (1 - k)). rewrite H.
    rewrite <- Rmult_1_l.
    apply Rmult_le_compat_r.
    exact (Rinv_nonneg hk). exact (Rminus_pow_le_one m hk).
    field_simplify_eq. ring.
    split.
    assert (-(k-1) = 1 - k) by ring. rewrite <- H.
    exact (Ropp_neq_0_compat (k-1) (k_le_one_ne_one hk)).
    exact (k_le_one_ne_one hk).
    rewrite <- Hn0. refine (dist_iter_fun_aux_2 _ hk Hf _ _ _ Heps Hphi Hxfx). 
    rewrite Hn0. omega.
Qed.        

Lemma iter_is_proper (a : V) : ProperFilter (fun P => Hierarchy.eventually (fun n => P (iter_fun n f a))).
Proof.
  split. intros P He.
  destruct He as [x hb].
  exists (iter_fun x f a).
  apply hb. omega.
  split.
  *
    exists 1%nat. intros n Hn. trivial.
  *
    intros P Q (p,hp) (q,hq).
    exists (max p q). intros n Hmax.
    split.
    apply hp. etransitivity.
    assert ((p <= Init.Nat.max p q)%nat) by (apply Nat.le_max_l); apply H.
    assumption.
    apply hq. etransitivity.
    assert ((q <= Init.Nat.max p q)%nat) by (apply Nat.le_max_r); apply H.
    assumption.
  *
    intros P Q Hpq (nep,Hnep).
    exists nep. intros n Hn. intuition.
Qed.

(*Lemma iter_is_cauchy (a : V) :
 is_contractive f phi ->  phi a -> cauchy (fun P => Hierarchy.eventually (fun n => P(iter_fun n f a))).
Proof.
  intros Hf Hphi.
  generalize (@cauchy_distance V _ (iter_is_proper a)).
  unfold cauchy. intros (_,T). apply T. clear T.
 *)

End iter_props.

