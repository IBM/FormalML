Require Import Reals Coquelicot.Coquelicot.
Require Import Classical.
Require Import micromega.Lra.
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

Lemma Rinv_le_cancel: forall x y : R, 0 < y -> / y <= / x -> x <= y.
Proof.
intros x y H1 H2.
case (Req_dec x 0); intros Hx.
rewrite Hx; now left.
destruct H2.
left; now apply Rinv_lt_cancel.
right; rewrite <- Rinv_involutive.
2: now apply Rgt_not_eq.
rewrite H.
now apply sym_eq, Rinv_involutive.
Qed.

Theorem strong_induction:
 forall P : nat -> Prop,
    (forall n : nat, (forall k : nat, ((k < n)%nat -> P k)) -> P n) ->
       forall n : nat, P n.
Proof.
intros P H n.
assert (forall k, (k < S n)%nat -> P k).
induction n.
intros k Hk.
replace k with 0%nat.
apply H.
intros m Hm; contradict Hm.
apply lt_n_0.
generalize Hk; case k; trivial.
intros m Hm; contradict Hm.
apply le_not_lt.
now auto with arith.
intros k Hk.
apply H.
intros m Hm.
apply IHn.
apply lt_le_trans with (1:=Hm).
now apply gt_S_le.
apply H0.
apply le_n.
Qed.

Lemma Rle_pow_le: forall (x : R) (m n : nat), 0 < x <= 1 -> (m <= n)%nat -> x ^ n <= x ^ m.
Proof.
intros x m n (Hx1,Hx2) H.
apply Rinv_le_cancel.
now apply pow_lt.
rewrite 2!Rinv_pow; try now apply Rgt_not_eq.
apply Rle_pow; try assumption.
rewrite <- Rinv_1.
apply Rinv_le_contravar; try assumption.
Qed.

Lemma contraction_lt_any: forall k d, 0 <= k < 1 -> 0 < d -> exists N, pow k N < d.
Proof.
intros k d Hk Hd.
case (proj1 Hk); intros Hk'.
(* 0 < k *)
assert (ln k < 0).
rewrite <- ln_1.
apply ln_increasing; try apply Hk; assumption.
exists (Z.abs_nat (up (ln d / ln k))).
apply ln_lt_inv; try assumption.
now apply pow_lt.
rewrite <- Rpower_pow; trivial.
unfold Rpower.
rewrite ln_exp.
apply Rmult_lt_reg_l with (- /ln k).
apply Ropp_gt_lt_0_contravar.
now apply Rinv_lt_0_compat.
apply Rle_lt_trans with (-(INR (Z.abs_nat (up (ln d / ln k))))).
right; field.
now apply Rlt_not_eq.
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_lt_contravar.
generalize (archimed (ln d / ln k)); intros (Y1,_).
rewrite Rmult_comm.
apply Rlt_le_trans with (1:=Y1).
generalize (up (ln d / ln k)); clear; intros x.
rewrite INR_IZR_INZ, Zabs2Nat.id_abs.
apply IZR_le.
case (Zabs_spec x); intros (T1,T2); rewrite T2; auto with zarith.
(* k = 0 *)
exists 1%nat.
rewrite <- Hk';simpl.
now rewrite Rmult_0_l.
Qed.

Lemma contraction_lt_any': forall k d, 0 <= k < 1 -> 0 < d -> exists N, (0 < N)%nat /\ pow k N < d.
Proof.
intros k d H1 H2.
destruct (contraction_lt_any k d H1 H2) as (N,HN).
case_eq N.
intros H3; exists 1%nat; split.
now apply le_n.
rewrite H3 in HN; simpl in HN.
simpl; rewrite Rmult_1_r.
now apply Rlt_trans with 1.
intros m Hm.
exists N; split; try assumption.
rewrite Hm.
now auto with arith.
Qed.



  (* We can drop the phi_distanceable assumption for CompleteNormedModules. *)
Lemma phi_distancable_completemodule{ X: CompleteNormedModule R_AbsRing} (phi : X -> Prop) :
  forall x y : X, phi x -> phi y -> exists M, 0 <= M /\ ball x M y.
Proof.
  intros x y phix phiy; exists (norm (minus y x) + 1) ; split.
  apply Rplus_le_le_0_compat. apply norm_ge_0. apply Rle_0_1.
  apply (norm_compat1 x y).
  apply Rlt_plus_1.
Qed.


Variable f: V -> V.
Variable phi: V -> Prop.
Hypothesis phi_f: forall x:V, phi x -> phi (f x).
Hypothesis phi_distanceable:
   forall (x y:V), phi x -> phi y -> exists M, 0 <= M /\ ball x M y.



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


Definition lim : ((V -> Prop) -> Prop) -> V := CompleteSpace.lim _ (CompleteSpace.class V).


Definition is_complete (phi : V -> Prop) :=
  forall (F : (V -> Prop) -> Prop), ProperFilter F -> cauchy F
                       -> (forall P, F P -> (exists x, P x /\ phi x)) -> phi (lim F).


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

Lemma dist_iter_aux_zero_phi : forall (a:V) p m,
    phi a ->
    is_lipschitz f 0 phi ->
    (0 < p)%nat -> (0 < m)%nat ->
    ball (iter_fun p f a) 0 (iter_fun m f a).
Proof.
  
intros a p m phi_a (_,H) Hp Hm.
case_eq p.
intros V0; rewrite V0 in Hp; now contradict Hp.
intros n1 Hn1.
case_eq m.
intros V1; rewrite V1 in Hm; now contradict Hm.
intros n2 Hn2.
simpl.
destruct (phi_distanceable (iter_fun n1 f a) (iter_fun n2 f a)) as (M,(HM1,HM2)).
now apply phi_iter_f.
now apply phi_iter_f.
replace 0 with (0*(M+1)) by ring.
apply H; try assumption.
apply Rle_lt_trans with (M+0).
now rewrite Rplus_0_r.
apply Rplus_lt_compat_l, Rlt_0_1.
apply phi_iter_f.
trivial.
apply phi_iter_f.
trivial.
apply ball_le with M; try assumption.
apply Rle_trans with (M+0).
right; ring.
apply Rplus_le_compat_l, Rle_0_1.
Qed.


Lemma dist_iter_gen_phi : forall a k p m n D, 0 <= k < 1 -> is_lipschitz f k phi ->
   phi a ->
   0 < D -> ball a D (f a) -> (n <= p)%nat -> (n <= m)%nat -> (0 < n)%nat ->
    ball (iter_fun p f a) (k^n/(1-k) *D) (iter_fun m f a).
Proof.
  intros a k p m n D (H1,H1') H2 Phi_a H3 H4 Hp Hm Hn.
case H1; intros P0.
(* *)
case (le_or_lt p m); intros H5.
(* . *)
replace m with (p+(m-p))%nat.
apply ball_le with (k^p/(1-k) *D).
apply Rmult_le_compat_r.
now left.
unfold Rdiv; apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat.
now apply Rlt_Rminus.
apply Rle_pow_le; try assumption.
split; try left; try assumption.
refine (dist_iter_fun _ _ _ _ H2 H3 Phi_a H4).
split; assumption. 
now apply le_plus_minus_r.
(* . *)
apply ball_sym.
replace p with (m+(p-m))%nat.
apply ball_le with (k^m/(1-k) *D).
apply Rmult_le_compat_r.
now left.
unfold Rdiv; apply Rmult_le_compat_r.
left; apply Rinv_0_lt_compat.
now apply Rlt_Rminus.
apply Rle_pow_le; try assumption.
split; try left; assumption.
refine (dist_iter_fun _ _ _ _ H2 H3 Phi_a H4).
split; assumption.
now apply le_plus_minus_r, lt_le_weak.
(* *)
apply ball_le with 0.
rewrite <- P0.
rewrite pow_i; try assumption.
right; unfold Rdiv; ring.
apply dist_iter_aux_zero_phi; try assumption.
now rewrite P0.
now apply lt_le_trans with n.
now apply lt_le_trans with n.
Qed.



Definition is_eq : V -> V -> Prop := fun a b => forall eps:posreal, ball a eps b.

Lemma is_eq_trans: forall x y z, is_eq x y -> is_eq y z -> is_eq x z.
Proof.
intros x y z H1 H2 eps.
pose (e':=mkposreal _ (is_pos_div_2 eps)).
replace (pos eps) with (pos e'+pos e').
apply ball_triangle with y.
apply H1.
apply H2.
simpl; field.
Qed.

Lemma is_eq_sym: forall x y, is_eq x y -> is_eq y x.
Proof.
intros x y H eps.
apply ball_sym.
now apply H.
Qed.

Lemma iter_is_cauchy (a : V) :
 is_contractive f phi ->  phi a -> cauchy (fun P => Hierarchy.eventually (fun n => P(iter_fun n f a))).
Proof.
intros (k,(Hk1,(Hf1,Hf2))) Phi_a.
generalize (@cauchy_distance V _ (iter_is_proper a)).
unfold cauchy; intros (_,T); apply T; clear T.
intros eps. unfold Hierarchy.eventually.
destruct (phi_distanceable a (f a)) as (M,(HM1,HM2)).
assumption.
now apply phi_f.
destruct HM1.
(* 0 < M *)
destruct (contraction_lt_any' k (eps/M*(1-k)*/3)) as (n,(Hn',Hn)).
firstorder.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply Rdiv_lt_0_compat; trivial.
destruct eps; now simpl.
now apply Rlt_Rminus.
apply Rinv_0_lt_compat.
apply Rplus_lt_0_compat; try apply Rlt_0_1; apply Rlt_0_2.
exists (fun x => exists m:nat, (n <= m)%nat /\ (iter_fun m f a = x)).
split.
(* . *)
exists n.
intros l Hl.
exists l; split; try easy.
(* . *)
intros u v (n1,(Hn1,Hu)) (n2,(Hn2,Hv)).
assert (L:(0 < eps/3)).
apply Rdiv_lt_0_compat.
destruct eps; now simpl.
apply Rplus_lt_0_compat; try apply Rlt_0_1; apply Rlt_0_2.
pose (e:=mkposreal _ L).
replace (pos eps) with (pos e+(pos e+pos e))%R by (simpl;field).
apply ball_triangle with (iter_fun n1 f a).
rewrite Hu. apply ball_center.
apply ball_triangle with (iter_fun n2 f a).
apply ball_sym. 
apply ball_le with (k ^ n / (1 - k) * M).
unfold e; simpl.
apply Rmult_le_reg_l with (/M).
now apply Rinv_0_lt_compat.
apply Rmult_le_reg_l with (1-k).
now apply Rlt_Rminus.
apply Rle_trans with (eps / M * (1 - k) * / 3).
2: right; unfold Rdiv; ring.
left; apply Rle_lt_trans with (2:=Hn).
right; field.
split; apply Rgt_not_eq; try assumption.
now apply Rlt_Rminus.
apply dist_iter_gen_phi.
split. now apply Rge_le. assumption.
now split. assumption. assumption. assumption. assumption. assumption. assumption.
rewrite Hv. apply ball_center.
(* M = 0 *)
rewrite <- H in HM2.
assert (forall n, is_eq (iter_fun n f a) a).
apply strong_induction with (P:= fun n => is_eq (iter_fun n f a) a).
intros n; case n.
simpl; intros _.
intros e; apply ball_center.
clear n; intros n; case n.
intros _; simpl.
intros e; apply ball_sym, ball_le with 0; try assumption.
destruct e; left; now simpl.
clear n; intros n IH.
apply is_eq_trans with (iter_fun (S n) f a).
2: apply IH.
2: apply le_n.
simpl; intros e.
apply ball_le with (k*e).
rewrite <- (Rmult_1_l e) at 2.
apply Rmult_le_compat_r.
destruct e; left; now simpl.
now left.
apply Hf2.
apply cond_pos. change (phi (iter_fun (S n) f a)).
apply (phi_iter_f _ _ Phi_a). now apply phi_iter_f.
assert (L:(is_eq (iter_fun (S n) f a) (iter_fun n f a))).
apply is_eq_trans with a.
apply IH.
apply le_n.
apply is_eq_sym.
apply IH.
apply le_S, le_n.
apply L.
exists (fun x => is_eq x a).
split.
exists 0%nat.
intros n _; apply H0.
intros u v Hu Hv.
assert (is_eq u v).
apply is_eq_trans with a; try assumption.
now apply is_eq_sym.
apply H1.
Qed.

Definition my_complete (phi:V->Prop) := (forall (F:(V -> Prop) -> Prop),
    ProperFilter F -> cauchy F ->
   (forall P, F P -> (exists x, P x /\ phi x)) -> phi (lim F)).

Lemma FixedPoint_aux1_phi : forall (a:V), my_complete phi -> is_contractive f phi -> phi a ->
  let  x := lim  (fun P => Hierarchy.eventually (fun n => P (iter_fun n f a))) in
      is_eq (f x) x.
Proof.
intros a phi_c Hf Phi_a x.
generalize (complete_cauchy
   (fun P => Hierarchy.eventually (fun n => P (iter_fun n f a)))
    (iter_is_proper a)
    (iter_is_cauchy _ Hf Phi_a)).
replace ((Hierarchy.lim
         (fun P : V -> Prop => Hierarchy.eventually (fun n0 : nat => P (iter_fun n0 f a))))) with x by reflexivity.
intros H eps.
pose (e2 :=mkposreal _ (is_pos_div_2 eps)).
specialize (H e2).
destruct H as (n,Hn).
replace (pos eps) with (pos e2 + pos e2).
2: simpl; field.
apply ball_sym.
apply ball_triangle with (iter_fun (S n) f a).
apply Hn.
apply le_S, le_n.
generalize Hf; intro Hf'.
destruct Hf as (k,(Hk1,(Hk2,Hk3))).
apply ball_le with (k*e2).
rewrite <- (Rmult_1_l e2) at 2.
apply Rmult_le_compat_r.
destruct e2; left; now simpl.
now left.
simpl.
apply Hk3.
apply (cond_pos e2).
now apply phi_iter_f. 
unfold x.
unfold my_complete in phi_c.
apply phi_c.
apply iter_is_proper.
apply iter_is_cauchy.
trivial.
trivial.
intros P Hev.
unfold eventually in Hev.
destruct Hev as (N,Hev).
specialize (Hev (N+1)%nat).
assert (Hev' : P (iter_fun (N+1) f a)).
apply Hev.
intuition.
exists (iter_fun (N+1) f a).
split; try assumption.
apply phi_iter_f.
trivial.
trivial.
apply ball_sym.
apply Hn.
apply le_n.
Qed.

Hypothesis phi_X_not_empty: exists (a:V), phi a.
Hypothesis phi_closed: my_complete phi.

Lemma FixedPoint_aux2_phi : forall (a:V), is_contractive f phi -> phi a ->
  let  x := lim
  (fun P => Hierarchy.eventually (fun n => P (iter_fun n f a))) in
      phi x.
Proof.
intros a Hf Phi_a x.
apply phi_closed.
apply iter_is_proper.
now apply iter_is_cauchy.
intros P (N,HN).
exists (iter_fun N f a).
split.
apply HN.
apply le_n.
now apply phi_iter_f.
Qed.

Search ( _ < _).
Lemma FixedPoint_uniqueness_weak_phi : forall a b, is_contractive f phi
      -> phi a -> phi b
      -> is_eq (f a) a -> is_eq (f b) b ->
        is_eq a b.
Proof.
intros a b (k,(Hk1,(Hk2,Hf))) Phi_a Phi_b Ha Hb eps.
destruct (phi_distanceable a b) as (M,(HM1,HM2)); try assumption.
destruct HM1.
(* *)
pose (k' := (k + 1)/2).
assert (k < k').
unfold k'; apply Rmult_lt_reg_l with 2%R.
apply Rlt_0_2.
apply Rplus_lt_reg_l with (-k).
replace (-k+2*k) with k by ring.
replace (-k + 2 * ((k + 1) / 2)) with 1 by field.
assumption.
assert (0 < k' < 1).
split.
apply Rle_lt_trans with k. apply Rge_le. assumption.
unfold k'; apply Rmult_lt_reg_l with 2%R.
apply Rlt_0_2.
apply Rplus_lt_reg_l with (-1).
replace (-1+2*1) with 1 by ring.
replace (-1 + 2 * ((k + 1) / 2)) with k by field. lra.
unfold k'. apply Rmult_lt_reg_l with 2%R. apply Rlt_0_2.
apply Rplus_lt_reg_l with (-1).
replace (-1+2*1) with 1 by ring.
replace (-1 + 2 * ((k + 1) / 2)) with k by field. lra.
(* *)
destruct (contraction_lt_any k' (eps/M)) as (N,HN).
now (split; try left).
apply Rdiv_lt_0_compat; trivial.
destruct eps; simpl; easy.
apply ball_le with (M*k'^N).
apply Rmult_le_reg_r with (/M).
now apply Rinv_0_lt_compat.
left; apply Rle_lt_trans with (2:=HN).
right; field.
now apply Rgt_not_eq.
(* *)
clear HN; induction N.
simpl; rewrite Rmult_1_r.
assumption.
assert (L:(0 < M*k'^S N*(k'-k)/2)).
apply Rdiv_lt_0_compat; try apply Rlt_0_2.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat; try assumption.
now apply pow_lt.
now apply Rlt_Rminus.
specialize (Ha (mkposreal _ L)).
specialize (Hb (mkposreal _ L)).
apply ball_le with ((M * k' ^ (S N) * (k' - k) / 2) + ((k*(M * k' ^ N)) + (M * k' ^ (S N) * (k' - k) / 2))).
simpl.
apply Rle_trans with ((k'*(k' - k)  + k)*M*k'^N).
right; field.
apply Rle_trans with (k'*M*k'^N).
2: right; ring.
apply Rmult_le_compat_r.
left; now apply pow_lt.
apply Rmult_le_compat_r.
now left.
apply Rplus_le_reg_l with (-k'*(k'-k)-k).
apply Rle_trans with 0.
right; ring.
apply Rle_trans with (Rsqr ((k-1)/2)).
apply Rle_0_sqr.
right; unfold Rsqr, k'.
field.
apply ball_triangle with (f a).
apply ball_sym, Ha.
apply ball_triangle with (f b).
apply Hf; try assumption.
apply Rmult_lt_0_compat; try assumption.
now apply pow_lt.
apply Hb.
(* *)
apply ball_le with M; try assumption.
rewrite <- H; destruct eps; simpl; left; easy.
Qed.


Theorem FixedPoint_C_phi : is_contractive f phi ->
   exists a:V,
     phi a
      /\ is_eq (f a) a
      /\ (forall b, phi b -> is_eq (f b) b -> is_eq b a) /\
    forall x, phi x -> is_eq (lim  (fun P => Hierarchy.eventually (fun n => P (iter_fun n f x)))) a.
Proof.
intros Hf.
destruct phi_X_not_empty as (a, Ha).
exists (lim (fun P => Hierarchy.eventually (fun n => P (iter_fun n f a)))).
split.
now apply FixedPoint_aux2_phi.
split.
now apply FixedPoint_aux1_phi.
split.
intros b Phi_b Hb.
apply FixedPoint_uniqueness_weak_phi; try assumption.
now apply FixedPoint_aux2_phi.
now apply FixedPoint_aux1_phi.
intros x Phi_x.
apply FixedPoint_uniqueness_weak_phi; try assumption.
now apply FixedPoint_aux2_phi.
now apply FixedPoint_aux2_phi.
now apply FixedPoint_aux1_phi.
now apply FixedPoint_aux1_phi.
Qed.

End iter_props.

