(**
This file is part of the Elfic library

Copyright (C) Boldo, Clément, Faissole, Martin, Mayero

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Coquelicot.Rcomplements Coquelicot.Rbar Coquelicot.Markov Coquelicot.Iter Coquelicot.Lub Coquelicot.Hierarchy.
Require Import continuous_linear_map.

(** Complete Dependant uniform spaces *)

Module CompleteSpaceD.

Record mixin_of (T : UniformSpace) := Mixin {
  lim : forall (F:(T->Prop)->Prop) (H1:ProperFilter F) (H2:cauchy F), T ;
  ax1 : forall F (H1:ProperFilter F) (H2:cauchy F), forall eps : posreal,
        F (ball (lim F H1 H2) eps)
}.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : UniformSpace.class_of T ;
  mixin : mixin_of (UniformSpace.Pack _ base T)
}.
Local Coercion base : class_of >-> UniformSpace.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition UniformSpace := UniformSpace.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> UniformSpace.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Notation CompleteSpaceD := type.

End Exports.

End CompleteSpaceD.

Export CompleteSpaceD.Exports.

Section CompleteSpace1.

Context {T : CompleteSpaceD}.

Definition lim (F:(T->Prop)->Prop) (H1:ProperFilter F) (H2:cauchy F): T
  := CompleteSpaceD.lim _ (CompleteSpaceD.class T) F H1 H2.

Lemma complete_cauchyD :
  forall (F : (T -> Prop) -> Prop)
  (H1:ProperFilter F) (H2:cauchy F),
  forall eps : posreal,
  F (ball (lim F H1 H2) eps).
Proof.
apply CompleteSpaceD.ax1.
Qed.

(** Dependant iota *)

Lemma iotaD'_correct_weak_aux1: forall (P : T -> Prop) (H:exists x:T, P x),
  ProperFilter (fun A : T -> Prop => forall t : T, P t -> A t).
Proof.
intros P (x,Hx).
constructor.
intros Q FQ.
exists x.
now apply FQ.
constructor.
now intro x0.
intros A B HA HB x0 Hx0.
split.
now apply HA.
now apply HB.
intros A B HAB HA x0 Hx0.
apply HAB ; now apply HA.
Qed.

Lemma iotaD'_correct_weak_aux2: forall (P : T -> Prop) (H:exists x:T, P x),
  (forall x y, P x -> P y -> forall eps : posreal, ball x eps y) ->
    cauchy (fun A : T -> Prop => forall t : T, P t -> A t).
Proof.
intros P (x,Hx) H e.
exists x.
intros y Hy.
now apply H.
Qed.

Definition iotaD' (P : T -> Prop) (H:exists x:T, P x)
     (HP: forall x y, P x -> P y -> forall eps : posreal, ball x eps y)
   := lim (fun A => (forall x, P x -> A x)) (iotaD'_correct_weak_aux1 P H)
            (iotaD'_correct_weak_aux2 P H HP).

Lemma iotaD'_correct_weak :
  forall (P : T -> Prop)
  (HP:forall x y, P x -> P y -> forall eps : posreal, ball x eps y)
   (H:(exists x:T, P x))  (eps : posreal),
     forall y, P y -> ball (iotaD' P H HP) eps y.
Proof.
intros P HP H eps.
set (F := fun A : T -> Prop => forall t : T, P t -> A t).
assert (forall eps : posreal, F (ball (iotaD' P H HP) eps)) as HF.
apply complete_cauchyD.
assert (F (ball (iotaD' P H HP) eps)) as Heps.
apply HF.
now apply Heps.
Qed.

End CompleteSpace1.

(** Dependant functional CompleteSpace *)

Section fct_CompleteSpaceD.

Context {T : Type} {U : CompleteSpaceD}.

Let Fr := fun (F : ((T -> U) -> Prop) -> Prop)
   (t : T) (P : U -> Prop) => F (fun g => P (g t)).

Lemma lim_fct_aux1: forall (F : ((T -> U) -> Prop) -> Prop),
    (ProperFilter F) ->  forall t, ProperFilter (Fr F t).
Proof.
  intros F FF.
   case: FF => HF FF t.
    split.
    - move => P Hp.
      case: (HF _ Hp) => f Hf.
      by exists (f t).
    - split.
      + by apply FF.
      + move => P P' Hp Hp'.
      by apply FF.
      + move => P P' Hpp'.
      apply FF.
      move => f ; by apply Hpp'.
Qed.

Lemma lim_fct_aux2: forall (F : ((T -> U) -> Prop) -> Prop),
    (ProperFilter F) -> (cauchy F) ->  forall t, cauchy (Fr F t).
Proof.
intros F FF HFc t.
   move => eps.
    case: (HFc eps) => f Hf.
    exists (f t).
    move: Hf ; apply FF => g.
    by [].
Qed.

Definition lim_fct (F : ((T -> U) -> Prop) -> Prop) (H1: ProperFilter F)
  (H2: cauchy F) (t : T) :=
  lim (Fr F t) (lim_fct_aux1 F H1 t) (lim_fct_aux2 F H1 H2 t).

Lemma complete_cauchy_fct :
  forall (F : ((T -> U) -> Prop) -> Prop)
  (H1: ProperFilter F)  (H2: cauchy F)
   (eps : posreal), F (ball (lim_fct F H1 H2) eps).
Proof.
  move => F FF HFc.
  assert (forall t (eps : posreal), (Fr F t) (fun x => ball (lim_fct F FF HFc t) eps x)).
  move => t.
  apply complete_cauchyD.
  move => eps.
  generalize (proj1 cauchy_distance HFc) => HFc1.
  case: (HFc1 (pos_div_2 eps)) => {HFc1} P ; simpl ; case => HP H0.
  apply filter_imp with (2 := HP).
  move => g Hg t.
  move: (fun h => H0 g h Hg) => {H0}.
  move => H0.
  move: (H t (pos_div_2 eps)) ; simpl => {H}.
  move => H.
  unfold Fr in H ; generalize (filter_and _ _ H HP) => {H}.
  move => H.
  apply filter_ex in H ; case: H => h H.
  rewrite (double_var eps).
  apply ball_triangle with (h t).
  by apply H.
  apply ball_sym, H0.
  by apply H.
Qed.

Definition fct_CompleteSpaceD_mixin :=
  CompleteSpaceD.Mixin _ lim_fct complete_cauchy_fct.

Canonical fct_CompleteSpaceD :=
  CompleteSpaceD.Pack (T -> U) (CompleteSpaceD.Class _ _ fct_CompleteSpaceD_mixin) (T -> U).

End fct_CompleteSpaceD.

(** Dependant Complete Normed Modules *)

Module CompleteNormedModuleD.

Section ClassDef.

Variable K : AbsRing.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : CompleteSpaceD.mixin_of (UniformSpace.Pack T base T)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : CompleteSpaceD.class_of T :=
  CompleteSpaceD.Class _ (base T cT) (mixin T cT).
Local Coercion base2 : class_of >-> CompleteSpaceD.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition NormedModuleAux := NormedModuleAux.Pack _ cT xclass xT.
Definition NormedModule := NormedModule.Pack _ cT xclass xT.
Definition UniformSpace := UniformSpace.Pack cT xclass xT.
Definition CompleteSpaceD := CompleteSpaceD.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> NormedModule.class_of.
Coercion mixin : class_of >-> CompleteSpaceD.mixin_of.
Coercion base2 : class_of >-> CompleteSpaceD.class_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion NormedModuleAux : type >-> NormedModuleAux.type.
Canonical NormedModuleAux.
Coercion NormedModule : type >-> NormedModule.type.
Canonical NormedModule.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Coercion CompleteSpaceD : type >-> CompleteSpaceD.type.
Canonical CompleteSpaceD.
Notation CompleteNormedModuleD := type.

End Exports.

End CompleteNormedModuleD.

Export CompleteNormedModuleD.Exports.

Section CompleteNormedModuleD1.

Context {T : Type} {K : AbsRing} {V : CompleteNormedModuleD K}.

Lemma iotaD_aux1: forall P : V -> Prop,
  (exists! x : V, P x) ->
   (forall x y, P x -> P y -> forall eps : posreal, ball x eps y).
Proof.
intros P [x [Px HP]].
intros u v Pu Pv eps.
replace v with u.
apply ball_center.
apply eq_trans with x.
now apply eq_sym, HP.
now apply HP.
Qed.

Lemma iotaD_aux2: forall (P : V -> Prop),
  (exists! x : V, P x) -> (exists x : V, P x).
Proof.
intros  P [x [Px HP]].
now exists x.
Qed.

Definition iotaD (P : V -> Prop) (HP: (exists! x : V, P x))
   := iotaD' P (iotaD_aux2 P HP) (iotaD_aux1 P HP).

Lemma iota_correct :
  forall (P : V -> Prop)  (HP: exists! x : V, P x),
  P (iotaD P HP).
Proof.
intros P HP.
elim HP; intros x [Px H].
replace (iotaD P HP) with x.
exact Px.
apply eq_sym, eq_close.
intros eps.
unfold iotaD.
now apply: iotaD'_correct_weak.
Qed.

End CompleteNormedModuleD1.

(** CompleteSpace CompleteSpaceD *)

Section CS_is_CSD.

Context {E: CompleteSpace}.

Definition lime : ((E -> Prop)-> Prop) -> E
    := CompleteSpace.lim _ (CompleteSpace.class E).

Lemma CS_is_CSD_aux: forall F (H1:ProperFilter F) (H2:cauchy F),
  forall eps : posreal, F (ball (lime F) eps).
Proof.
intros.
now apply: complete_cauchy.
Qed.

Definition CompleteSpace_CompleteSpaceD_mixin :=
  CompleteSpaceD.Mixin _ (fun F _ _ => (lime F))
     (CS_is_CSD_aux).

Canonical CompleteSpace_CompleteSpaceD :=
  CompleteSpaceD.Pack _ (CompleteSpaceD.Class _ _ CompleteSpace_CompleteSpaceD_mixin) E.

End CS_is_CSD.

(** CompleteNormedModule CompleteNormedModuleD *)

Section CNM_is_CNMD.

Context {E: CompleteNormedModule R_AbsRing}.

Canonical CompleteNormedModule_CompleteNormedModuleD :=
  CompleteNormedModuleD.Pack R_AbsRing E
     (CompleteNormedModuleD.Class R_AbsRing E
            (NormedModule.class R_AbsRing E)
            (@CompleteSpace_CompleteSpaceD_mixin
               (CompleteSpace.Pack E (CompleteSpace.class E) E))) E.

End CNM_is_CNMD.

Canonical R_CompleteNormedModuleD :=
  @CompleteNormedModule_CompleteNormedModuleD R_CompleteNormedModule.

(** Clm is CompleteNormedModuleD *)

Section clm_complete.

Variable E : NormedModule R_AbsRing.
Variable F : CompleteNormedModuleD R_AbsRing.

Definition cleanFilter (Fi: ((clm E F) -> Prop) -> Prop):
  (((E -> F) -> Prop) -> Prop)
    := fun A : (E->F) -> Prop => exists V : clm E F -> Prop,
           Fi V /\ (forall f, V f -> A (m f)).

Let Fr := fun (FF : ((E -> F) -> Prop) -> Prop)
   (t : E) (P : F -> Prop) => FF (fun g => P (g t)).

Let Fri := fun (Fi: ((clm E F) -> Prop) -> Prop)
    (t : E) (P : F -> Prop) => Fr (cleanFilter Fi) t P.

Lemma cleanFilterProper: forall (Fi: ((clm E F) -> Prop) -> Prop),
  ProperFilter Fi -> ProperFilter (cleanFilter Fi).
Proof.
intros Fi (FF1,FF2).
constructor.
unfold cleanFilter.
intros P (V,(HV1,HV2)).
destruct (FF1 V HV1) as (f,Hf).
exists f; now apply HV2.
constructor; unfold cleanFilter.
exists (fun _ => True); split.
apply FF2.
easy.
intros P Q (Vp,(HP1,HP2)) (Vq,(HQ1,HQ2)).
exists (fun x => Vp x /\ Vq x); split.
now apply FF2.
intros f (Hf1,Hf2); split.
now apply HP2.
now apply HQ2.
intros P Q H (Vp,(HP1,HP2)).
exists Vp; split.
easy.
intros f Hf.
apply H; now apply HP2.
Qed.

Lemma clm_lim_aux1: forall (Fi : ((clm E F) -> Prop) -> Prop),
    (ProperFilter Fi) ->  forall t, ProperFilter (Fri Fi t).
Proof.
intros Fi FFi t.
apply lim_fct_aux1.
now apply cleanFilterProper.
Qed.

Lemma clm_lim_aux2: forall (Fi : ((clm E F) -> Prop) -> Prop),
    (ProperFilter Fi) -> (cauchy Fi) -> forall t, cauchy (Fri Fi t).
Proof.
intros Fi FFi HFc t eps.
case (is_zero_dec t); intros Ht.
exists zero.
unfold Fri, Fr, cleanFilter.
exists (fun _ => True).
split.
apply FFi.
intros f _.
replace (f t) with (@zero F).
apply ball_center.
rewrite Ht.
apply sym_eq.
apply: is_linear_mapping_zero.
apply f.
assert (K1: 0 < norm t) by now apply norm_gt_0.
assert (K2: 0 < / norm t) by now apply Rinv_0_lt_compat.
assert (K:0 < eps/norm t).
apply Rmult_lt_0_compat.
apply eps.
exact K2.
destruct (HFc (mkposreal _ K)) as (f,Hf).
exists (f t).
unfold Fri, Fr, cleanFilter.
exists (ball f (eps/norm t)).
split.
exact Hf.
intros g Hg.
unfold ball in Hg; simpl in Hg; unfold clm_ball in Hg.
apply: norm_compat1.
replace (minus (g t) (f t)) with ((minus g f) t) by reflexivity.
apply Rle_lt_trans with (operator_norm (minus g f)*norm t).
apply operator_norm_helper'; try assumption.
apply is_finite_operator_norm_plus.
apply (Cf _ _ g).
apply is_finite_operator_norm_opp.
apply (Cf _ _ f).
apply Rmult_lt_reg_r with (/ norm t); try assumption.
apply Rle_lt_trans with (2:=Hg).
right; field.
now apply Rgt_not_eq.
Qed.

Definition clm_lim (Fi : ((clm E F) -> Prop) -> Prop)
   (H1: ProperFilter Fi) (H2: cauchy Fi) (t:E) :=
      lim (Fri Fi t) (clm_lim_aux1 Fi H1 t) (clm_lim_aux2 Fi H1 H2 t).

Lemma ball_plus_plus: forall (x a y b:F) (eps:posreal), ball x eps a -> ball y eps b ->
      ball (plus x y) (2*(@norm_factor R_AbsRing F)*eps) (plus a b).
Proof.
intros x a y b eps Hx Hy.
pose (v:=@norm_factor R_AbsRing F); fold v.
apply: norm_compat1.
apply Rle_lt_trans with (norm (plus (minus a x) (minus b y))).
right; f_equal.
unfold minus.
rewrite <- 2!plus_assoc; f_equal.
rewrite opp_plus plus_comm; rewrite <- plus_assoc; f_equal.
apply plus_comm.
apply: (Rle_lt_trans _ _ _ (norm_triangle _ _)).
replace (2*v*eps) with (v*eps+v*eps) by ring.
apply Rplus_lt_compat; unfold v.
now apply: norm_compat2.
now apply: norm_compat2.
Qed.

Lemma ball_scal_scal: forall (x a:F) l (eps:posreal),
      l <> 0 -> ball x eps a ->
      ball (scal l x) (Rabs l*@norm_factor R_AbsRing F * eps) (scal l a).
Proof.
intros x a l eps Hl Hx.
pose (v:=@norm_factor R_AbsRing F); fold v.
apply: norm_compat1.
apply Rle_lt_trans with (norm (scal l (minus a x))).
right; f_equal.
unfold minus.
rewrite scal_distr_l; f_equal.
apply sym_eq; apply: scal_opp_r.
rewrite norm_scal_R.
unfold abs; simpl; rewrite Rmult_assoc.
apply Rmult_lt_compat_l.
now apply Rabs_pos_lt.
now apply: norm_compat2.
Qed.

Lemma clm_lim_linear: forall (Fi : ((clm E  F) -> Prop) -> Prop)
   (H1: ProperFilter Fi)  (H2: cauchy Fi),
     is_linear_mapping (clm_lim Fi H1 H2).
Proof.
intros Fi H1 H2; split.
(* plus *)
intros x y.
apply eq_close; intros eps.
pose (v:=@norm_factor R_AbsRing F).
assert (K:0 < eps /4 / v).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply eps.
apply Rinv_0_lt_compat.
apply Rmult_lt_0_compat; apply Rlt_0_2.
apply Rinv_0_lt_compat.
apply norm_factor_gt_0.
(* *)
assert (HX:((fun P : F -> Prop => cleanFilter Fi (fun g : E -> F => P (g x)))
        (ball (clm_lim Fi H1 H2 x) (mkposreal _ K)))).
unfold clm_lim.
apply complete_cauchyD.
destruct HX as (Vx, (Hx1,Hx2)).
assert (HY:((fun P : F -> Prop => cleanFilter Fi (fun g : E -> F => P (g y)))
        (ball (clm_lim Fi H1 H2 y) (mkposreal _ K)))).
unfold clm_lim.
apply complete_cauchyD.
destruct HY as (Vy, (Hy1,Hy2)).
assert (HXY:((fun P : F -> Prop => cleanFilter Fi (fun g : E -> F => P (g (plus x y))))
        (ball (clm_lim Fi H1 H2 (plus x y)) (pos_div_2 eps)))).
unfold clm_lim.
apply complete_cauchyD.
destruct HXY as (Vxy, (Hxy1,Hxy2)).
(* *)
assert (H:(Fi (fun f => Vx f /\ Vy f /\ Vxy f))).
apply H1; try assumption.
apply H1; assumption.
apply H1 in H.
destruct H as (l,Hl).
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps).
2: simpl; field.
apply ball_triangle with (l (plus x y)).
apply (Hxy2 l), Hl.
replace (l (plus x y)) with (plus (l x) (l y)).
2: apply sym_eq, (Lf _ _ l).
replace (pos (pos_div_2 eps)) with (2*v*(mkposreal _ K)).
apply ball_plus_plus.
apply ball_sym, (Hx2 l), Hl.
apply ball_sym, (Hy2 l), Hl.
simpl; field.
apply Rgt_not_eq, norm_factor_gt_0.
(* scal *)
intros x l.
case (Req_dec l 0); intros Hl.
(* . l = 0 *)
rewrite Hl 2!scal_zero_l.
apply eq_close; intros eps.
assert (H:((fun P : F -> Prop => cleanFilter Fi (fun g : E -> F => P (g zero)))
        (ball (clm_lim Fi H1 H2 zero) (eps)))).
unfold clm_lim.
apply complete_cauchyD.
destruct H as (V,(HV1,HV2)).
apply H1 in HV1; destruct HV1 as (f,Hf).
specialize (HV2 f Hf).
replace (f zero) with (@zero F) in HV2.
exact HV2.
apply sym_eq; apply: is_linear_mapping_zero.
apply (Lf _ _ f).
(* . l <> 0 *)
apply eq_close; intros eps.
pose (v:=@norm_factor R_AbsRing F).
assert (K:0 < pos_div_2 eps /Rabs l / v).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply (pos_div_2 eps).
apply Rinv_0_lt_compat.
now apply Rabs_pos_lt.
apply Rinv_0_lt_compat.
apply norm_factor_gt_0.
(* *)
assert (HX:((fun P : F -> Prop => cleanFilter Fi (fun g : E -> F => P (g x)))
        (ball (clm_lim Fi H1 H2 x) (mkposreal _ K)))).
unfold clm_lim.
apply complete_cauchyD.
destruct HX as (Vx, (Hx1,Hx2)).
assert (HLX:((fun P : F -> Prop => cleanFilter Fi (fun g : E -> F => P (g (scal l x))))
        (ball (clm_lim Fi H1 H2 (scal l x)) (pos_div_2 eps)))).
unfold clm_lim.
apply complete_cauchyD.
destruct HLX as (Vlx, (Hlx1,Hlx2)).
(* *)
assert (H:(Fi (fun f => Vx f /\ Vlx f))).
apply H1; assumption.
apply H1 in H.
destruct H as (f,Hf).
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps).
2: simpl; field.
apply ball_triangle with (f (scal l x)).
apply (Hlx2 f), Hf.
replace (f (scal l x)) with (scal l (f x)).
2: apply sym_eq, (Lf _ _ f).
replace (pos (pos_div_2 eps)) with (Rabs l*v*(mkposreal _ K)).
apply ball_scal_scal; try assumption.
apply ball_sym, (Hx2 f), Hf.
simpl; field; split.
apply Rgt_not_eq, Rabs_pos_lt; assumption.
apply Rgt_not_eq, norm_factor_gt_0.
Qed.

Lemma clm_lim_continuous: forall (Fi : ((clm E  F) -> Prop) -> Prop)
   (H1: ProperFilter Fi)  (H2: cauchy Fi),
     is_finite (operator_norm (clm_lim Fi H1 H2)).
Proof.
intros Fi H1 H2.
pose (v:=@norm_factor R_AbsRing F).
elim (H2 (mkposreal _ Rlt_0_1)); intros f Hf; simpl in Hf.
replace (clm_lim Fi H1 H2) with
    (plus (m f) (plus (clm_lim Fi H1 H2) (opp f))).
apply is_finite_operator_norm_plus.
apply (Cf _ _ f).
apply operator_norm_helper3 with (2).
left; apply Rlt_0_2.
intros x NZx.
assert (K: 0 < norm x /v).
apply Rmult_lt_0_compat.
now apply norm_gt_0.
apply Rinv_0_lt_compat.
apply norm_factor_gt_0.
assert (HX:((fun P : F -> Prop => cleanFilter Fi (fun g : E -> F => P (g x)))
        (ball (clm_lim Fi H1 H2 x) (mkposreal _ K)))).
unfold clm_lim.
apply complete_cauchyD.
destruct HX as (V,(HV1,HV2)); simpl in HV2.
assert (H:(Fi (fun z => V z /\  (ball f 1 z)))).
apply H1; assumption.
apply H1 in H.
destruct H as (g,(Hg1,Hg2)).
specialize (HV2 g Hg1).
unfold ball in Hg2; simpl in Hg2; unfold clm_ball in Hg2.
apply Rle_trans with
  (norm (plus (minus (clm_lim Fi H1 H2 x) (g x))
              (minus (g x) (f x)))).
right; f_equal.
unfold minus; rewrite <- plus_assoc.
apply trans_eq with (plus (clm_lim Fi H1 H2 x) (opp (f x))).
reflexivity.
f_equal.
rewrite plus_assoc.
rewrite (plus_opp_l (g x)).
apply sym_eq, plus_zero_l.
apply Rle_trans with (norm (minus (clm_lim Fi H1 H2 x) (g x))
      + norm (minus (g x) (f x))).
apply: norm_triangle.
replace (2*norm x) with (v*(mkposreal _ K)+ norm x).
apply Rplus_le_compat.
left; unfold v; apply: norm_compat2.
now simpl; apply ball_sym.
replace (minus (g x) (f x)) with ((minus g f) x) by reflexivity.
apply Rle_trans with (operator_norm (minus g f)*norm x).
apply operator_norm_helper'; try assumption.
apply is_finite_operator_norm_plus.
apply (Cf _ _ g).
apply is_finite_operator_norm_opp.
apply (Cf _ _ f).
rewrite <- (Rmult_1_l (norm x)) at 2.
apply Rmult_le_compat_r.
apply norm_ge_0.
now left.
simpl; field.
apply Rgt_not_eq, norm_factor_gt_0.
rewrite plus_comm - plus_assoc.
rewrite plus_opp_l.
apply plus_zero_r.
Qed.

Definition Clm_lim:= fun (Fi : ((clm E F) -> Prop) -> Prop)
   (H1: ProperFilter Fi)  (H2: cauchy Fi) =>
      Clm E F (clm_lim Fi H1 H2) (clm_lim_linear Fi H1 H2)
                                 (clm_lim_continuous Fi H1 H2).

Lemma complete_cauchy_clm :
  forall (Fi : ((clm E F) -> Prop) -> Prop)
         (H1:ProperFilter Fi) (H2:cauchy Fi),
       forall eps : posreal, Fi (ball (Clm_lim Fi H1 H2) eps).
Proof.
intros Fi H1 H2 eps.
pose (v:=@norm_factor R_AbsRing F).
generalize (proj1 cauchy_distance H2) => HFc1.
destruct (HFc1 (pos_div_2 (pos_div_2 eps))) as (P, (HP1,HP2)).
apply filter_imp with (2:=HP1).
intros f Hf.
unfold ball; simpl; unfold clm_ball; simpl.
apply Rle_lt_trans with (pos_div_2 eps).
apply operator_norm_helper3'.
left; apply (pos_div_2 eps).
intros u Hu.
assert (K:0 < eps/4*norm u/v).
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply Rmult_lt_0_compat.
apply (eps).
apply Rinv_0_lt_compat.
apply Rmult_lt_0_compat; apply Rlt_0_2.
now apply norm_gt_0.
apply Rinv_0_lt_compat.
apply norm_factor_gt_0.
assert (HH:((fun P : F -> Prop => cleanFilter Fi (fun g : E -> F => P (g u)))
        (ball (clm_lim Fi H1 H2 u) (mkposreal _ K)))).
unfold clm_lim.
apply complete_cauchyD.
simpl in HH; destruct HH as (V,(HV1,HV2)).
assert (H:(Fi (fun z => V z /\  P z))).
apply H1; assumption.
apply H1 in H.
destruct H as (g,(Hg1,Hg2)).
specialize (HV2 g Hg1).
apply Rle_trans with (norm (plus (minus (g u) (clm_lim Fi H1 H2 u)) (opp (minus (g u) (f u))))).
right; f_equal.
apply trans_eq with (plus (f u) (opp (clm_lim Fi H1 H2 u))).
reflexivity.
unfold minus; rewrite plus_comm (plus_comm (g u) _).
rewrite <- plus_assoc; f_equal.
rewrite opp_plus opp_opp.
now rewrite plus_assoc plus_opp_r plus_zero_l.
apply Rle_trans with (1:=norm_triangle _ _).
replace (pos_div_2 eps*norm u) with (v*(mkposreal _ K)+eps/2/2*norm u).
apply Rplus_le_compat.
left; unfold v; apply: norm_compat2.
exact HV2.
rewrite norm_opp.
specialize (HP2 f g Hf Hg2).
unfold ball in HP2; simpl in HP2; unfold clm_ball in HP2.
apply Rle_trans with (norm ((minus g f) u)).
right; reflexivity.
apply Rle_trans with (operator_norm (minus g f)*norm u).
apply operator_norm_helper'; try assumption.
apply is_finite_operator_norm_plus.
apply (Cf _ _ g).
apply is_finite_operator_norm_opp.
apply (Cf _ _ f).
apply Rmult_le_compat_r.
apply norm_ge_0.
now left.
simpl; field.
apply Rgt_not_eq.
apply norm_factor_gt_0.
rewrite <- (Rmult_1_r eps).
unfold pos_div_2; simpl; unfold Rdiv.
apply Rmult_lt_compat_l.
apply eps.
apply Rmult_lt_reg_l with 2.
apply Rlt_0_2.
rewrite Rinv_r.
rewrite Rmult_1_r.
apply Rplus_lt_reg_l with (-1); ring_simplify.
apply Rlt_0_1.
apply Rgt_not_eq, Rlt_0_2.
Qed.

Definition clm_CompleteSpaceD_mixin :=
  CompleteSpaceD.Mixin _ Clm_lim complete_cauchy_clm.

Canonical clm_CompleteSpaceD :=
  CompleteSpaceD.Pack (clm E F) (CompleteSpaceD.Class _ _ clm_CompleteSpaceD_mixin) (clm E F).

Canonical clm_CompleteNormedModuleD :=
  CompleteNormedModuleD.Pack _ (clm E F)
     (CompleteNormedModuleD.Class R_AbsRing _
       (NormedModule.class _ (clm_NormedModule E F))
      clm_CompleteSpaceD_mixin) (clm E F).

End clm_complete.
