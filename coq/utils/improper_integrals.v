(* from improper_integrals coq library *)
From mathcomp Require Import ssreflect.
Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Lra.

Lemma ball_Rabs x y e : ball x e y <-> Rabs (y - x) < e.
Proof. intros; tauto. Qed.

Definition filter_Rlt F1 F2 :=
  exists m, filter_prod F1 F2 (fun p => fst p < m < snd p).

Lemma filter_Rlt_witness m (F1 F2  : (R -> Prop) -> Prop) :
  F1 (Rgt m) -> F2 (Rlt m) ->  filter_Rlt F1 F2.
Proof.
exists m; split with (Rgt m) (Rlt m); simpl; auto with real.
Qed.

Lemma filter_Rlt_m_infty_p_infty :
  filter_Rlt (Rbar_locally m_infty) (Rbar_locally p_infty).
Proof.
apply (filter_Rlt_witness 0); exists 0; tauto.
Qed.

Lemma filter_Rlt_m_infty_at_left b :
  filter_Rlt (Rbar_locally m_infty) (at_left b).
Proof.
apply (filter_Rlt_witness (b - 1)).
now exists (b - 1); intros x cmpx; apply Rlt_gt.
exists posreal_half; intros x yb _.
enough (b - x  < 1) by lra.
apply Rle_lt_trans with (abs (minus b x)).
  now apply Rle_abs.
apply ball_sym in yb; apply AbsRing_norm_compat2 in yb.
apply Rlt_trans with (1 := yb).
rewrite Rmult_1_l; simpl.
lra.
Qed.

Lemma filter_Rlt_at_right_p_infty b :
  filter_Rlt (at_right b) (Rbar_locally p_infty).
Proof.
apply (filter_Rlt_witness (b + 1)).
  exists posreal_half; intros y yb _.
  enough (y - b < 1) by lra.
  apply Rle_lt_trans with (abs (minus y b)).
    now apply Rle_abs.
  apply AbsRing_norm_compat2 in yb.
  apply Rlt_trans with (1 := yb).
  rewrite Rmult_1_l; simpl.
  lra.
now exists (b + 1); intros x cmpx.
Qed.

Lemma filter_Rlt_at_point_p_infty b :
  filter_Rlt (at_point b) (Rbar_locally p_infty).
Proof.
apply (filter_Rlt_witness (b + 1)).
  now unfold at_point; lra.
now exists (b + 1); tauto.
Qed.

Lemma filter_Rlt_m_infty_at_point b :
  filter_Rlt (Rbar_locally m_infty) (at_point b).
Proof.
apply (filter_Rlt_witness (b - 1)).
  now exists (b - 1); tauto.
now unfold at_point; lra.
Qed.

Local Lemma compare_half_sum a b (altb : a < b) : a < (a + b) / 2 < b.
Proof.
assert ((a + b) / 2 * 2 = a + b) by field.
split; apply Rmult_lt_reg_r with 2; lra.
Qed.

Lemma filter_Rlt_at_point a b : a < b ->
  filter_Rlt (at_point a) (at_point b).
Proof.
intros altb; apply filter_Rlt_witness with ((a + b) / 2).
  unfold at_point.
  now destruct (compare_half_sum _ _ altb); tauto.
unfold at_point.
now destruct (compare_half_sum _ _ altb); tauto.
Qed.

Lemma Rplus_minus_cancel1 : forall a b, a + b - a = b.
Proof. intros; ring. Qed.

Lemma filter_Rlt_locally a b : a < b ->
  filter_Rlt (Rbar_locally a) (Rbar_locally b).
Proof.
intros ab.
assert (bmap: 0 < (b - a)/2).
  apply Rmult_lt_reg_r with 2;[lra | ].
  unfold Rdiv; rewrite -> Rmult_0_l, Rmult_assoc.
  rewrite -> Rinv_l, Rmult_1_r;[ | apply Rgt_not_eq]; lra.
apply (filter_Rlt_witness ((a + b)/2)).
  exists (mkposreal _ bmap); intros y ya.
  enough (yma : y * 2 - a * 2 < b - a).
    apply Rmult_lt_reg_r with 2;[lra | ].
    unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l;[ | apply Rgt_not_eq; lra].
    rewrite -> Rmult_1_r; lra.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_reg_r with (/2).
    apply Rinv_0_lt_compat; lra.
  rewrite -> Rmult_assoc, Rinv_r, Rmult_1_r;[|apply Rgt_not_eq; lra].
  apply Rle_lt_trans with (abs (minus y a)).
    now apply Rle_abs.
  apply AbsRing_norm_compat2 in ya; apply Rlt_le_trans with (1 := ya).
  now rewrite -> Rmult_1_l; simpl; auto with real.
exists (mkposreal _ bmap); intros y yb.
enough (yma : b * 2 - y * 2 < b - a).
  apply Rmult_lt_reg_r with 2;[lra | ].
  unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l;[ | apply Rgt_not_eq; lra].
  rewrite -> Rmult_1_r; lra.
rewrite <- Rmult_minus_distr_r; apply Rmult_lt_reg_r with (/2).
  apply Rinv_0_lt_compat; lra.
rewrite -> Rmult_assoc, Rinv_r, Rmult_1_r;[|apply Rgt_not_eq; lra].
apply Rle_lt_trans with (abs (minus b y)).
  now apply Rle_abs.
apply ball_sym in yb; apply AbsRing_norm_compat2 in yb.
  apply Rlt_le_trans with (1 := yb).
now rewrite -> Rmult_1_l; simpl; auto with real.
Qed.

Lemma filter_Rlt_left_right  a b : a <= b ->
  filter_Rlt (at_left a) (at_right b).
intros ab; apply (filter_Rlt_witness a).
  now exists posreal_half; intros y _; apply Rgt_lt.
now exists posreal_half; intros y _ yb ; apply Rle_lt_trans with b.
Qed.

Lemma filter_Rlt_trans a F G {FF : Filter F} {GG : Filter G} :
  filter_Rlt F (at_point a) ->
  filter_Rlt (at_point a) G -> filter_Rlt F G.
Proof.
intros [m1 Pm1] [m2 Pm2].
apply filter_Rlt_witness with a.
  destruct Pm1 as [P Q FP atQ cnd1].
  assert (qa : Q a) by now apply atQ; intros; apply ball_center.
  apply (filter_imp P); auto.
  intros x px.
  assert (t := cnd1 x a px qa); simpl in t; destruct t; lra.
destruct Pm2 as [P Q atP GQ cnd2].
assert (pa : P a) by now apply atP; intros; apply ball_center.
apply (filter_imp Q); auto.
intros x qx.
assert (t := cnd2 a x pa qx); simpl in t; destruct t; lra.
Qed.

Lemma filter_Rlt_right_left a b : a < b ->
  filter_Rlt (at_right a) (at_left b).
Proof.
intros ab.
assert (bmap: 0 < (b - a)/2).
  apply Rmult_lt_reg_r with 2;[lra | ].
  unfold Rdiv; rewrite -> Rmult_0_l, Rmult_assoc.
  rewrite -> Rinv_l, Rmult_1_r;[ | apply Rgt_not_eq]; lra.
apply (filter_Rlt_witness ((a + b)/2)).
  exists (mkposreal _ bmap); intros y ya cmp.
  enough (yma : y * 2 - a * 2 < b - a).
    apply Rmult_lt_reg_r with 2;[lra | ].
    unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l;[ | apply Rgt_not_eq; lra].
    rewrite -> Rmult_1_r; lra.
  rewrite <- Rmult_minus_distr_r; apply Rmult_lt_reg_r with (/2).
    apply Rinv_0_lt_compat; lra.
  rewrite -> Rmult_assoc, Rinv_r, Rmult_1_r;[|apply Rgt_not_eq; lra].
  apply Rle_lt_trans with (abs (minus y a)).
    now apply Rle_abs.
  apply AbsRing_norm_compat2 in ya; apply Rlt_le_trans with (1 := ya).
  now rewrite -> Rmult_1_l; simpl; auto with real.
exists (mkposreal _ bmap); intros y yb cmp.
enough (yma : b * 2 - y * 2 < b - a).
  apply Rmult_lt_reg_r with 2;[lra | ].
  unfold Rdiv; rewrite -> Rmult_assoc, Rinv_l;[ | apply Rgt_not_eq; lra].
  rewrite -> Rmult_1_r; lra.
rewrite <- Rmult_minus_distr_r; apply Rmult_lt_reg_r with (/2).
  apply Rinv_0_lt_compat; lra.
rewrite -> Rmult_assoc, Rinv_r, Rmult_1_r;[|apply Rgt_not_eq; lra].
apply Rle_lt_trans with (abs (minus b y)).
  now apply Rle_abs.
apply ball_sym in yb; apply AbsRing_norm_compat2 in yb.
  apply Rlt_le_trans with (1 := yb).
now rewrite -> Rmult_1_l; simpl; auto with real.
Qed.

Local Ltac chain_comparisons :=
  match goal with
  | h : ?a <= _ |- ?a < _ => apply Rle_lt_trans with (1 := h)
  | h : _ <= ?a |- _ < ?a => apply Rlt_le_trans with (2 := h)
  | h : ?a < _ |- ?a < _ => apply Rlt_trans with (1 := h)
  | h : _ < ?a |- _ < ?a => apply Rlt_trans with (2 := h)
  end.

Lemma ex_RInt_gen_bound (g : R -> R) (f : R -> R) F G
  {PF : ProperFilter F} {PG : ProperFilter G} :
  filter_Rlt F G ->
  ex_RInt_gen g F G ->
  filter_prod F G
    (fun p => (forall x, fst p < x < snd p -> 0 <= f x <= g x) /\
       ex_RInt f (fst p) (snd p)) ->
    ex_RInt_gen f F G.
Proof.
intros [m mmid] [gl intg] cmp.
assert (F (Rgt m)).
  destruct mmid as [pf pg fpf gpg cmp'].
  apply (filter_imp pf); destruct (filter_ex pg) as [y py]; auto.
  intros x px; destruct (cmp' x y px py) as [it _]; exact it.
assert (G (Rlt m)).
  destruct mmid as [pf pg fpf gpg cmp'].
  apply (filter_imp pg); destruct (filter_ex (F := F) pf) as [x px]; auto.
  intros y py; destruct (cmp' x y px py) as [_ it]; exact it.
exists (lim (filtermap (fun p => RInt f (fst p) (snd p)) (filter_prod F G))).
destruct cmp as [Q1 R1 fq1 gr1 cmp]; simpl in cmp.
assert (cc : cauchy (filtermap (fun p => RInt f (fst p) (snd p))
                       (filter_prod F G))).
  intros eps.
  destruct (intg _ (locally_ball gl (pos_div_2 eps))) as [Qg Rg FQg GRg main].
  assert (fq : F (fun x => Q1 x /\ Qg x /\ m > x))
    by now repeat apply filter_and.
  assert (gr : G (fun x => R1 x /\ Rg x /\ m < x))
    by now repeat apply filter_and.
  destruct (filter_ex _ fq) as [x qx], (filter_ex _ gr) as [y ry].
    exists (RInt f x y).
  exists (fun x => Q1 x /\ Qg x /\ m > x)
         (fun y => R1 y /\ Rg y /\ m < y);
    try now repeat apply filter_and.
  intros u v Qu Rv.
  assert (wlog_cc : forall a b c d,
            Q1 a /\ Qg a ->
            Q1 b /\ Qg b ->
            R1 c /\ Rg c ->
            R1 d /\ Rg d ->
            a <= b -> c <=d -> b < m -> m < c ->
            (ball (RInt f a d) eps (RInt f b c) /\
            ball (RInt f a c) eps (RInt f b d))).
    clear x y qx ry u v Qu Rv; intros a b c d Qa Qb Rc Rd ab cd bm mc.
    assert (ex_RInt f a c /\ ex_RInt f b c /\ ex_RInt f b d).
      now repeat apply conj; apply cmp.
    move main after mc.
    destruct (main a c) as [gac [acP acQ]]; try tauto; simpl in acP.
    assert (ex_RInt g a c) by (eapply ex_intro; eauto).
    destruct (main b c) as [gbc [bcP bcQ]]; try tauto; simpl in bcP.
    assert (ex_RInt g b c) by (eapply ex_intro; eauto).
    destruct (main b d) as [gbd [bdP bdQ]]; try tauto; simpl in bdP.
    assert (ex_RInt g b d) by (eapply ex_intro; eauto).
    assert (ex_RInt f a b).
      now apply ex_RInt_Chasles with c;[ | apply ex_RInt_swap].
    assert (ex_RInt f c d).
      now apply ex_RInt_Chasles with b;[apply ex_RInt_swap | ].
    assert (ex_RInt g a b).
      now apply ex_RInt_Chasles with c;[ | apply ex_RInt_swap];
       eapply ex_intro; eauto.
    assert (ex_RInt g c d).
      now apply ex_RInt_Chasles with b;[apply ex_RInt_swap | ];
       eapply ex_intro; eauto.
    assert (bc : b < c) by (apply Rlt_trans with m; tauto).
    split.
      apply ball_sym, Rle_lt_trans with (Rabs (RInt g a d - RInt g b c)).
        rewrite <- (RInt_Chasles f a b d), <- (RInt_Chasles f b c d),
                <- (RInt_Chasles g a b d), <- (RInt_Chasles g b c d),
               !(Rplus_comm (RInt _ a b)), !Rplus_assoc, !Rplus_minus_cancel1;
         try tauto.
        unfold abs; simpl; rewrite -> !Rabs_right;
        try (apply Rle_ge, Rplus_le_le_0_compat; apply RInt_ge_0; auto);
(* The following fragment duplicated several times. *)
        try (intros x [x1 x2]; enough (0 <= f x <= g x)
           by (solve[tauto | apply Rle_trans with (f x); tauto]);
           apply (cmp a d); try tauto; split;
           solve[repeat (auto; chain_comparisons)]).
        apply Rplus_le_compat; apply RInt_le; try tauto;
(* the following fragment duplicated several times. *)
        try (intros x [x1 x2]; enough (0 <= f x <= g x)
           by (solve[tauto | apply Rle_trans with (f x); tauto]);
           apply (cmp a d); try tauto; split;
           solve[repeat (auto; chain_comparisons)]).
      change (ball (RInt g b c) eps (RInt g a d)).
      replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
      apply ball_triangle with gl.
        now rewrite -> (is_RInt_unique _ _ _ _ bcP); apply ball_sym.
      destruct (main a d) as [gad [adP adQ]]; try tauto; simpl in adP.
      now rewrite -> (is_RInt_unique _ _ _ _ adP).
    change (Rabs (RInt f b d + - RInt f a c) < eps).
    rewrite <- (RInt_Chasles f b c d), <- (RInt_Chasles f a b c),
      Ropp_plus_distr, !Rplus_assoc, (Rplus_comm (RInt f b c)), !Rplus_assoc,
      Rplus_opp_l, Rplus_0_r; try tauto.
    apply Rle_lt_trans with (1 := Rabs_triang _ _);
       rewrite -> Rabs_Ropp, !Rabs_right;
    try (apply Rle_ge, RInt_ge_0; try tauto);
(* the following fragment duplicated several times. *)
        try (intros x [x1 x2]; enough (0 <= f x <= g x)
           by (solve[tauto | apply Rle_trans with (f x); tauto]);
           apply (cmp a d); try tauto; split;
           solve[repeat (auto; chain_comparisons)]).
    replace (pos eps) with (pos_div_2 eps + pos_div_2 eps)
             by (simpl; field).
    assert (dc : RInt f c d <= RInt g c d /\ RInt f a b <= RInt g a b).
      split; apply RInt_le; try tauto;
(* the following fragment duplicated several times. *)
        try (intros x [x1 x2]; enough (0 <= f x <= g x)
           by (solve[tauto | apply Rle_trans with (f x); tauto]);
           apply (cmp a d); try tauto; split;
           solve[repeat (auto; chain_comparisons)]).
    apply Rle_lt_trans with (1 := Rplus_le_compat _ _ _ _ (proj1 dc)(proj2 dc)).
    apply Rle_lt_trans with (1 := Rle_abs _).
    replace (RInt _ _ _ + _) with
      ((RInt g a d - gl) - (RInt g b c - gl)) by (*TODO : explain this! *)
    (rewrite <- (RInt_Chasles g a b d), <- (RInt_Chasles g b c d);
            try tauto; set (zoo := plus); change zoo with Rplus; ring).
    apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
      destruct (main a d) as [gad [adP adQ]]; try tauto; simpl in adP.
      now rewrite -> (is_RInt_unique _ _ _ _ adP).
    now rewrite -> Rabs_Ropp; rewrite -> (is_RInt_unique _ _ _ _ bcP).
  destruct (Rlt_dec x u), (Rlt_dec v y);
   [apply (wlog_cc x u v y) | apply (wlog_cc x u y v) |
    apply ball_sym, (wlog_cc u x v y) | apply ball_sym, (wlog_cc u x y v)];
    try split;
    try solve[tauto | apply Rlt_le; tauto |
      apply Rge_le; tauto | apply Rle_ge; tauto|
      apply Rnot_lt_le; tauto].
intros P [eps Peps].
move cc after Peps.
unfold filtermapi.
assert (tmp := complete_cauchy _ _ cc eps).
destruct tmp as [Q2 R2 Q2P R2P PP2].
exists (fun x => Q2 x /\ Q1 x) (fun x => R2 x /\ R1 x);
  try (apply filter_and; auto).
intros x y [Q2x Q1x] [R2x R1x].
destruct (cmp x y Q1x R1x) as [cmp' [fxy intxy]].
exists fxy; split;[assumption | apply Peps].
rewrite <- (is_RInt_unique _ _ _ _ intxy); apply PP2; auto.
Qed.

Lemma is_RInt_gen_Rle (g : R -> R) gl (f : R -> R) fl F G
  {PF : ProperFilter F} {PG : ProperFilter G} :
  filter_Rlt F G ->
  is_RInt_gen g F G gl ->
  is_RInt_gen f F G fl ->
  filter_prod F G
    (fun p => (forall x, fst p < x < snd p -> f x <= g x)) ->
    fl <= gl.
Proof.
intros [m mmid] intg intf cmp.
apply (filterlim_le (F := filter_prod F G) (fun p => RInt f (fst p) (snd p))
          (fun p => RInt g (fst p) (snd p)) fl gl).
    specialize (intf _ (locally_ball fl (mkposreal _ Rlt_0_1))).
    specialize (intg _ (locally_ball gl (mkposreal _ Rlt_0_1))).
    unfold filtermapi in intg, intf.
    apply: filter_imp (filter_and _ _ (filter_and _ _ intg intf)
                          (filter_and _ _ mmid cmp)).
    intros [a b]; simpl; intros [[[Ig [Hg1 Hg2]] [If [Hf1 Hf2]]] [cmp']]. 
    apply RInt_le;
      [apply Rle_trans with m;apply Rlt_le | exists If| exists Ig| ]; tauto.
  intros P HP; specialize (intf P HP); unfold filtermapi, filtermap in intf |- *.
  apply: filter_imp intf.
  intros [a b]; simpl; intros [y [inty Py]].
  now  rewrite -> (is_RInt_unique _ _ _ _ inty).
intros P HP; specialize (intg P HP); unfold filtermapi, filtermap in intg |- *.
apply: filter_imp intg.
intros [a b]; simpl; intros [y [inty Py]].
now  rewrite -> (is_RInt_unique _ _ _ _ inty).
Qed.

Lemma is_RInt_gen_at_point_at_right (f : R -> R) (a : R) F {FF : ProperFilter F}
  v : locally a (continuous f) -> is_RInt_gen f (at_point a) F v ->
  filter_Rlt (at_point a) F ->  is_RInt_gen f (at_right a) F v.
Proof.
intros [delta1 pd1] intf [m [P Q FP FQ cmp]]; simpl in cmp.
destruct (pd1 a (ball_center a delta1)
          (ball (f a) (mkposreal _ Rlt_0_1)) (locally_ball _ _)) as
    [delta2 Pd2].
assert (pa : P a) by (apply FP; intros; apply ball_center).
assert (intf2 := intf).
intros P2 PP2; specialize (intf P2 PP2); destruct PP2 as [eps P2eps].
set (M := Rabs (f a) + 1).
assert (M0 : 0 < eps / M).
  apply Rmult_lt_0_compat;[apply cond_pos | apply Rinv_0_lt_compat].
  now assert (0 <= Rabs (f a)) by apply Rabs_pos; unfold M; lra.
assert (close : forall y, y <> a -> ball a delta2 y -> Rabs (f y) < M).
  intros y ay b_y; unfold M.
  replace (f y) with (f a + (f y - f a)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  now apply Rplus_lt_compat_l, Pd2; auto.
assert (exrint_close : forall a', ball a delta1 a' -> ex_RInt f a a').
  intros a' baa'.
  apply (ex_RInt_continuous f); intros z pz; apply pd1.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_left, Rmax_right in pz; auto.
    change (Rabs (z - a) < delta1).
    rewrite -> Rabs_right; cycle 1.
      destruct pz; lra.
    destruct pz; apply Rle_lt_trans with (a' - a); try lra.
    rewrite <- (Rabs_right (a' - a)); try lra.
    tauto.
  change (Rabs (z - a) < delta1).
  destruct (Rle_dec a z) as [az | za].
    apply Rnot_le_lt in a'a.
    rewrite -> Rmin_right, Rmax_left in pz; try (destruct pz; lra).
    assert (za' : z = a).
      now apply Rle_antisym; (destruct pz; lra).
    now rewrite -> za', Rminus_eq_0, Rabs_R0; case delta1; tauto.
  apply Rnot_le_lt in a'a; apply Rnot_le_lt in za.
  rewrite -> Rmin_right, Rmax_left in pz; try lra.
  rewrite -> Rabs_left;[ | lra].
  apply Rle_lt_trans with (a - a'); try (intuition lra).
  rewrite <- (Rabs_right (a - a')); try (intuition lra).
  now change (ball a' delta1 a); apply ball_sym; tauto.
assert (pre_ep2 : 0 < eps / 2 * /M).
  repeat apply Rmult_lt_0_compat; try lra;[destruct eps; tauto | ].
  now apply Rinv_0_lt_compat; unfold M; assert (t := Rabs_pos (f a)); lra.
set (ep2 := mkposreal _ pre_ep2).
assert (at_right a (fun x => ball a delta1 x /\ ball a ep2 x /\
                             ball a delta2 x /\ a < x /\ x < m)).
  repeat apply filter_and; try (now apply filter_le_within, locally_ball).
    now exists ep2; intros; tauto.
  destruct (filter_ex _ FQ) as [y' Py'].
  assert (ma0 : 0 < m - a).
    now destruct (cmp a y'); auto; lra.
  exists (mkposreal _ ma0); simpl; intros y.
  intros bay ay; change (Rabs (y - a) < m - a) in bay.
  now rewrite -> Rabs_right in bay; lra.
specialize (intf2 _ (locally_ball v (pos_div_2 eps))).
destruct intf2 as [Pl Ql FPl FQl closerint].
assert (pla : Pl a) by (apply FPl; intros; apply ball_center).
assert (F (fun y => Q y /\ Ql y)) by (apply filter_and; auto).
exists (fun x => ball a delta1 x /\ ball a ep2 x /\
                 ball a delta2 x /\ a < x /\ x < m)
       (fun y => Q y /\ Ql y); auto.
intros x y bx Ry; exists (RInt f x y).
destruct (closerint a y) as [fay [close_fay]]; try tauto.
split.
  simpl. apply (RInt_correct f x y).
  apply (ex_RInt_Chasles_2 f a);[ | exists fay; tauto].
  split; apply Rlt_le;
    [| apply Rlt_trans with m; assert (t := cmp a y pa (proj1 Ry))]; tauto.
apply P2eps.
assert (Rabs (RInt f a x) < pos_div_2 eps).
  apply Rle_lt_trans with ((x - a) * M).
    apply abs_RInt_le_const;[apply Rlt_le; tauto | | ].
      now apply exrint_close; tauto.
    intros t atx.
    replace (f t) with (f a + (f t - f a)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _).
    apply Rplus_le_compat;[apply Rle_refl | ].
    apply Rlt_le, (Pd2 t).
    change (Rabs (t - a) < delta2); rewrite -> Rabs_right;[ | intuition lra].
    apply Rle_lt_trans with (x - a);[intuition lra | ].
    now rewrite <- (Rabs_right (x - a));[tauto | intuition lra].
  replace (pos (pos_div_2 eps)) with (ep2 * M).
    rewrite <- (Rabs_right (x - a));[|intuition lra].
    apply Rmult_lt_compat_r;[unfold M  | tauto].
    now assert (t := Rabs_pos (f a)); lra.
  simpl; field; unfold M; apply Rgt_not_eq; assert (t := Rabs_pos (f a)).
  now lra.
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
apply ball_triangle with (RInt f a y); cycle 1.
  change (Rabs (RInt f x y - RInt f a y) < pos_div_2 eps).
  replace (RInt f a y) with (RInt f a x + RInt f x y); cycle 1.
  apply (RInt_Chasles f).
      now apply exrint_close; tauto.
    apply (ex_RInt_Chasles_2 f a).
      split;[apply Rlt_le; tauto | apply Rlt_le, Rlt_trans with m; try tauto].
    now destruct (cmp a y); tauto.
  now exists fay.
  match goal with |- Rabs ?v < _ => replace v with (-RInt f a x) by ring end.
  now rewrite -> Rabs_Ropp.
now rewrite -> (is_RInt_unique f a y fay).
Qed.

Lemma is_RInt_gen_at_point_at_left (f : R -> R) (a : R) F {FF : ProperFilter F}
  v : locally a (continuous f) -> is_RInt_gen f F (at_point a) v ->
  filter_Rlt F (at_point a) ->  is_RInt_gen f F (at_left a) v.
Proof.
intros [delta1 pd1] intf [m [P Q FP FQ cmp]]; simpl in cmp.
destruct (pd1 a (ball_center a delta1)
          (ball (f a) (mkposreal _ Rlt_0_1)) (locally_ball _ _)) as
    [delta2 Pd2].
assert (qa : Q a) by (apply FQ; intros; apply ball_center).
assert (intf2 := intf).
intros P2 PP2; specialize (intf P2 PP2); destruct PP2 as [eps P2eps].
set (M := Rabs (f a) + 1).
assert (M0 : 0 < eps / M).
  apply Rmult_lt_0_compat;[apply cond_pos | apply Rinv_0_lt_compat].
  now assert (0 <= Rabs (f a)) by apply Rabs_pos; unfold M; lra.
assert (close : forall y, y <> a -> ball a delta2 y -> Rabs (f y) < M).
  intros y ay b_y; unfold M.
  replace (f y) with (f a + (f y - f a)) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  now apply Rplus_lt_compat_l, Pd2; auto.
assert (exrint_close : forall a', ball a delta1 a' -> ex_RInt f a' a).
  intros a' baa'.
  apply (ex_RInt_continuous f); intros z pz; apply pd1.
  destruct (Rle_dec a a') as [aa' | a'a].
    rewrite -> Rmin_right, Rmax_left in pz; auto.
    change (Rabs (z - a) < delta1).
    rewrite -> Rabs_right; cycle 1.
      destruct pz; lra.
    destruct pz; apply Rle_lt_trans with (a' - a); try lra.
    rewrite <- (Rabs_right (a' - a)); try lra.
    tauto.
  change (Rabs (z - a) < delta1).
  destruct (Rle_dec a z) as [az | za].
    apply Rnot_le_lt in a'a.
    rewrite -> Rmin_left, Rmax_right in pz; try (destruct pz; lra).
    assert (za' : z = a).
      now apply Rle_antisym; (destruct pz; lra).
    now rewrite -> za', Rminus_eq_0, Rabs_R0; case delta1; tauto.
  apply Rnot_le_lt in a'a; apply Rnot_le_lt in za.
  rewrite -> Rmin_left, Rmax_right in pz; try lra.
  rewrite -> Rabs_left;[ | lra].
  apply Rle_lt_trans with (a - a'); try (intuition lra).
  rewrite <- (Rabs_right (a - a')); try (intuition lra).
  now change (ball a' delta1 a); apply ball_sym; tauto.
assert (pre_ep2 : 0 < eps / 2 * /M).
  repeat apply Rmult_lt_0_compat; try lra;[destruct eps; tauto | ].
  now apply Rinv_0_lt_compat; unfold M; assert (t := Rabs_pos (f a)); lra.
set (ep2 := mkposreal _ pre_ep2).
assert (at_left a (fun x => ball a delta1 x /\ ball a ep2 x /\
                             ball a delta2 x /\ m < x /\ x < a)).
  repeat apply filter_and; try (now apply filter_le_within, locally_ball).
    destruct (filter_ex _ FP) as [y' Py'].
    assert (ma0 : 0 < a - m).
      now destruct (cmp y' a); auto; lra.
    exists (mkposreal _ ma0); simpl; intros y.
    now rewrite ball_Rabs; intros bay ay; rewrite Rabs_left in bay; lra.
  now exists ep2; intros; tauto.
specialize (intf2 _ (locally_ball v (pos_div_2 eps))).
destruct intf2 as [Pl Ql FPl FQl closerint].
assert (pla : Ql a) by (apply FQl; intros; apply ball_center).
assert (F (fun y => P y /\ Pl y)) by (apply filter_and; auto).
exists (fun y => P y /\ Pl y)
       (fun x => ball a delta1 x /\ ball a ep2 x /\
                 ball a delta2 x /\ m < x /\ x < a); auto.
intros x y bx Ry; exists (RInt f x y).
destruct (closerint x a) as [fxa [close_fxa]]; try tauto.
split.
  simpl. apply (RInt_correct f x y).
  apply (ex_RInt_Chasles_1 f _ _ a);[ | exists fxa; tauto].
  split; apply Rlt_le;
    [apply Rlt_trans with m; assert (t := cmp x a (proj1 bx) qa) |]; tauto.
apply P2eps.
assert (Rabs (RInt f y a) < pos_div_2 eps).
  apply Rle_lt_trans with ((a - y) * M).
    apply abs_RInt_le_const;[apply Rlt_le; tauto | | ].
      now apply exrint_close; tauto.
    intros t yta.
    replace (f t) with (f a + (f t - f a)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _).
    apply Rplus_le_compat;[apply Rle_refl | ].
    apply Rlt_le, (Pd2 t).
    change (Rabs (t - a) < delta2); rewrite -> Rabs_left1;[ |intuition lra].
    apply Rle_lt_trans with (a - y);[intuition lra | ].
    rewrite <- (Rabs_right (a - y));[ | intuition lra].
    now rewrite <- Rabs_Ropp, Ropp_minus_distr; tauto.
  replace (pos (pos_div_2 eps)) with (ep2 * M).
    rewrite <- (Rabs_right (a - y));[|intuition lra].
    apply Rmult_lt_compat_r;[unfold M  |].
      now assert (t := Rabs_pos (f a)); lra.
    now rewrite <- Rabs_Ropp, Ropp_minus_distr; tauto.
  simpl; field; unfold M; apply Rgt_not_eq; assert (t := Rabs_pos (f a)).
  now lra.
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
apply ball_triangle with (RInt f x a); cycle 1.
  change (Rabs (RInt f x y - RInt f x a) < pos_div_2 eps).
  replace (RInt f x a) with (RInt f x y + RInt f y a); cycle 1.
  apply (RInt_Chasles f).
      apply (ex_RInt_Chasles_1 f _ _ a).
      split;[ apply Rlt_le, Rlt_trans with m; try tauto| apply Rlt_le; tauto].
        now destruct (cmp x a); tauto.
      now exists fxa.
    now apply exrint_close; tauto.
  match goal with |- Rabs ?v < _ => replace v with (-RInt f y a) by ring end.
  now rewrite -> Rabs_Ropp.
now rewrite -> (is_RInt_unique f x a fxa).
Qed.

Lemma ex_RInt_gen_cut (a : R) (F G: (R -> Prop) -> Prop)
   {FF : ProperFilter F} {FG : ProperFilter G} (f : R -> R) :
   filter_Rlt F (at_point a) -> filter_Rlt (at_point a) G ->
   ex_RInt_gen f F G -> ex_RInt_gen f (at_point a) G.
Proof.
intros lFa laG [vfg Pvfg].
assert (lFG := filter_Rlt_trans _ _ _ lFa laG).
set (v := R_complete_lim (filtermap (fun x => RInt f a x) G)).
exists v; intros P PP2.
destruct laG as [m [S1 S2 p1 p2 laG]]; cbn in laG.
destruct lFa as [m' [S5 S6 p5 p6 lFa]]; cbn in lFa.
assert (S6 a) by apply p6.
assert (S1 a) by apply p1.
assert (t': forall eps : posreal, exists x,
         filtermap (fun x => RInt f a x) G (ball x eps)).
  intros eps.
  specialize (Pvfg (ball vfg (pos_div_2 eps)) (locally_ball _ _)).
  destruct Pvfg as [S7 S8 p7 p8 vfg'].
  destruct (filter_ex (F := G)
                (fun y => S8 y /\ S2 y)) as [y Py].
    repeat apply filter_and; tauto.
  exists (RInt f a y); destruct (filter_ex (F := F)
                        (fun x => S7 x /\ S5 x)) as [x Px].
    repeat apply filter_and; tauto.
  unfold filtermap; apply (filter_imp (fun y => S8 y /\ S2 y)).
  intros z PZ; change (Rabs (RInt f a z - RInt f a y) < eps).
  replace (RInt f a z - RInt f a y) with
          ((RInt f x a + RInt f a z) - (RInt f x a + RInt f a y)) by ring.
    destruct (vfg' x y) as [xy pxy]; try tauto.
    destruct (vfg' x z) as [xz pxz]; try tauto.
    assert (ex_RInt f x y) by (exists xy; tauto).
    assert (ex_RInt f x z) by (exists xz; tauto).
    assert (x < a) by (destruct (lFa x a); intuition lra || tauto).
    assert (a < y) by (destruct (laG a y); intuition lra || tauto).
    assert (a < z) by (destruct (laG a z); intuition lra || tauto).
    assert (ex_RInt f x a).
      apply (ex_RInt_Chasles_1 f x a y);[intuition lra | assumption].
    rewrite -> !(RInt_Chasles f); auto;
       try (apply (ex_RInt_Chasles_2 f x); auto; intuition lra); cycle 1.
    change (ball (RInt f x y) eps (RInt f x z)).
    replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
    replace (RInt f x y) with xy by (symmetry; apply is_RInt_unique; tauto).
    replace (RInt f x z) with xz by (symmetry; apply is_RInt_unique; tauto).
    now apply (ball_triangle _ vfg); [apply ball_sym | ]; tauto.
  now repeat apply filter_and; tauto.
destruct PP2 as [eps Peps].
assert (t := (R_complete
            (filtermap (fun x => RInt f a x) G) _
            t' eps)).
unfold filtermap, filtermapi in t |- *.
assert (atpa : at_point a (eq a)) by reflexivity.
enough (H1 : exists S4, G S4 /\ forall x, S4 x -> is_RInt f a x (RInt f a x)).
  destruct H1 as [S4 [gs4 Ps4]].
  apply (Filter_prod (at_point a) G _ (eq a) 
           (fun x => ball
             (R_complete_lim
                (fun P : R -> Prop => G (fun x0 => P (RInt f a x0)))) eps 
           (RInt f a x) /\ S4 x) atpa (filter_and _ _ t gs4)).
  intros x y <- dist.
  now exists (RInt f a y);split;[apply Ps4; tauto| apply Peps; tauto].
destruct (Pvfg (ball vfg (mkposreal _ Rlt_0_1))) as [S3 S4 fs3 gs4 Ps4].
  now apply locally_ball.
assert (F (Rgt a)).
  apply (filter_imp S5); [intros x s5x | auto].
  assert (s6a : S6 a) by apply p6.
  destruct (lFa x a s5x s6a); lra.
destruct (filter_ex (F := F) (fun x => a > x /\ S3 x)) as [w Pw];
  [apply filter_and; auto | ].
exists (fun x => S4 x /\ a < x); split;[ | intros x px; apply (RInt_correct f)].
  apply filter_and;[assumption | apply (filter_imp S2);[intros x s2x | easy]].
  assert (s1a : S1 a) by apply p1.
  destruct (laG a x s1a s2x); lra.
apply ex_RInt_Chasles_2 with w;[split; apply Rlt_le; tauto | ].
destruct (Ps4 w x) as [wx [Pwx closewx]]; try tauto; exists wx; tauto.
Qed.

Hint Mode ProperFilter' - + : typeclass_instances.

(* TODO : move to coquelicot. *)
Lemma filter_prod_le {T : Type} (F G F' G' : (T -> Prop) -> Prop) :
  filter_le F F' -> filter_le G G' -> filter_le (filter_prod F G)
    (filter_prod F' G').
Proof.  now intros FF GG S [S1 S2 FS GS Imp]; exists S1 S2; auto. Qed.

Lemma is_RInt_gen_filter_le {T : NormedModule R_AbsRing}
  F G F' G' {FF : Filter F} {FG : Filter G}
  {FF' : Filter F'} {FG' : Filter G'} (f : R -> T) v :
  filter_le F' F -> filter_le G' G -> is_RInt_gen f F G v ->
  is_RInt_gen f F' G' v.
Proof.
intros lef leg intf P PP; unfold filtermapi.
now apply (filter_prod_le _ _ _ _ lef leg), intf.
Qed.

Lemma is_RInt_gen_comp {Fa Fb : (R -> Prop) -> Prop} {FFa : Filter Fa}
  {FFb : Filter Fb} (f : R -> R) (dg g : R -> R) l :
  filter_prod Fa Fb (fun p =>
      forall y, Rmin (fst p) (snd p) <= y <= Rmax (fst p) (snd p) ->
             continuous f (g y) /\
             is_derive g y (dg y) /\ continuous dg y) ->
  is_RInt_gen f (filtermap g Fa) (filtermap g Fb) l ->
  is_RInt_gen (fun x => scal (dg x) (f (g x))) Fa Fb l.
Proof.
intros dp intf P PP.
destruct dp as [S1 S2 FS1 FS2 dp].
destruct (intf P PP) as [S S' FS FS' fp1].
exists (fun x => S (g x) /\ S1 x) (fun x => S' (g x) /\ S2 x);
      try now apply filter_and; auto.
intros x y [sgx s1x] [sgy s2y]; simpl.
exists (RInt f (g x) (g y)); split.
  destruct (fp1 (g x) (g y)); try tauto.
  apply (is_RInt_comp f g dg).
     intros z zcond. 
     now destruct (dp x y s1x s2y z); auto.
  intros z zcond.
  now destruct (dp x y s1x s2y z); auto.
destruct (fp1 (g x) (g y) sgx sgy) as [v [isint Pv]]; simpl in isint.
now rewrite -> (is_RInt_unique _ _ _ _ isint).
Qed.

Lemma is_RInt_gen_equiv F G F' G' (f : R -> R) v:
  (forall s, F s <-> F' s) -> (forall s, G s <-> G' s) ->
  is_RInt_gen f F G v -> is_RInt_gen f F' G' v.
Proof.
intros eqF eqG intf P PP'; unfold filtermapi.
assert (tmp := filter_prod_le F' G' F G); unfold filter_le in tmp; apply tmp.
    now intros A; rewrite eqF.
  now intros A; rewrite eqG.
now apply (intf P PP').
Qed.

Lemma ex_RInt_gen_unique
  (F G : (R -> Prop) -> Prop) {FF : ProperFilter F}
  {FG : ProperFilter G} (f : R -> R) :
  ex_RInt_gen f F G -> exists ! v, is_RInt_gen f F G v.
Proof.
intros [v Pv]; exists (RInt_gen f F G); unfold unique.
rewrite -> (is_RInt_gen_unique _ _ Pv) at 1; split;[assumption | ].
now intros v' Pv'; rewrite -> (is_RInt_gen_unique _ _ Pv').
Qed.

(* extensions to improper integral package *)


Lemma is_RInt_gen_Rle0 (g : R -> R) gl F G
  {PF : ProperFilter F} {PG : ProperFilter G} :
  filter_Rlt F G ->
  is_RInt_gen g F G gl ->
  filter_prod F G
    (fun p => (forall x, fst p < x < snd p -> 0 <= g x)) ->
    0 <= gl.
Proof.
  intros.
  apply is_RInt_gen_Rle with (g := g) (f := fun _ => 0) (F := F) (G := G).
  trivial.
  trivial.
  trivial.
  trivial.
  apply (is_RInt_gen_ext (Derive (fun _ => 0))).
  apply filter_forall.
  intros.
  apply Derive_const.
  replace (0) with (0 - 0) at 1.
  apply is_RInt_gen_Derive.
  apply filter_forall.
  intros.
  apply ex_derive_const.
  apply filter_forall.
  intros.
  apply (continuous_ext (fun _ => 0)).
  intros.
  symmetry.
  apply Derive_const.
  apply continuous_const.
  apply filterlim_const.
  apply filterlim_const.
  lra.
  trivial.
Qed.

Lemma RInt_gen_Rle0 (g : R -> R) F G
  {PF : ProperFilter F} {PG : ProperFilter G} :
  filter_Rlt F G ->
  ex_RInt_gen g F G ->
  filter_prod F G
    (fun p => (forall x, fst p < x < snd p -> 0 <= g x)) ->
    0 <= RInt_gen g F G.
Proof.
  intros.
  unfold ex_RInt_gen in H0.
  destruct H0.
  replace (RInt_gen g F G) with (x).
  apply is_RInt_gen_Rle0 with (g := g) (F := F) (G := G).
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  symmetry.
  apply is_RInt_gen_unique.
  trivial.
Qed.  

Lemma RInt_gen_comp {Fa Fb : (R -> Prop) -> Prop} {FFa : ProperFilter' Fa}
  {FFb : ProperFilter' Fb} (f : R -> R) (dg g : R -> R) :
  filter_prod Fa Fb (fun p =>
      forall y, Rmin (fst p) (snd p) <= y <= Rmax (fst p) (snd p) ->
             continuous f (g y) /\
             is_derive g y (dg y) /\ continuous dg y) ->
  ex_RInt_gen f (filtermap g Fa) (filtermap g Fb) ->
  RInt_gen f (filtermap g Fa) (filtermap g Fb) =
  RInt_gen (fun x => scal (dg x) (f (g x))) Fa Fb.
Proof.
  intros.
  destruct H0 as [l lpf].
  generalize (is_RInt_gen_comp f dg g l H lpf); intros HH.
  apply (@is_RInt_gen_unique) in HH
  ; trivial.
  apply (@is_RInt_gen_unique) in lpf
  ; trivial.
  congruence.
  now apply filtermap_proper_filter'.
  now apply filtermap_proper_filter'.
Qed.

Lemma RInt_gen_scal {Fa Fb : (R -> Prop) -> Prop}
  {FFa : ProperFilter' Fa} {FFb : ProperFilter' Fb} (f : R -> R) (k : R) :
  ex_RInt_gen f Fa Fb ->
  RInt_gen (fun y => scal k (f y)) Fa Fb  = scal k (RInt_gen f Fa Fb).
Proof.
  intros.
  apply (@is_RInt_gen_unique).
  easy.
  easy.
  apply (@is_RInt_gen_scal).
  apply filter_filter'.
  apply filter_filter'.  
  now apply RInt_gen_correct.
Qed.

Section integrals_over_V.
  
Context {V : NormedModule R_AbsRing}.

Lemma ex_RInt_gen_Chasles {Fa Fc : (R -> Prop) -> Prop}
  {FFa : Filter Fa} {FFc : Filter Fc}
  (f : R -> V) (b : R) :
  ex_RInt_gen f Fa (at_point b) -> ex_RInt_gen f (at_point b) Fc
  -> ex_RInt_gen f Fa Fc .
Proof.
  intros [l1 H1] [l2 H2].
  exists (plus l1 l2).  
  by apply is_RInt_gen_Chasles with b.
Qed.

End integrals_over_V.
