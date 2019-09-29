(* from improper_integrals coq library *)
Require Import Reals Coquelicot.Coquelicot.

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

