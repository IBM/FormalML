Require Import Reals Coquelicot.Coquelicot Sums.
Require Import Reals Fourier FunctionalExtensionality Psatz.
Require Import Coq.Logic.ProofIrrelevance Coq.Bool.Bool.
Require Import Setoid Program.
Require Import Paco.paco.
Require Import Reals Fourier FunctionalExtensionality Psatz.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype finset finfun bigop.

(* Joe's ldist. Renamed to Pmf. *)


Record Pmf (A: Type) := mkPmf {
  outcomes :> list (R * A);
  nonneg : all  (fun r => Rle_dec 0 r) [seq r.1 | r <- outcomes];
  sum1 : \big[Rplus/0]_(a <- map fst outcomes) a = R1
 }.

 Arguments outcomes {_}.
 Arguments sum1 {_}.
 Arguments mkPmf {_}.
 

Lemma Pmf_ext  (A : Type) (p q : Pmf A)  : outcomes p = outcomes q -> p = q.
Proof.
destruct p as [op  np sp].
destruct q as [oq  nq sq]. rewrite /outcomes => ?.
subst. f_equal. apply bool_irrelevance. apply proof_irrelevance.
Qed.

(*Definition Pmf_support A (p : Pmf A) : list A := filter (fun x => _) _. *)

Lemma pure_nonneg {A} (a : A) : is_true (all (fun r : R => Rle_dec 0 r) [seq r.1 | r <- [:: (R1, a)]]).
Proof.
simpl.
rewrite andb_true_r.
destruct Rle_dec => //=. nra.
Qed.

Lemma pure_sum1 {A} (a : A) : \big[Rplus/0]_(a <- [seq i.1 | i <- [:: (R1, a)]]) a = R1. 
Proof.
  simpl. rewrite big_cons. rewrite big_nil. nra.
Qed.


Definition Pmf_pure A (a : A) : Pmf A := {|
outcomes := [:: (R1,a)];
nonneg :=  pure_nonneg a;
sum1 := pure_sum1 a
|}.

Definition dist_bind_aux :=
  fun {A B} (f: A -> Pmf B) =>
  fix go (l: seq (R * A)) :=
    match l with
      [::] => [::]
    | (r, x) :: l => map (fun py => (r * py.1, py.2)%R) (f x) ++ go l
    end.

Check dist_bind_aux.
Check allP.

Lemma dist_bind_pf1 {A B} (f: A -> Pmf B) d:
  all [eta (Rle_dec 0)] [seq r.1 | r <- dist_bind_aux f (outcomes d)].
Proof.
  Admitted.

  
Definition Pmf_bind {A B} (p : Pmf A) (f : A -> Pmf B) : Pmf B := {|
  outcomes := dist_bind_aux f p.(outcomes);
  nonneg := dist_bind_pf1 f p;
  sum1 := _
  |}.
