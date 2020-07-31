(*
 * Copyright 2015-2016 IBM Corporation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(** This module contains additional definitions and lemmas on strings,
 including a total order relation. *)

Require Import Orders.
Require Import Ascii.
Require Import List.
Require Import String.
Require Import Arith.
Require Import Min.
Require Import Equivalence.
Require Import EquivDec.
Require Import Compare_dec.
Require Import Lia.
Require Import LibUtilsCoqLibAdd.

(** * Total order on characters *)

Module AsciiOrder <: OrderedTypeFull with Definition t:=ascii.
  Definition t:= ascii.
  Definition eq := @eq t.
  Definition eq_equiv : (Equivalence eq) := eq_equivalence.
  Definition eq_dec := ascii_dec.

  (* This could be done more directly, but this suffices *)
  Definition compare (a b:ascii) : comparison :=
    Nat.compare (nat_of_ascii a) (nat_of_ascii b).

  Definition lt (a b:ascii) := compare a b = Lt.

  Lemma lt_strorder : StrictOrder lt.
  Proof.
    split; repeat red; unfold lt, compare; intros;
      repeat match goal with 
             | [H:Nat.compare _ _ = Lt |- _ ] => apply nat_compare_lt in H
             | [|- Nat.compare _ _ = Lt ] => apply nat_compare_lt
             end; lia.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful, eq; intros; subst; intuition.
  Qed.

  Lemma compare_eq_iff a b: compare a b = Eq <-> a = b.
  Proof.
    unfold AsciiOrder.compare.
    generalize (Nat.compare_eq_iff (nat_of_ascii a) (nat_of_ascii b)).
    destruct 1; split; intros; subst.
    - specialize (H H1).
      apply (f_equal ascii_of_nat) in H.
      repeat rewrite ascii_nat_embedding in H.
      trivial.
    - auto.
  Qed.

  Lemma compare_spec :
    forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros. unfold eq, lt, compare. 
    generalize (Nat.compare_spec (nat_of_ascii x) (nat_of_ascii y)); intros nc.
    inversion nc.
    - apply (f_equal ascii_of_nat) in H0.
      repeat rewrite ascii_nat_embedding in H0.
      subst. auto.
    - eauto.
    - constructor.
      apply nat_compare_lt. trivial.
  Qed.

  Lemma trichotemy a b : {lt a b} + {eq a b} + {lt b a}.
  Proof.
    generalize (compare_spec a b); intros nc.
    destruct (compare a b);
      [left; right|left;left|right]; inversion nc; trivial.
  Defined.

  Definition le (a b:ascii) :=
    match compare a b with
    | Lt => True
    | Eq => True
    | Gt => False
    end.

  Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
  Proof.
    intros.
    generalize (compare_spec x y); inversion 1;
      unfold le, lt, eq in *;
      case_eq (compare x y); intuition congruence.
  Qed.

  Lemma compare_refl_eq a: compare a a = Eq.
  Proof.
    unfold AsciiOrder.compare.
    rewrite (Nat.compare_eq_iff (nat_of_ascii a) (nat_of_ascii a)); trivial.
  Qed.

End AsciiOrder.

(** * Total order on strings *)

Module StringOrder <: OrderedTypeFull with Definition t:=string.
  Definition t:= string.
  Definition eq := @eq t.
  Definition eq_equiv : (Equivalence eq) := eq_equivalence.
  Definition eq_dec := string_dec.

  Fixpoint compare (a:string) (b:string) : comparison :=
    match a, b with
    | EmptyString, EmptyString => Eq
    | EmptyString, String _ _ => Lt
    | String _ _, EmptyString => Gt
    | String a' a's, String b' b's => 
      match AsciiOrder.compare a' b' with
      | Lt => Lt
      | Eq => compare a's b's
      | Gt => Gt
      end
    end.

  Definition lt (a b:string) := compare a b = Lt.

  Lemma compare_spec :
    forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    unfold eq, lt. 
    induction x; destruct y; simpl in *; eauto.
    specialize (IHx y).
    case_eq (AsciiOrder.compare_spec a a0); intros.
    - unfold AsciiOrder.eq in *; subst.
      rewrite AsciiOrder.compare_refl_eq.
      inversion IHx; simpl; subst; eauto.
    - eauto.
    - unfold AsciiOrder.lt in *; rewrite l; eauto.
  Qed.

  Lemma trichotemy a b : {lt a b} + {eq a b} + {lt b a}.
  Proof.
    generalize (compare_spec a b); intros nc.
    destruct (compare a b);
      [left; right|left;left|right]; inversion nc; trivial.
  Defined.

  Lemma compare_refl_eq a: compare a a = Eq.
  Proof.
    induction a; simpl in *; eauto.
    rewrite AsciiOrder.compare_refl_eq; trivial.
  Qed.

  Lemma compare_eq_iff a b: compare a b = Eq <-> a = b.
  Proof.
    split; [| intros; subst; apply compare_refl_eq].
    revert b.
    induction a; destruct b; simpl in *; eauto; try congruence.
    generalize (AsciiOrder.compare_eq_iff a a1).
    intros. specialize (IHa b).
    destruct (AsciiOrder.compare a a1); intuition; congruence.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split; repeat red; unfold lt.
    - intros a H; rewrite compare_refl_eq in H. discriminate. 
    - induction x; destruct y; destruct z; simpl; eauto; try congruence.
      intros. specialize (IHx y z).
      generalize (@StrictOrder_Transitive _ _ (AsciiOrder.lt_strorder) a a0 a1).
      unfold AsciiOrder.lt. intros AC.
      case_eq (AsciiOrder.compare a a0); 
        intros re; rewrite re in *; try congruence;
          case_eq (AsciiOrder.compare a0 a1); 
          intros re2; rewrite re2 in *; try congruence;
            try rewrite AsciiOrder.compare_eq_iff in *; subst;
              try rewrite re in*; try rewrite re2 in *;
                try rewrite AC by trivial; 
                try rewrite AsciiOrder.compare_refl_eq; 
                auto.
  Qed.

  Lemma lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful, eq; intros; subst; intuition.
  Qed.

  Program Definition lt_dec (a b:string) : {lt a b} + {~lt a b}
    := match compare a b with
       | Lt => left _
       | Eq => right _
       | Gt => right _
       end.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    trivial.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    rewrite H0. apply irreflexivity.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    intro l2. apply (asymmetry H0 l2).
  Qed.

  Definition le (a b:string) :=
    match compare a b with
    | Lt => True
    | Eq => True
    | Gt => False
    end.

  Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
  Proof.
    intros.
    generalize (compare_spec x y); inversion 1;
      unfold le, lt, eq in *;
      case_eq (compare x y); intuition congruence.
  Qed.

  Program Definition le_dec (a b:string) : {le a b} + {~le a b}
    := match compare a b with
       | Lt => left _
       | Eq => left _
       | Gt => right _
       end.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    apply le_lteq.
    intuition.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    apply le_lteq.
    intuition.
  Qed.
  Next Obligation.
    generalize (compare_spec a b); rewrite <- Heq_anonymous; inversion 1.
    intro l2.
    apply le_lteq in l2.
    destruct l2.
    - apply (asymmetry H0 H1).
    - rewrite H1 in H0. apply (irreflexivity H0).
  Qed.

End StringOrder.

(** * String prefixes *)

Section Prefix.
  Lemma substring_zero s :
    substring 0 0 s = ""%string.
  Proof.
    induction s; reflexivity.
  Qed.
  
  Lemma substring_S a m s :
    substring 0 (S m) (String a s) = String a (substring 0 m s).
  Proof.
    reflexivity.
  Qed.

  Lemma append_string_distr a s1 s2 :
    (String a s1 ++ s2 = String a (s1 ++ s2))%string.
  Proof.
    auto.
  Qed.

  Lemma append_eq_inv1 x y z : append x y = append x z -> y = z.
  Proof.
    revert y z.
    induction x; simpl; trivial; intros.
    inversion H; subst.
    auto.
  Qed.

  Lemma prefix_refl y : prefix y y = true.
  Proof.
    induction y; simpl; trivial.
    match_destr; congruence.
  Qed.
  
  Lemma substring_append_cancel x y :
    substring (String.length x) (String.length y) (append x y) = y.
  Proof.
    revert y.
    induction x; simpl; intros.
    - apply prefix_correct. apply prefix_refl.
    - trivial.
  Qed.

  Lemma string_length_append x y :
    String.length (append x y) = String.length x + String.length y.
  Proof.
    revert y.
    induction x; simpl; auto.
  Qed.

  Lemma prefix_nil post : prefix ""%string post = true.
  Proof.
    destruct post; trivial.
  Qed.

  Lemma prefix_app pre post : prefix pre (append pre post) = true.
  Proof.
    revert post.
    induction pre; intros; simpl.
    - apply prefix_nil.
    - match_destr; intuition.
  Qed.

  Lemma prefix_break {pre x} :
    prefix pre x = true ->
    {y | x = append pre y}.
  Proof.
    revert x.
    induction pre; simpl.
    - eauto.
    - destruct x; simpl; try discriminate.
      match_destr.
      subst; intros p.
      destruct (IHpre _ p).
      subst.
      eauto.
  Qed.

  
  Lemma substring_split s n m l :
    append (substring s n l) (substring (s+n) m l) = substring s (n+m) l.
  Proof.
    revert n m s.
    induction l; simpl; destruct s; destruct n; simpl; trivial.
    - f_equal.
      apply IHl.
    - rewrite IHl; simpl; trivial.
    - rewrite IHl. simpl; trivial.
  Qed.

  Lemma substring_all l :
    substring 0 (String.length l) l = l.
  Proof.
    induction l; simpl; congruence.
  Qed.

  Lemma substring_bounded s n l :
    substring s n l = substring s (min n (String.length l - s)) l.
  Proof.
    revert s n.
    induction l; destruct s; destruct n; simpl; trivial.
    - rewrite IHl; simpl.
      f_equal.
      f_equal.
      f_equal.
      lia.
    - rewrite IHl.
      match_case.
  Qed.

  Lemma substring_le_prefix s n m l :
    n <= m ->
    prefix (substring s n l) (substring s m l) = true.
  Proof.
    revert s n m.
    induction l; destruct s; destruct n; destruct m; simpl; trivial;
      try lia; intuition.
    match_destr; intuition.
  Qed.

  Lemma substring_prefix n l :
    prefix (substring 0 n l) l = true.
  Proof.
    rewrite substring_bounded.
    rewrite <- (substring_all l) at 3.
    apply substring_le_prefix.
    replace (String.length l - 0) with (String.length l) by lia.
    apply le_min_r.
  Qed.

  Lemma in_of_append pre y l :
    In (append pre y) l <->
    In y (map
            (fun x => substring (String.length pre) (String.length x - String.length pre) x)
            (filter (prefix pre) l)).
  Proof.
    rewrite in_map_iff.
    split; intros.
    - exists (append pre y).
      rewrite string_length_append.
      replace ((String.length pre + String.length y - String.length pre))
        with (String.length y) by lia.
      rewrite substring_append_cancel.
      split; trivial.
      apply filter_In.
      split; trivial.
      apply prefix_app.
    - destruct H as [x [subx inx]]; subst.
      apply filter_In in inx.
      destruct inx as [inx prex].
      destruct (prefix_break prex).
      subst.
      rewrite string_length_append.
      replace ((String.length pre + String.length x0 - String.length pre))
        with (String.length x0) by lia.
      rewrite substring_append_cancel.
      trivial.
  Qed.
  
  Lemma append_ass s1 s2 s3 : ((s1 ++ s2) ++ s3 = s1 ++ s2 ++ s3)%string.
  Proof.
    revert s2 s3.
    induction s1; simpl.
    - trivial.
    - intros. rewrite IHs1; trivial.
  Qed.

End Prefix.

(** * Character map over strings *)

Section MapString.
  Fixpoint map_string (f:ascii->ascii) (s:string)
    := match s with
       | EmptyString => EmptyString
       | String a s' => String (f a) (map_string f s')
       end.

  Fixpoint flat_map_string (f:ascii->string) (s:string)
    := match s with
       | EmptyString => EmptyString
       | String a s' => append (f a) (flat_map_string f s')
       end.

  Global Instance ascii_dec : EqDec ascii eq
    := ascii_dec.
End MapString.

(** Support for 'like' on strings *)

Section Join.
  Definition map_concat {A} separator (f:A -> string) (elems:list A) : string :=
    match elems with
    | nil => ""
    | e :: elems' =>
      (fold_left (fun acc e => acc ++ separator ++ (f e)) elems' (f e))%string
    end.
  
End Join.

(** * Conversion between lists of characters and strings *)

Section AsciiToString.

  Fixpoint string_reverse_helper (s:string) (acc:string)
    := match s with
       | EmptyString => acc
       | String x xs => string_reverse_helper xs (String x acc)
       end.

  Definition string_reverse (s:string) := string_reverse_helper s EmptyString.

  Fixpoint string_to_list (s:string) : list ascii
    := match s with
       | EmptyString => nil
       | String x xs => cons x (string_to_list xs)
       end.

  Fixpoint list_to_string (l:list ascii) : string
    := match l with
       | nil => EmptyString
       | cons x xs => String x (list_to_string xs)
       end.
  
  Lemma string_to_list_to_string (s:string) :
    list_to_string (string_to_list s) = s.
  Proof.
    induction s; simpl; intuition congruence.
  Qed.

  Lemma list_to_string_to_list (l:list ascii) :
    string_to_list (list_to_string l) = l.
  Proof.
    induction l; simpl; intuition congruence.
  Qed.

  Lemma string_to_list_inj (x y:string) : 
    string_to_list x = string_to_list y -> x = y.
  Proof.
    intros.
    generalize (f_equal list_to_string H); intros fe.
    repeat rewrite  string_to_list_to_string in fe; trivial.
  Qed.

  Lemma list_to_string_inj (x y:list ascii) : 
    list_to_string x = list_to_string y -> x = y.
  Proof.
    intros.
    generalize (f_equal string_to_list H); intros fe.
    repeat rewrite  list_to_string_to_list in fe; trivial.
  Qed.

  Lemma string_reverse_helper_reverse_append s acc:
    string_reverse_helper s acc = list_to_string (List.rev_append (string_to_list s) (string_to_list acc)).
  Proof.
    revert acc.
    induction s; simpl; intros.
    - rewrite string_to_list_to_string; trivial.
    - rewrite IHs. simpl; auto.
  Qed.

  Lemma string_reverse_reverse s :
    string_reverse s = list_to_string (List.rev (string_to_list s)).
  Proof.
    rewrite List.rev_alt. apply string_reverse_helper_reverse_append.
  Qed.

  Lemma string_reverse_involutive x : string_reverse (string_reverse x) = x.
  Proof.
    repeat rewrite string_reverse_reverse.
    rewrite list_to_string_to_list, List.rev_involutive, string_to_list_to_string.
    trivial.
  Qed.

  Lemma string_reverse_inj x y :
    string_reverse x = string_reverse y -> 
    x = y.
  Proof.
    intros re.
    generalize (f_equal string_reverse re); intros fe.
    repeat rewrite string_reverse_involutive in fe; trivial.
  Qed.

  Lemma lt_contr1 s1 s2 :
    ~StringOrder.lt s1 s2 -> ~StringOrder.lt s2 s1 -> StringOrder.eq s1 s2.
  Proof.
    unfold not; intros.
    generalize (StringOrder.trichotemy s1 s2); intros.
    inversion H1.
    elim H2; intros.
    congruence.
    assumption.
    congruence.
  Qed.

  Lemma lt_contr2 s1 s2 :
    StringOrder.lt s1 s2 -> ~StringOrder.eq s1 s2.
  Proof.
    compare s1 s2.
    intros. rewrite e in *; clear e.
    unfold not; intros.
    apply asymmetry with (x := s2) (y := s2); assumption.
    intros. assumption.
    apply ascii_dec.
  Qed.

  Lemma lt_contr3 s :
    StringOrder.lt s s -> False.
  Proof.
    generalize (lt_contr2 s s); intros.
    unfold not in *.
    apply (H H0).
    reflexivity.
  Qed.

End AsciiToString.

Section Like.
  (* This is intended to be like the SQL like operation *)
  (*  Definition string_like (s:pattern) *)

  Inductive like_clause :=
  | like_literal (literal:string) : like_clause
  | like_any_char : like_clause
  | like_any_string : like_clause.

  Fixpoint make_like_clause (s:string) (escape:option ascii) {struct s}: list like_clause
    := match s with
       | EmptyString => nil
       | String "_"%char tail => like_any_char :: make_like_clause tail escape
       | String "%"%char tail => like_any_string :: make_like_clause tail escape
       | other =>
         (fix make_like_literal_clause (ss:string)  (acc:string) {struct ss} : list like_clause
          := match ss with
             | EmptyString => like_literal (string_reverse acc) :: nil
             | String "_"%char tail => like_literal (string_reverse acc) :: like_any_char :: make_like_clause tail escape
             | String "%"%char tail => like_literal (string_reverse acc) :: like_any_string :: make_like_clause tail escape
             | String h tail =>
               if Some h == escape
               then
                 match tail with
                 | EmptyString =>
                   (* unclear what to do with an escape character at the end of the string.  We will interpret it as a literal character *)
                   like_literal (string_reverse (String h acc)) :: nil
                 | String "_"%char tail => make_like_literal_clause tail (String "_" acc)
                 | String "%"%char tail => make_like_literal_clause tail (String "%" acc)
                 | String nh ntail =>
                   if Some nh == escape
                   then make_like_literal_clause ntail (String nh acc)
                   else
                     (* unclear what to do with an escape character that is invalid.  We will interpret it as a literal character *)
                     make_like_literal_clause ntail (String nh (String h acc))
                 end
               else
                 make_like_literal_clause tail (String h acc)
             end
         ) other ""%string
       end.

  Example make_like_clause_example1 := make_like_clause "hello_there^^^%%" None.
  Example make_like_clause_example2 := make_like_clause "hello_there^^^%%" (Some "^"%char).

  (*
  Eval vm_compute in make_like_clause_example1.
  Eval vm_compute in make_like_clause_example2.
   *)

  Fixpoint  string_exists_suffix (f:string->bool) (s:string) : bool
    := f s ||
         match s with
         | EmptyString => false
         | String _ tail => string_exists_suffix f tail
         end.

  (* something like bayer-moore would be much more efficient.
     This implementation is known to have very poor performance *)
  Fixpoint like_clause_matches_string (pat:list like_clause) (s:string)
    := match pat with
       | nil => s ==b EmptyString
       | (like_literal literal)::rest =>
         andb (prefix literal s)
              (like_clause_matches_string rest (substring (String.length literal) (String.length s - String.length literal) s))
       | like_any_char::rest =>
         match s with
         | EmptyString => false
         | String _ tail => like_clause_matches_string rest tail
         end
       | like_any_string::rest =>
         string_exists_suffix (like_clause_matches_string rest) s
       end.
  
  (* This is intended to be like the SQL like operation *)
  Definition string_like (str pattern:string) (escape:option ascii) : bool
    := let pat_clause := make_like_clause pattern escape in
       like_clause_matches_string pat_clause str.

  Example string_like_example1 := string_like "hello there" "hello there" None.
  Example string_like_example2 := string_like "hello there" "hello %there" None.
  Example string_like_example3 := string_like "hello there" "he%th_re" None.
  Example string_like_example4 := string_like "hello there " "he%th_re" None.
  Example string_like_example5 := string_like "hello thethare" "he%th_re" None.
  Example string_like_example6 := string_like "hello thetheare" "he%th_re" None.

(*
  Eval vm_compute in string_like_example1.
  Eval vm_compute in string_like_example2.
  Eval vm_compute in string_like_example3.
  Eval vm_compute in string_like_example4.
  Eval vm_compute in string_like_example5.
  Eval vm_compute in string_like_example6.
 *)
  
End Like.

