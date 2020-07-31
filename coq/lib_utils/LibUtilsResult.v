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

Require Import List.

Section Result.
  Section definition.
    Context (A: Type). (**r Type of success *)
    Context (E: Type). (**r Type of failure *)

    Inductive Result : Type :=
    | Success : A -> Result
    | Failure : E -> Result.
  End definition.

  Section operations.
    Definition lift_failure {A B E:Type} (f:A -> Result B E) : (Result A E -> Result B E) :=
      fun r =>
        match r with
        | Success _ _ a => f a
        | Failure _ _ e => Failure _ _ e
        end.

    Definition lift_failure_in {A B E:Type} (f: A -> B) : (Result A E -> Result B E) :=
        fun r =>
          lift_failure (fun a :A  => Success _ _ (f a)) r.

    Definition raise_failure {A B E:Type} (f:A -> B) (e:E) : (Result A E -> Result B E) :=
      fun r =>
        Failure _ _ e.

    Definition lift_failure_in_two {A B C E:Type} (f:A -> B -> C)
      : (Result A E -> Result B E -> Result C E) :=
      fun a =>
        match a with
        | Failure _ _ e => fun b => Failure _ _ e
        | Success _ _ a =>
          (fun b =>
             match b with
             | Failure _ _ e => Failure _ _ e
             | Success _ _ b =>
               Success _ _ (f a b)
             end)
        end.
    
    Definition lift_failure_in_three {A B C D E:Type} (f:A -> B -> C -> D)
      : (Result A E -> Result B E -> Result C E -> Result D E) :=
      fun a =>
        match a with
        | Failure _ _ e => fun b => fun c => Failure _ _ e
        | Success _ _ a =>
          (fun b =>
             match b with
             | Failure _ _ e => fun c => Failure _ _ e
             | Success _ _ b =>
               (fun c =>
                  match c with
                  | Failure _ _ e => Failure _ _ e
                  | Success _ _ c  =>
                    Success _ _ (f a b c)
                  end)
             end)
        end.
    
    Definition lift_failure_map {A B E:Type} (f: A -> Result B E) (al:list A) : Result (list B) E :=
      let init_bl := Success _ _ nil in
      let proc_one (a:A) (acc:Result (list B) E) : Result (list B) E :=
          lift_failure_in_two
            cons
            (f a)
            acc
      in
      fold_right proc_one init_bl al.

    Definition result_of_option {A E:Type} (a:option A) (e:E) : Result A E :=
      match a with
      | Some a => Success _ _ a
      | None => Failure _ _ e
      end.

    Definition option_of_result {A E:Type} (r:Result A E) : option A :=
      match r with
      | Failure _ _ _ => None
      | Success _ _ a => Some a
      end.
    
  End operations.
End Result.

