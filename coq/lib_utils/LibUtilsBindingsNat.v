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

(** This module provides support for bindings where the key is a
natural number. *)

Require Import Arith.
Require Import NPeano.
Require Import LibUtilsBindings.

Section BindingsNat.
    
  Global Program Instance ODT_nat : (@ODT nat)
    := mkODT _ _ lt Nat.lt_strorder lt_dec Nat.compare _.
  Next Obligation.
    simpl.
    apply Nat.compare_spec.
  Qed.

End BindingsNat.

Hint Unfold rec_sort rec_concat_sort : fml.
Hint Resolve drec_sort_sorted drec_concat_sort_sorted : fml.
Hint Resolve is_list_sorted_NoDup_strlt : fml.

