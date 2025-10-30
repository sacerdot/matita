(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/arith/nat_plus.ma".
include "ground/lib/list_length.ma".

(* BINARY WEIGHT FOR LISTS **************************************************)

definition list_weight_2 (A) (B) (l1) (l2): ℕ ≝
  ❘l1❘{A}+❘l2❘{B}.

(* Basic constructions ******************************************************)

lemma list_weight_2_unfold (A) (B) (l1) (l2):
      ❘l1❘+❘l2❘ = list_weight_2 A B l1 l2.
// qed-.

lemma list_weight_2_lcons_sx (A) (B) (l1) (l2) (a):
      (⁤↑(list_weight_2 … l1 l2)) = list_weight_2 A B (a⨮l1) l2.
#A #B #l1 #l2 #a1
<list_weight_2_unfold <list_weight_2_unfold //
qed.

lemma list_weight_2_lcons_dx (A) (B) (l1) (l2) (a):
      (⁤↑(list_weight_2 … l1 l2)) = list_weight_2 A B l1 (a⨮l2).
#A #B #l1 #l2 #a1
<list_weight_2_unfold <list_weight_2_unfold //
qed.
