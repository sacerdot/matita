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

include "ground/lib/list_length_rcons.ma".
include "ground/lib/list_weight_2.ma".

(* BINARY WEIGHT FOR LISTS **************************************************)

(* Constructions with list_rcons ********************************************)

lemma list_weight_2_rcons_sx (A) (B) (l1) (l2) (a):
      (⁤↑(list_weight_2 … l1 l2)) = list_weight_2 A B (l1⨭a) l2.
#A #B #l1 #l2 #a1
<list_weight_2_unfold <list_weight_2_unfold //
qed.

lemma list_weight_2_rcons_dx (A) (B) (l1) (l2) (a):
      (⁤↑(list_weight_2 … l1 l2)) = list_weight_2 A B l1 (l2⨭a).
#A #B #l1 #l2 #a1
<list_weight_2_unfold <list_weight_2_unfold //
qed.
