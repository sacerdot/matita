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

include "delayed_updating/substitution/lift_prototerm_eq.ma".
include "delayed_updating/substitution/lift_path_id.ma".

(* LIFT FOR PROTOTERM *******************************************************)

(* Constructions with tr_id *************************************************)

lemma lift_term_id_sn (t):
      t ⊆ 🠡[𝐢]t.
#t #p #Hp
>(lift_path_id p)
/2 width=1 by in_comp_lift_path_term/
qed-.

lemma lift_term_id_dx (t):
      🠡[𝐢]t ⊆ t.
#t #p * #q #Hq #H destruct //
qed-.

lemma lift_term_id (t):
      t ⇔ 🠡[𝐢]t.
/3 width=2 by lift_term_id_dx, lift_term_id_sn, conj/
qed.
