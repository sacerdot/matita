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

include "delayed_updating/syntax/prototerm.ma".
include "delayed_updating/syntax/path_structure.ma".
include "ground/lib/subset_ext.ma".

(* STRUCTURE FOR PROTOTERM **************************************************)

interpretation
  "structure (prototerm)"
  'CircledTimes t = (subset_ext_f1 ?? structure t).

(* Basic constructions ******************************************************)

lemma in_comp_structure_bi (t) (p):
      p ϵ t → ⊗p ϵ ⊗t.
/2 width=1 by subset_in_ext_f1_dx/
qed.

(* Basic inversions *********************************************************)

lemma term_in_comp_structure_grafted_inv_d_dx (t) (p) (q) (k):
      q ϵ ⋔[p◖𝗱k]⊗t → ⊥.
#t #p #q #k * #r #_ #H0 -t
elim (eq_inv_append_structure … (sym_eq … H0)) -H0 #s1 #s2 #H0 #_ #_ 
elim (eq_inv_d_dx_structure … H0)
qed-.

lemma term_in_root_structure_inv_d_dx (t) (p) (k):
      p◖𝗱k ϵ ▵⊗t → ⊥.
#t #p #k * #q #H0
elim (term_in_comp_structure_grafted_inv_d_dx … H0)
qed-.
