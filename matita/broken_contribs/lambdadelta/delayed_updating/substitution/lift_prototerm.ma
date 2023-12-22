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

include "delayed_updating/substitution/lift_path.ma".
include "delayed_updating/syntax/prototerm.ma".
include "ground/lib/subset_ext.ma".

(* LIFT FOR PROTOTERM *******************************************************)

interpretation
  "lift (prototerm)"
  'UpTriangleArrow f t = (subset_ext_f1 ? ? (lift_path f) t).

(* Basic constructions ******************************************************)

lemma in_comp_lift_bi (f) (t) (p):
      p ϵ t → 🠡[f]p ϵ 🠡[f]t.
/2 width=1 by subset_in_ext_f1_dx/
qed.

(* Basic inversions *********************************************************)

lemma in_comp_inv_lift_bi (f) (t) (p):
      (🠡[f]p) ϵ 🠡[f]t → p ϵ t.
/3 width=4 by lift_path_inj, subset_in_inv_ext_f1_dx/
qed-.

(* Constructions with term_slice ********************************************)

lemma in_comp_slice_lift_bi (f) (p) (r):
      r ϵ ↑p → 🠡[f]r ϵ ↑🠡[f]p.
#f #p #r * #q #H0 destruct //
qed.

(* Iinversions with term_slice **********************************************)

lemma in_comp_slice_lift_inv_bi (f) (p) (r):
      (🠡[f]r) ϵ ↑🠡[f]p → r ϵ ↑p.
#f #p #r * #q #_ #H0
elim (eq_inv_lift_path_append … H0) -H0 #s1 #s2 #Hs1 #_ #H0 destruct
lapply (lift_path_inj … Hs1) -Hs1 #H0 destruct //
qed-.
