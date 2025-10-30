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

include "delayed_updating/unwind/unwind2_prototerm.ma".
include "delayed_updating/syntax/preterm_structure.ma".
include "ground/subsets/subset_or_le.ma".
include "ground/subsets/subset_ol.ma".

(* TAILED UNWIND FOR PRETERM ************************************************)

(* Inversions with subset_ol ************************************************)

lemma term_ol_inv_unwind_bi (f) (t1) (t2):
      t1 ∪ t2 ϵ 𝐓 →
      (▼[f]t1) ≬ ▼[f]t2 → t1 ≬ t2.
#f #t1 #t2 #Ht * #r * #s1 #Hs1 #H1 * #s2 #Hs2 #H2 destruct
lapply (eq_des_unwind2_path_bi_structure … H2) -H2 #H2
lapply (term_structure_inj … Ht … H2) -H2 [3: #H0 destruct ]
/2 width=3 by subset_or_in_dx, subset_or_in_sx, subset_ol_i/
qed-.
