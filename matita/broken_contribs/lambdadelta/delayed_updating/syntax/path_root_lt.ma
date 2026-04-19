
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

include "delayed_updating/syntax/path_proper.ma".
include "delayed_updating/notation/relations/sqsubset_2.ma".
include "delayed_updating/notation/relations/neg_sqsubset_2.ma".

(* STRICT ROOT ORDER FOR PATH ***********************************************)

definition path_rlt: relation2 (ℙ) (ℙ) ≝
           λp1,p2. ∃∃q. q ϵ 𝐏 & p2 = p1●q
.

interpretation
  "strict root order (path)"
  'SqSubset p1 p2 = (path_rlt p1 p2).

interpretation
  "negated strict root order (path)"
  'NegSqSubset p1 p2 = (negation (path_rlt p1 p2)).

(* Basic constructions ******************************************************)

lemma path_rlt_mk (p1) (p2) (q):
      q ϵ 𝐏 → p2 = p1●q → p1 ⊏ p2.
/2 width=3 by ex2_intro/
qed.

(* Main constructions *******************************************************)

theorem path_rlt_trans:
        Transitive … path_rlt.
#p1 #p0 * #q1 #Hq1 #H1 #p2 * #q2 #_ #H2 destruct
/3 width=4 by path_rlt_mk, in_comp_ppc_append_sx/
qed.

(* Advanced inversions ******************************************************)

lemma path_rlt_antirefl (p):
      p ⧸⊏ p.
#p * #x #Hx #H0
lapply (eq_inv_list_append_dx_dx_refl … H0) -H0 #H0 destruct
/2 width=1 by ppc_inv_empty/
qed-.

lemma path_rlt_antisym (p1) (p2):
      p1 ⊏ p2 → p2 ⊏ p1 → ⊥.
/3 width=4 by path_rlt_antirefl, path_rlt_trans/
qed-.
