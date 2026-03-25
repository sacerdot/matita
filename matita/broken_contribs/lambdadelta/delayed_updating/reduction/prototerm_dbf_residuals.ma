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

include "delayed_updating/reduction/path_dbf_residuals.ma".

(* RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ******************************)

(* Note: residuals of u with respect to r *)
definition term_dbfr (r) (u): 𝒫❨ℙ❩ ≝
           {y | ∃∃s. s ϵ u & y ϵ s /𝐝𝐛𝐟 r}.

interpretation
  "residuals of a subset of dbf-redex pointers (subset of paths)"
  'SlashDBF u r = (term_dbfr r u).

(* Basic inversions *********************************************************)

lemma term_dbfr_inv_refl_dx (u) (r):
      r ⧸ϵ (u /𝐝𝐛𝐟 r).
#u #r * #s #_ #H0
/2 width=3 by path_dbfr_inv_refl_dx/
qed-.
