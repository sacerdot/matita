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

(* Note: residuals of u with resprct to r ϵ 𝐑❨t❩ *)
definition term_dbfr (t) (r) (u): 𝒫❨ℙ❩ ≝
           {y | ∃∃s. s ϵ u & y ϵ s /𝐝𝐛𝐟{t} r}.

interpretation
  "residuals of a subset of dbf-redex pointers (subset of paths)"
  'SlashDBF t u r = (term_dbfr t r u).

(* Basic inversions *********************************************************)

lemma term_dbfr_inv_refl_dx (t) (u) (r):
      r ⧸ϵ (u /𝐝𝐛𝐟{t} r).
#t #u #r * #s #_ #H0
/2 width=4 by path_dbfr_inv_refl_dx/
qed-.
