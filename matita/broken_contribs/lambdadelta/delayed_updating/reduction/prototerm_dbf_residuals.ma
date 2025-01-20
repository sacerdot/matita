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

include "ground/subsets/subset_le.ma".
include "delayed_updating/reduction/path_dbf_residuals.ma".

(* RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ******************************)

definition term_dbfr (t) (r) (u): 𝒫❨ℙ❩ ≝
           {s | ∃∃x. x ϵ u & s ϵ x /𝐝𝐛𝐟{t} r}.

interpretation
  "residuals of a subset of dbf-redex pointers (subset of paths)"
  'SlashDBF t u r = (term_dbfr t r u).

(* Basic constructions ******************************************************)

lemma term_dbfr_mk (t) (u) (s) (r):
      s ϵ u → (s /𝐝𝐛𝐟{t} r) ⊆ (u /𝐝𝐛𝐟{t} r).
/2 width=3 by ex2_intro/
qed.

lemma term_dbfr_nin (t) (u) (r):
      r ⧸ϵ u  → u ⊆ u /𝐝𝐛𝐟{t} r.
#t #u #r #Hr #s #Hs
/4 width=3 by term_dbfr_mk, path_dbfr_neq/
qed.

lemma term_dbfr_refl (u) (r):
      (❴r❵ /𝐝𝐛𝐟{u} r) ⊆ Ⓕ.
#u #r #s * #x #Hx #Hs
lapply (subset_in_inv_single ??? Hx) -Hx #H0 destruct
elim (path_dbfr_inv_refl … Hs)
qed.

(* Basic inversions *********************************************************)

lemma term_dbfr_inv_refl_dx (t) (u) (r):
      r ⧸ϵ (u /𝐝𝐛𝐟{t} r).
#t #u #r * #s #_ #H0
/2 width=4 by path_dbfr_inv_refl_dx/
qed-.
