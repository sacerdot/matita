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

include "delayed_updating/syntax/prototerm_origin.ma".
include "delayed_updating/computation/dbfrs.ma".
include "delayed_updating/notation/functions/subset_o_plus_0.ma".

(* SUBSET OF ORIGINATED PROTOTERMS ******************************************)

definition topc: 𝒫❨𝕋❩ ≝
           {t2 | ∃∃t1,rs. t1 ϵ 𝐎 & t1 ➡*𝐝𝐛𝐟[rs] t2}
.

interpretation
  "originated (subset of prototerms)"
  'SubsetOPlus = (topc).

(* Basic properties *********************************************************)

lemma topc_mk (t1) (t2) (rs):
      t1 ϵ 𝐎 → t1 ➡*𝐝𝐛𝐟[rs] t2 → t2 ϵ 𝐎⁺.
/2 width=4 by ex2_2_intro/
qed.

lemma toc_topc (t):
      t ϵ 𝐎 → t ϵ 𝐎⁺.
/3 width=4 by frs_refl, topc_mk/
qed.

lemma topc_dbfrs_trans (t1) (t2) (r):
      t1 ϵ 𝐎⁺ → t1 ➡*𝐝𝐛𝐟[r] t2 → t2 ϵ 𝐎⁺.
#t #t2 #ss * #t1 #rs #Ht1 #Ht #Ht2
/3 width=7 by frs_trans, topc_mk/
qed.

(* Advanced properties ******************************************************)

lemma toc_dbfr_trans (t1) (t2) (r):
      t1 ϵ 𝐎⁺ → t1 ➡𝐝𝐛𝐟[r] t2 → t2 ϵ 𝐎⁺.
#t #t2 #s * #t1 #rs #Ht1 #Ht #Ht2
/3 width=7 by frs_step_dx, topc_mk/
qed.
