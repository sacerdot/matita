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

include "delayed_updating/reduction/prototerm_normal.ma".
include "delayed_updating/computation/dbf_steps.ma".
include "delayed_updating/notation/functions/subset_wn_0.ma".

(* WEAK NORMALIZATION FOR PROTOTERM *****************************************)

definition twn: 𝒫❨𝕋❩ ≝
           {t1 | ∃∃t2,rs. t1 ➡*𝐝𝐛𝐟[rs] t2 & t2 ϵ 𝐍𝐅}
.

interpretation
  "weak normalization (prototerm)"
  'SubsetWN = (twn).

(* Basic properties *********************************************************)

lemma twn_mk (t1) (t2) (rs):
      t1 ➡*𝐝𝐛𝐟[rs] t2 → t2 ϵ 𝐍𝐅 → t1 ϵ 𝐖𝐍.
/2 width=4 by ex2_2_intro/
qed.

lemma term_normal_wn (t):
      t ϵ 𝐍𝐅 → t ϵ 𝐖𝐍.
/3 width=4 by frs_refl, twn_mk/
qed.

lemma dbfss_twn_trans (t1) (t2) (rs):
      t1 ➡*𝐝𝐛𝐟[rs] t2 → t2 ϵ 𝐖𝐍 → t1 ϵ 𝐖𝐍.
#t1 #t #rs #Ht1 * #t2 #ss #Ht2
/3 width=7 by frs_trans, twn_mk/
qed.

(* Advanced properties ******************************************************)

lemma dbfs_twn_trans (t1) (t2) (r):
      t1 ➡𝐝𝐛𝐟[r] t2 → t2 ϵ 𝐖𝐍 → t1 ϵ 𝐖𝐍.
#t1 #t #r #Ht1 * #t2 #ss #Ht2
/3 width=7 by frs_step_sn, twn_mk/
qed.
