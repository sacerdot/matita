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

include "delayed_updating/reduction/dbf_step_irefs.ma".
include "delayed_updating/computation/dbf_steps_preterm.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

(* Destructions with pirc ***************************************************)

lemma dbfss_des_le_clear_pir_bi (t1) (t2) (rs):
      t1 ϵ 𝐓 → t1 ➡*𝐝𝐛𝐟[rs] t2 → ⓪𝐈❨t1❩ ⊆ ⓪𝐈❨t2❩.
#t1 #t2 #r #Ht1 #H0
@(dbfss_ind_dx … H0) -t2 -r //
[ #u1 #u2 #_ * #_ #Hu #Hu2
  @(subset_le_trans … Hu2) -t1
  /3 width=3 by subset_le_pir_bi, clear_le_repl/
| #t #t2 #rs #r #Ht1 #Ht2 #IH
  @(subset_le_trans … IH) -IH
  /3 width=5 by dbfss_preterm_trans, dbfs_des_le_clear_pir_bi/
]
qed-.
