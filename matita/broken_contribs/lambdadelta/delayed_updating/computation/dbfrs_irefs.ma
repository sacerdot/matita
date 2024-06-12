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

include "delayed_updating/reduction/dbfr_irefs.ma".
include "delayed_updating/computation/dbfrs_preterm.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

(* Destructions with pirc ***************************************************)

lemma dbfrs_des_le_pirc_bi (t1) (t2) (rs):
      t1 ϵ 𝐓 → t1 ➡*𝐝𝐛𝐟[rs] t2 → 𝐈❨t1❩ ⊆ 𝐈❨t2❩.
#t1 #t2 #r #Ht1 #H0
@(dbfrs_ind_dx … H0) -t2 -r //
[ #u1 #u2 #_ * #_ #Hu #Hu2
  /3 width=3 by subset_le_pirc_bi, subset_le_trans/
| #t #t2 #rs #r #Ht1 #Ht2 #IH
  @(subset_le_trans … IH) -IH
  /3 width=5 by dbfrs_preterm_trans, dbfr_des_le_pirc_bi/
]
qed-.
