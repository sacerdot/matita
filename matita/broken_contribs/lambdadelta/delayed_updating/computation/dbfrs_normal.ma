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

include "delayed_updating/reduction/dbfr_normal.ma".
include "delayed_updating/computation/dbfrs.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

(* Destructionss with tnf ***************************************************)

lemma dbfrs_des_tnf_sn (t1) (t2) (rs):
      t1 ϵ 𝐍𝐅 → t1 ➡*𝐝𝐛𝐟[rs] t2 → t1 ⇔ t2.
#t1 #t2 #rs #Ht1 #Ht
@(dbfrs_ind_dx … Ht) -t2 -rs //
[ #t #t2 #_ #Ht2 #Ht12
  /2 width=3 by subset_eq_canc_dx/
| #t #t2 #rs #r #_ #Ht2 #Ht1 -rs
  lapply (eq_dbfr_trans … Ht1 Ht2) -t #Ht12
  elim (dbfr_inv_tnf_sn …Ht12) -t2 -r //
]
qed-.
