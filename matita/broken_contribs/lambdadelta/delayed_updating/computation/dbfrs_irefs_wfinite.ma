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

include "delayed_updating/reduction/dbfr_irefs_wfinite.ma".
include "delayed_updating/computation/dbfrs.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

(* Inversions with pirc and subsets_wfinite *********************************)

lemma dbfrs_pirc_wfinite_sn (t1) (t2) (rs):
      (𝐈❨t1❩) ϵ 𝐖𝛀 → t1 ➡*𝐝𝐛𝐟[rs] t2 →  𝐈❨t2❩ ϵ 𝐖𝛀.
#t1 #t2 #rs #Ht1 #H0
@(dbfrs_ind_dx … H0) -t2 -rs //
[ #t0 #t2 #_ * #Ht02 #_ #Ht2 -t1
  /3 width=3 by subset_le_pirc_bi, subsets_wfinite_le_trans/
| #t0 #t2 #rs #r #_ #Ht02 #Ht0 -t1 -rs
  /2 width=4 by dbfr_pirc_wfinite_sn/
]
qed-.
