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

include "delayed_updating/reduction/dbf_step_irefs_wfinite.ma".
include "delayed_updating/computation/dbf_steps.ma".

(* DELAYED BALANCED FOCUSED COMPUTATION *************************************)

(* Inversions with pir and subsets_wfinite **********************************)

lemma dbfss_clear_pir_wfinite_sx (t1) (t2) (rs):
      (⓪𝐈❨t1❩) ϵ 𝐖𝛀 → t1 ➡*𝐝𝐛𝐟[rs] t2 →  ⓪𝐈❨t2❩ ϵ 𝐖𝛀.
#t1 #t2 #rs #Ht1 #H0
@(dbfss_ind_dx … H0) -t2 -rs //
[ #t0 #t2 #_ * #Ht02 #_ #Ht2 -t1
  /4 width=3 by subset_le_pir_bi, clear_le_repl, subsets_wfinite_le_trans/
| #t0 #t2 #rs #r #_ #Ht02 #Ht0 -t1 -rs
  /2 width=4 by dbfs_clear_pir_wfinite_sx/
]
qed-.
