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

include "ground/subsets/subsets_wfinite_lt.ma".
include "delayed_updating/computation/dbf_steps_normal.ma".
include "delayed_updating/computation/dbf_steps_irefs.ma".
include "delayed_updating/computation/dbf_steps_irefs_wfinite.ma".
include "delayed_updating/computation/dbf_steps_confluence.ma".
include "delayed_updating/computation/prototerm_wn.ma".
include "delayed_updating/computation/prototerm_sn.ma".

(* STRONG NORMALIZATION FOR PRETERM *****************************************)

(* Constructions with twn ***************************************************)

lemma wfinite_clear_pir_twn_tsn_aux (t1):
      t1 ϵ 𝐍𝐅 → ∀u0. u0 ϵ 𝐖𝛀 →
      ∀t0,rs. t0 ➡*𝐝𝐛𝐟[rs] t1 → t0 ϵ 𝐓 →  ⓪𝐈❨t1❩ ⧵ ⓪𝐈❨t0❩ ⊆ u0 →
      t0 ϵ 𝐒𝐍.
#t1 #Ht1 @(subsets_wfinite_ind_lt … eq_path_dec)
#u0 #_ #IH #t0 #rs #Ht01 #Ht0 #Hu0
@tsn_step #t2 #r #Ht02
elim (dbfss_conf … Ht0 … Ht01 … t2) -rs
[2,3: /2 width=2 by frs_step/ ] #t #ss1 #ss2 #Hs1 #Hs2
lapply (dbfss_des_tnf_sx … Hs1) // -ss1 #Hs1
lapply (dbfss_eq_canc_dx … Hs2 … Hs1) -t #H1t21
lapply (dbfs_des_lt_clear_pir_bi … Ht02) //
lapply (dbfs_preterm_trans … Ht02) // -r -Ht0 #Ht2 #Ht02
lapply (dbfss_des_le_clear_pir_bi … H1t21) // #H2t21
@(IH (⓪𝐈❨t1❩⧵⓪𝐈❨t2❩) … H1t21) [2,3: // ] -ss2 -IH -Ht1 -Ht2
@(subset_lt_le_trans … Hu0) -u0
@subset_lt_nimp_sx_bi // -Ht02
@(subset_le_trans ????? H2t21) //
qed.

theorem wfinite_clear_pir_twn_tsn (t):
        t ϵ 𝐓 → ⓪𝐈❨t❩ ϵ 𝐖𝛀 → t ϵ 𝐖𝐍 → t ϵ 𝐒𝐍.
#t #H1t #H2t * #t0 #rs #H1t0 #H2t0
lapply (dbfss_clear_pir_wfinite_sx … H1t0) // -H2t #H3t0
@(wfinite_clear_pir_twn_tsn_aux … (⓪𝐈❨t0❩) … H1t0) -rs //
qed.
