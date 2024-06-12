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

include "ground/subsets/subsets_finite_lt.ma".
include "delayed_updating/reduction/dbfr_preterm.ma".
include "delayed_updating/computation/dbfrs_normal.ma".
include "delayed_updating/computation/dbfrs_irefs.ma".
include "delayed_updating/computation/dbfrs_irefs_finite.ma".
include "delayed_updating/computation/dbfrs_confluence.ma".
include "delayed_updating/computation/prototerm_wn.ma".
include "delayed_updating/computation/prototerm_sn.ma".

(* STRONG NORMALIZATION FOR PRETERM *****************************************)

(* Constructions with twn ***************************************************)

lemma finite_pirc_twn_tsn_aux (t1):
      t1 ϵ 𝐍𝐅 → ∀u0. u0 ϵ 𝛀 →
      ∀t0,rs. t0 ➡*𝐝𝐛𝐟[rs] t1 → t0 ϵ 𝐓 →  𝐈❨t1❩ ⧵ 𝐈❨t0❩ ⊆ u0 →
      t0 ϵ 𝐒𝐍.
#t1 #Ht1 @(subsets_finite_ind_lt … eq_path_dec)
#u0 #_ #IH #t0 #rs #Ht01 #Ht0 #Hu0
@tsn_step #t2 #r #Ht02
elim (dbfrs_conf … Ht0 … Ht01 … t2) -rs
[2,3: /2 width=2 by frs_step/ ] #t #ss1 #ss2 #Hs1 #Hs2
lapply (dbfrs_des_tnf_sn … Hs1) // -ss1 #Hs1
lapply (dbfrs_eq_canc_dx … Hs2 … Hs1) -t #H1t21
lapply (dbfr_des_lt_pirc_bi … Ht02) //
lapply (dbfr_preterm_trans … Ht02) // -r -Ht0 #Ht2 #Ht02
lapply (dbfrs_des_le_pirc_bi … H1t21) // #H2t21
@(IH (𝐈❨t1❩⧵𝐈❨t2❩) … H1t21) [2,3: // ] -ss2 -IH -Ht1 -Ht2
@(subset_lt_le_trans … Hu0) -u0
@subset_lt_nimp_sn_bi // -Ht02
@(subset_le_trans ????? H2t21) //
qed.

theorem finite_pirc_twn_tsn (t):
        t ϵ 𝐓 → 𝐈❨t❩ ϵ 𝛀 → t ϵ 𝐖𝐍 → t ϵ 𝐒𝐍.
#t #H1t #H2t * #t0 #rs #H1t0 #H2t0
lapply (dbfrs_pirc_finite_sn … H1t0) // -H2t #H3t0
@(finite_pirc_twn_tsn_aux … (𝐈❨t0❩) … H1t0) -rs //
qed.
