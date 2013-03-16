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

include "basic_2/unfold/ltpss_sn_alt.ma".
include "basic_2/static/ssta_ltpss_dx.ma".

(* STRATIFIED STATIC TYPE ASSIGNMENT ON TERMS *******************************)

(* Properties about sn parallel unfold **************************************)

lemma ssta_ltpss_sn_conf: ∀h,g,L1,T,U1,l. ⦃h, L1⦄ ⊢ T •[g] ⦃l, U1⦄ →
                          ∀L2,d,e. L1 ⊢ ▶* [d, e] L2 →
                          ∃∃U2. ⦃h, L2⦄ ⊢ T •[g] ⦃l, U2⦄ & L1 ⊢ U1 ▶* [d, e] U2.
#h #g #L1 #T #U1 #l #HTU1 #L2 #d #e #HL12
lapply (ltpss_sn_ltpssa … HL12) -HL12 #HL12
@(ltpssa_ind … HL12) -L2 [ /2 width=3/ ] -HTU1
#L #L2 #HL1 #HL2 * #U #HTU #HU1
lapply (ltpssa_ltpss_sn … HL1) -HL1 #HL1
elim (ssta_ltpss_dx_conf … HTU … HL2) -HTU #U2 #HTU2 #HU2
lapply (ltpss_dx_tpss_trans_eq … HU2 … HL2) -HU2 -HL2 #HU2
lapply (ltpss_sn_tpss_trans_eq … HU2 … HL1) -HU2 -HL1 #HU2
lapply (tpss_trans_eq … HU1 HU2) -U /2 width=3/
qed.

lemma ssta_ltpss_sn_tpss_conf: ∀h,g,L1,T1,U1,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                               ∀L2,d,e. L1 ⊢ ▶* [d, e] L2 →
                               ∀T2. L2 ⊢ T1 ▶* [d, e] T2 →
                               ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l, U2⦄ &
                                     L1 ⊢ U1 ▶* [d, e] U2.
#h #g #L1 #T1 #U1 #l #HTU1 #L2 #d #e #HL12 #T2 #HT12
elim (ssta_ltpss_sn_conf … HTU1 … HL12) -HTU1 #U #HT1U #HU1
elim (ssta_tpss_conf … HT1U … HT12) -T1 #U2 #HTU2 #HU2
lapply (ltpss_sn_tpss_trans_eq … HU2 … HL12) -HU2 -HL12 #HU2
lapply (tpss_trans_eq … HU1 HU2) -U /2 width=3/
qed.

lemma ssta_ltpss_sn_tps_conf: ∀h,g,L1,T1,U1,l. ⦃h, L1⦄ ⊢ T1 •[g] ⦃l, U1⦄ →
                              ∀L2,d,e. L1 ⊢ ▶* [d, e] L2 →
                              ∀T2. L2 ⊢ T1 ▶ [d, e] T2 →
                              ∃∃U2. ⦃h, L2⦄ ⊢ T2 •[g] ⦃l, U2⦄ &
                                    L1 ⊢ U1 ▶* [d, e] U2.
/3 width=3/ qed.
