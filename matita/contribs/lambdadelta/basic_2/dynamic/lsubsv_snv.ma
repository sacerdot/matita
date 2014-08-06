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

include "basic_2/dynamic/lsubsv_scpds.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Properties concerning stratified native validity *************************)

lemma lsubsv_snv_trans: ∀h,g,G,L2,T. ⦃G, L2⦄ ⊢ T ¡[h, g] →
                        ∀L1. G ⊢ L1 ⫃¡[h, g] L2 → ⦃G, L1⦄ ⊢ T ¡[h, g].
#h #g #G #L2 #T #H elim H -G -L2 -T //
[ #I #G #L2 #K2 #V #i #HLK2 #_ #IHV #L1 #HL12
  elim (lsubsv_drop_O1_trans … HL12 … HLK2) -L2 #X #H #HLK1
  elim (lsubsv_inv_pair2 … H) -H * #K1
  [ #HK12 #H destruct /3 width=5 by snv_lref/
  | #W #l #HVW #_ #_ #_ #_ #H1 #H2 destruct -IHV
    /3 width=6 by shnv_inv_snv, snv_lref/
  ]
| #a #I #G #L2 #V #T #_ #_ #IHV #IHT #L1 #HL12 destruct
  /4 width=1 by snv_bind, lsubsv_pair/
| #a #G #L2 #V #W0 #T #U0 #l #_ #_ #HVW0 #HTU0 #IHV #IHT #L1 #HL12
  elim (lsubsv_scpds_trans … HVW0 … HL12) -HVW0 #V0 #HV0 #HWV0
  elim (lsubsv_scpds_trans … HTU0 … HL12) -HTU0 #X #HT0 #H
  elim (cprs_inv_abst1 … H) -H #W #T0 #HW0 #_ #H destruct
  elim (cprs_conf … HWV0 … HW0) -W0
  /4 width=10 by snv_appl, scpds_cprs_trans, cprs_bind/
| #G #L2 #U #T #U0 #_ #_ #HU0 #HTU0 #IHU #IHT #L1 #HL12
  elim (lsubsv_scpds_trans … HTU0 … HL12) -HTU0
  /4 width=5 by lsubsv_cprs_trans, snv_cast, cprs_trans/
]
qed-.
