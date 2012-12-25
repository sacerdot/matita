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

include "basic_2/static/aaa_ltpss_dx.ma".
include "basic_2/static/lsuba_aaa.ma".
include "basic_2/reducibility/ltpr_ldrop.ma".

(* CONTEXT-FREE PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ********************)

(* Properties about atomic arity assignment on terms ************************)

fact aaa_ltpr_tpr_conf_aux: ∀L,T,L1,T1,A. L1 ⊢ T1 ⁝ A → L = L1 → T = T1 →
                            ∀L2. L1 ➡ L2 → ∀T2. T1 ➡ T2 → L2 ⊢ T2 ⁝ A.
#L #T @(fw_ind … L T) -L -T #L #T #IH
#L1 #T1 #A * -L1 -T1 -A
[ -IH #L1 #k #H1 #H2 #L2 #_ #T2 #H destruct
  >(tpr_inv_atom1 … H) -H //
| #I #L1 #K1 #V1 #B #i #HLK1 #HK1 #H1 #H2 #L2 #HL12 #T2 #H destruct
  >(tpr_inv_atom1 … H) -T2
  lapply (ldrop_pair2_fwd_fw … HLK1 (#i)) #HKV1
  elim (ltpr_ldrop_conf … HLK1 … HL12) -HLK1 -HL12 #X #H #HLK2
  elim (ltpr_inv_pair1 … H) -H #K2 #V2 #HK12 #HV12 #H destruct
  lapply (IH … HKV1 … HK1 … HK12 … HV12) // -L1 -K1 -V1 /2 width=5/
| #a #L1 #V1 #T1 #B #A #HB #HA #H1 #H2 #L2 #HL12 #X #H destruct
  elim (tpr_inv_abbr1 … H) -H *
  [ #V2 #T #T2 #HV12 #HT1 #HT2 #H destruct
    lapply (tps_lsubs_trans … HT2 (L2.ⓓV2) ?) -HT2 /2 width=1/ #HT2
    lapply (IH … HB … HL12 … HV12) -HB /width=5/ #HB
    lapply (IH … HA … (L2.ⓓV2) … HT1) -IH -HA -HT1 /width=5/ -T1 /2 width=1/ -L1 -V1 /3 width=5/
  | -B #T #HT1 #HXT #H destruct
    lapply (IH … HA … (L2.ⓓV1) … HT1) /width=5/ -T1 /2 width=1/ -L1 #HA
    @(aaa_inv_lift … HA … HXT) /2 width=1/
  ]
| #a #L1 #V1 #T1 #B #A #HB #HA #H1 #H2 #L2 #HL12 #X #H destruct
  elim (tpr_inv_abst1 … H) -H #V2 #T2 #HV12 #HT12 #H destruct
  lapply (IH … HB … HL12 … HV12) -HB /width=5/ #HB
  lapply (IH … HA … (L2.ⓛV2) … HT12) -IH -HA -HT12 /width=5/ -T1 /2 width=1/
| #L1 #V1 #T1 #B #A #HV1 #HT1 #H1 #H2 #L2 #HL12 #X #H destruct
  elim (tpr_inv_appl1 … H) -H *
  [ #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH … HV1 … HL12 … HV12) -HV1 -HV12 /width=5/ #HB
    lapply (IH … HT1 … HL12 … HT12) -IH -HT1 -HL12 -HT12 /width=5/ /2 width=3/
  | #a #V2 #W2 #T0 #T2 #HV12 #HT02 #H1 #H2 destruct
    elim (aaa_inv_abst … HT1) -HT1 #B0 #A0 #HB0 #HA0 #H destruct
    lapply (IH … HV1 … HL12 … HV12) -HV1 -HV12 /width=5/ #HB
    lapply (IH … HB0  … HL12 W2 ?) -HB0 /width=5/ #HB0
    lapply (IH … HA0 … (L2.ⓛW2) … HT02) -IH -HA0 -HT02 [2,4: // |3,5: skip ] /2 width=1/ -T0 -L1 -V1 /4 width=7/
  | #a #V0 #V2 #W0 #W2 #T0 #T2 #HV10 #HW02 #HT02 #HV02 #H1 #H2 destruct
    elim (aaa_inv_abbr … HT1) -HT1 #B0 #HW0 #HT0
    lapply (IH … HW0  … HL12 … HW02) -HW0 /width=5/ #HW2
    lapply (IH … HV1 … HL12 … HV10) -HV1 -HV10 /width=5/ #HV0
    lapply (IH … HT0 … (L2.ⓓW2) … HT02) -IH -HT0 -HT02 [2,4: // |3,5: skip ] /2 width=1/ -V1 -T0 -L1 -W0 #HT2
    @(aaa_abbr … HW2) -HW2
    @(aaa_appl … HT2) -HT2 /3 width=7/ (**) (* explict constructors, /5 width=7/ is too slow *)
  ]
| #L1 #V1 #T1 #A #HV1 #HT1 #H1 #H2 #L2 #HL12 #X #H destruct
  elim (tpr_inv_cast1 … H) -H
  [ * #V2 #T2 #HV12 #HT12 #H destruct
    lapply (IH … HV1 … HL12 … HV12) -HV1 -HV12 /width=5/ #HV2
    lapply (IH … HT1 … HL12 … HT12) -IH -HT1 -HL12 -HT12 /width=5/ -L1 -V1 -T1 /2 width=1/
  | -HV1 #HT1X
     lapply (IH … HT1 … HL12 … HT1X) -IH -HT1 -HL12 -HT1X /width=5/
  ]
]
qed.

lemma aaa_ltpr_tpr_conf: ∀L1,T1,A. L1 ⊢ T1 ⁝ A → ∀L2. L1 ➡ L2 →
                         ∀T2. T1 ➡ T2 → L2 ⊢ T2 ⁝ A.
/2 width=9/ qed.

lemma aaa_ltpr_conf: ∀L1,T,A. L1 ⊢ T ⁝ A → ∀L2. L1 ➡ L2 → L2 ⊢ T ⁝ A.
/2 width=5/ qed.

lemma aaa_tpr_conf: ∀L,T1,A. L ⊢ T1 ⁝ A → ∀T2. T1 ➡ T2 → L ⊢ T2 ⁝ A.
/2 width=5/ qed.
