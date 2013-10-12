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

include "basic_2/computation/cpds_lift.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Relocation properties ****************************************************)

lemma snv_lift: ∀h,g,G,K,T. ⦃G, K⦄ ⊢ T ¡[h, g] → ∀L,d,e. ⇩[d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃G, L⦄ ⊢ U ¡[h, g].
#h #g #G #K #T #H elim H -G -K -T
[ #G #K #k #L #d #e #_ #X #H
  >(lift_inv_sort1 … H) -X -K -d -e //
| #I #G #K #K0 #V #i #HK0 #_ #IHV #L #d #e #HLK #X #H
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (ldrop_trans_le … HLK … HK0) -K /2 width=2/ #X #HL0 #H
    elim (ldrop_inv_skip2 … H) -H /2 width=1/ -Hid #L0 #W #HLK0 #HVW #H destruct
    /3 width=8/
  | lapply (ldrop_trans_ge … HLK … HK0 ?) -K // -Hid /3 width=8/
  ]
| #a #I #G #K #V #T #_ #_ #IHV #IHT #L #d #e #HLK #X #H
  elim (lift_inv_bind1 … H) -H #W #U #HVW #HTU #H destruct
  /4 width=4/
| #a #G #K #V #V0 #V1 #T #T1 #l #_ #_ #Hl #HV0 #HV01 #HT1 #IHV #IHT #L #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W #U #HVW #HTU #H destruct
  elim (lift_total V0 d e) #W0 #HVW0
  elim (lift_total V1 d e) #W1 #HVW1
  elim (lift_total T1 (d+1) e) #U1 #HTU1
  @(snv_appl … a … W0 … W1 … U1 l)
  [1,2: /2 width=4/ | /2 width=7/ |4,5: /2 width=9/ ]
  @(cpds_lift … HT1 … HLK … HTU) /2 width=1/
| #G #K #V0 #T #V #l #_ #_ #Hl #HTV #HV0 #IHV0 #IHT #L #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W0 #U #HVW0 #HTU #H destruct
  elim (lift_total V d e) #W #HVW
  @(snv_cast … W l) [1,2: /2 width=4/ | /2 width=7/ |4,5: /2 width=9/ ]
]
qed.

lemma snv_inv_lift: ∀h,g,G,L,U. ⦃G, L⦄ ⊢ U ¡[h, g] → ∀K,d,e. ⇩[d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃G, K⦄ ⊢ T ¡[h, g].
#h #g #G #L #U #H elim H -G -L -U
[ #G #L #k #K #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X -L -d -e //
| #I #G #L #L0 #W #i #HL0 #_ #IHW #K #d #e #HLK #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct
  [ elim (ldrop_conf_le … HLK … HL0) -L /2 width=2/ #X #HK0 #H
    elim (ldrop_inv_skip1 … H) -H /2 width=1/ -Hid #K0 #V #HLK0 #HVW #H destruct
    /3 width=8/
  | lapply (ldrop_conf_ge … HLK … HL0 ?) -L // -Hid /3 width=8/
  ]
| #a #I #G #L #W #U #_ #_ #IHW #IHU #K #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #V #T #HVW #HTU #H destruct /4 width=4/
| #a #G #L #W #W0 #W1 #U #U1 #l #_ #_ #Hl #HW0 #HW01 #HU1 #IHW #IHU #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V #T #HVW #HTU #H destruct
  lapply (da_inv_lift … Hl … HLK … HVW) -Hl #Hl
  elim (ssta_inv_lift1 … HW0 … HLK … HVW) -HW0 #V0 #HVW0 #HV0
  elim (cprs_inv_lift1 … HW01 … HLK … HVW0) -W0 #V1 #HVW1 #HV01
  elim (cpds_inv_lift1 … HU1 … HLK … HTU) -HU1 #X #H #HTU
  elim (lift_inv_bind2 … H) -H #Y #T1 #HY #HTU1 #H destruct
  lapply (lift_inj … HY … HVW1) -HY #H destruct /3 width=8/
| #G #L #W0 #U #W #l #_ #_ #Hl #HUW #HW0 #IHW0 #IHU #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V0 #T #HVW0 #HTU #H destruct
  lapply (da_inv_lift … Hl … HLK … HTU) -Hl #Hl
  elim (ssta_inv_lift1 … HUW … HLK … HTU) -HUW #V #HVW #HTV
  lapply (cpcs_inv_lift G … HLK … HVW … HVW0 ?) // -W /3 width=4/
]
qed-.

(* Advanced properties ******************************************************)

lemma snv_fqu_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1⦄ ⊢ T1 ¡[h, g] → ⦃G2, L2⦄ ⊢ T2 ¡[h, g].
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I1 #G1 #L1 #V1 #H
  elim (snv_inv_lref … H) -H #I2 #L2 #V2 #H #HV2
  lapply (ldrop_inv_O2 … H) -H #H destruct //
|2: *
|5,6: /3 width=7 by snv_inv_lift/
]
[1,3: #a #I #G1 #L1 #V1 #T1 #H elim (snv_inv_bind … H) -H //
|2,4: * #G1 #L1 #V1 #T1 #H
  [1,3: elim (snv_inv_appl … H) -H //
  |2,4: elim (snv_inv_cast … H) -H //
  ]
]
qed-.
