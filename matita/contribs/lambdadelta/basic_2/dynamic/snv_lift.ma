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

include "basic_2/computation/dxprs_lift.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Relocation properties ****************************************************)

lemma snv_lift: ∀h,g,K,T. ⦃h, K⦄ ⊢ T ¡[g] → ∀L,d,e. ⇩[d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃h, L⦄ ⊢ U ¡[g].
#h #g #K #T #H elim H -K -T
[ #K #k #L #d #e #_ #X #H
  >(lift_inv_sort1 … H) -X -K -d -e //
| #I #K #K0 #V #i #HK0 #_ #IHV #L #d #e #HLK #X #H
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (ldrop_trans_le … HLK … HK0 ?) -K /2 width=2/ #X #HL0 #H
    elim (ldrop_inv_skip2 … H ?) -H /2 width=1/ -Hid #L0 #W #HLK0 #HVW #H destruct
    /3 width=8/
  | lapply (ldrop_trans_ge … HLK … HK0 ?) -K // -Hid /3 width=8/
  ]
| #a #I #K #V #T #_ #_ #IHV #IHT #L #d #e #HLK #X #H
  elim (lift_inv_bind1 … H) -H #W #U #HVW #HTU #H destruct
  /4 width=4/
| #a #K #V #V0 #V1 #T #T1 #l #_ #_ #HV0 #HV01 #HT1 #IHV #IHT #L #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W #U #HVW #HTU #H destruct
  elim (lift_total V0 d e) #W0 #HVW0
  elim (lift_total V1 d e) #W1 #HVW1
  elim (lift_total T1 (d+1) e) #U1 #HTU1
  @(snv_appl … a … W0 … W1 … U1 l)
  [ /2 width=4/ | /2 width=4/ | /2 width=9/ | /2 width=9/ ]
  @(dxprs_lift … HLK … HTU … HT1) /2 width=1/
| #K #V0 #T #V #l #_ #_ #HTV #HV0 #IHV0 #IHT #L #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W0 #U #HVW0 #HTU #H destruct
  elim (lift_total V d e) #W #HVW
  @(snv_cast … W l) [ /2 width=4/ | /2 width=4/ | /2 width=9/ | /2 width=9/ ]
]
qed.

lemma snv_inv_lift: ∀h,g,L,U. ⦃h, L⦄ ⊢ U ¡[g] → ∀K,d,e. ⇩[d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃h, K⦄ ⊢ T ¡[g].
#h #g #L #U #H elim H -L -U
[ #L #k #K #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X -L -d -e //
| #I #L #L0 #W #i #HL0 #_ #IHW #K #d #e #HLK #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct
  [ elim (ldrop_conf_le … HLK … HL0 ?) -L /2 width=2/ #X #HK0 #H
    elim (ldrop_inv_skip1 … H ?) -H /2 width=1/ -Hid #K0 #V #HLK0 #HVW #H destruct
    /3 width=8/
  | lapply (ldrop_conf_ge … HLK … HL0 ?) -L // -Hid /3 width=8/
  ]
| #a #I #L #W #U #_ #_ #IHW #IHU #K #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #V #T #HVW #HTU #H destruct /4 width=4/
| #a #L #W #W0 #W1 #U #U1 #l #_ #_ #HW0 #HW01 #HU1 #IHW #IHU #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V #T #HVW #HTU #H destruct
  elim (ssta_inv_lift1 … HW0 … HLK … HVW) -HW0 #V0 #HV0 #HVW0
  elim (cprs_inv_lift1 … HLK … HVW0 … HW01) -W0 #V1 #HVW1 #HV01
  elim (dxprs_inv_lift1 … HLK … HTU … HU1) -HU1 #X #H #HTU
  elim (lift_inv_bind2 … H) -H #Y #T1 #HY #HTU1 #H destruct
  lapply (lift_inj … HY … HVW1) -HY #H destruct /3 width=8/
| #L #W0 #U #W #l #_ #_ #HUW #HW0 #IHW0 #IHU #K #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V0 #T #HVW0 #HTU #H destruct
  elim (ssta_inv_lift1 … HUW … HLK … HTU) -HUW #V #HTV #HVW
  lapply (cpcs_inv_lift … HLK … HVW … HVW0 ?) // -W /3 width=4/
]
qed-.
