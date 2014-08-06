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

include "basic_2/multiple/fqus_alt.ma".
include "basic_2/computation/scpds_lift.ma".
include "basic_2/dynamic/snv.ma".

(* STRATIFIED NATIVE VALIDITY FOR TERMS *************************************)

(* Relocation properties ****************************************************)

lemma snv_lift: ∀h,g,G,K,T. ⦃G, K⦄ ⊢ T ¡[h, g] → ∀L,s,d,e. ⇩[s, d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃G, L⦄ ⊢ U ¡[h, g].
#h #g #G #K #T #H elim H -G -K -T
[ #G #K #k #L #s #d #e #_ #X #H
  >(lift_inv_sort1 … H) -X -K -d -e //
| #I #G #K #K0 #V #i #HK0 #_ #IHV #L #s #d #e #HLK #X #H
  elim (lift_inv_lref1 … H) * #Hid #H destruct
  [ elim (drop_trans_le … HLK … HK0) -K /2 width=2 by lt_to_le/ #X #HL0 #H
    elim (drop_inv_skip2 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #L0 #W #HLK0 #HVW #H destruct
    /3 width=9 by snv_lref/
  | lapply (drop_trans_ge … HLK … HK0 ?) -K
    /3 width=9 by snv_lref, drop_inv_gen/
  ]
| #a #I #G #K #V #T #_ #_ #IHV #IHT #L #s #d #e #HLK #X #H
  elim (lift_inv_bind1 … H) -H #W #U #HVW #HTU #H destruct
  /4 width=5 by snv_bind, drop_skip/
| #a #G #K #V #W0 #T #U0 #l #_ #_ #HVW0 #HTU0 #IHV #IHT #L #s #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W #U #HVW #HTU #H destruct
  elim (lift_total W0 d e) #W1 #HW01
  elim (lift_total U0 (d+1) e) #U1 #HU01
  @(snv_appl … a … W1 … U1 l) [1,2,3: /2 width=10 by scpds_lift/ ] -IHV -IHT
  @(scpds_lift … HTU0 … HLK … HTU) /2 width=1 by lift_bind/ (**) (* full auto raises typechecker failure *)
| #G #K #V #T #U0 #_ #_ #HVU0 #HTU0 #IHV #IHT #L #s #d #e #HLK #X #H
  elim (lift_inv_flat1 … H) -H #W #U #HVW #HTU #H destruct
  elim (lift_total U0 d e)
  /3 width=12 by snv_cast, cprs_lift, scpds_lift/
]
qed.

lemma snv_inv_lift: ∀h,g,G,L,U. ⦃G, L⦄ ⊢ U ¡[h, g] → ∀K,s,d,e. ⇩[s, d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃G, K⦄ ⊢ T ¡[h, g].
#h #g #G #L #U #H elim H -G -L -U
[ #G #L #k #K #s #d #e #_ #X #H
  >(lift_inv_sort2 … H) -X -L -d -e //
| #I #G #L #L0 #W #i #HL0 #_ #IHW #K #s #d #e #HLK #X #H
  elim (lift_inv_lref2 … H) * #Hid #H destruct
  [ elim (drop_conf_le … HLK … HL0) -L /2 width=2 by lt_to_le/ #X #HK0 #H
    elim (drop_inv_skip1 … H) -H /2 width=1 by lt_plus_to_minus_r/ -Hid #K0 #V #HLK0 #HVW #H destruct
    /3 width=12 by snv_lref/
  | lapply (drop_conf_ge … HLK … HL0 ?) -L /3 width=9 by snv_lref/
  ]
| #a #I #G #L #W #U #_ #_ #IHW #IHU #K #s #d #e #HLK #X #H
  elim (lift_inv_bind2 … H) -H #V #T #HVW #HTU #H destruct
  /4 width=5 by snv_bind, drop_skip/
| #a #G #L #W #W1 #U #U1 #l #_ #_ #HW1 #HU1 #IHW #IHU #K #s #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V #T #HVW #HTU #H destruct
  elim (scpds_inv_lift1 … HW1 … HLK … HVW) -HW1 #W0 #HW01 #HVW0  
  elim (scpds_inv_lift1 … HU1 … HLK … HTU) -HU1 #X #H #HTU0
  elim (lift_inv_bind2 … H) -H #Y #U0 #HY #HU01 #H destruct
  lapply (lift_inj … HY … HW01) -HY #H destruct
  /3 width=6 by snv_appl/
| #G #L #W #U #U1 #_ #_ #HWU1 #HU1 #IHW #IHU #K #s #d #e #HLK #X #H
  elim (lift_inv_flat2 … H) -H #V #T #HVW #HTU #H destruct
  elim (cprs_inv_lift1 … HWU1 … HLK … HVW) -HWU1 #U0 #HU01 #HVU0
  elim (scpds_inv_lift1 … HU1 … HLK … HTU) -HU1 #X #HX #HTU0 
  lapply (lift_inj … HX … HU01) -HX #H destruct
  /3 width=5 by snv_cast/
]
qed-.

(* Properties on subclosure *************************************************)

lemma snv_fqu_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                    ⦃G1, L1⦄ ⊢ T1 ¡[h, g] → ⦃G2, L2⦄ ⊢ T2 ¡[h, g].
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2
[ #I1 #G1 #L1 #V1 #H
  elim (snv_inv_lref … H) -H #I2 #L2 #V2 #H #HV2
  lapply (drop_inv_O2 … H) -H #H destruct //
|2: *
|5,6: /3 width=8 by snv_inv_lift/
]
[1,3: #a #I #G1 #L1 #V1 #T1 #H elim (snv_inv_bind … H) -H //
|2,4: * #G1 #L1 #V1 #T1 #H
  [1,3: elim (snv_inv_appl … H) -H //
  |2,4: elim (snv_inv_cast … H) -H //
  ]
]
qed-.

lemma snv_fquq_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐⸮ ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ T1 ¡[h, g] → ⦃G2, L2⦄ ⊢ T2 ¡[h, g].
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fquq_inv_gen … H) -H [|*]
/2 width=5 by snv_fqu_conf/
qed-.

lemma snv_fqup_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐+ ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ T1 ¡[h, g] → ⦃G2, L2⦄ ⊢ T2 ¡[h, g].
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H @(fqup_ind … H) -G2 -L2 -T2
/3 width=5 by fqup_strap1, snv_fqu_conf/
qed-.

lemma snv_fqus_conf: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐* ⦃G2, L2, T2⦄ →
                     ⦃G1, L1⦄ ⊢ T1 ¡[h, g] → ⦃G2, L2⦄ ⊢ T2 ¡[h, g].
#h #g #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqus_inv_gen … H) -H [|*]
/2 width=5 by snv_fqup_conf/
qed-.
