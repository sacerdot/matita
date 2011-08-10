(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

include "Basic-2/substitution/tps_lift.ma".

(* PARTIAL SUBSTITUTION ON TERMS ********************************************)

(* Split properties *********************************************************)

lemma tps_split_up: ∀L,T1,T2,d,e. L ⊢ T1 [d, e] ≫ T2 → ∀i. d ≤ i → i ≤ d + e →
                    ∃∃T. L ⊢ T1 [d, i - d] ≫ T & L ⊢ T [i, d + e - i] ≫ T2.
#L #T1 #T2 #d #e #H elim H -L T1 T2 d e
[ /2/
| /2/
| #L #K #V #V1 #V2 #i #d #e #Hdi #Hide #HLK #HV1 #HV12 #IHV12 #j #Hdj #Hjde
  elim (lt_or_ge i j) #Hij
  [ -HV1 Hide;
    lapply (drop_fwd_drop2 … HLK) #HLK'
    elim (IHV12 (j - i - 1) ? ?) -IHV12; normalize /2/ -Hjde <minus_n_O >arith_b2 // #W1 #HVW1 #HWV1
    generalize in match HVW1 generalize in match Hij -HVW1 (**) (* rewriting in the premises, rewrites in the goal too *)
    >(plus_minus_m_m_comm … Hdj) in ⊢ (% → % → ?) -Hdj #Hij' #HVW1
    elim (lift_total W1 0 (i + 1)) #W2 #HW12
    lapply (tps_lift_ge … HWV1 … HLK' HW12 HV12 ?) -HWV1 HLK' HV12 // >arith_a2 /3 width=6/
  | -IHV12 Hdi Hdj;
    generalize in match HV1 generalize in match Hide -HV1 Hide (**) (* rewriting in the premises, rewrites in the goal too *)
    >(plus_minus_m_m_comm … Hjde) in ⊢ (% → % → ?) -Hjde #Hide #HV1
    @ex2_1_intro [2: @tps_lref |1: skip | /2 width=6/ ] (**) (* /3 width=6 is too slow *)
  ]
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hdi #Hide
  elim (IHV12 i ? ?) -IHV12 // #V #HV1 #HV2
  elim (IHT12 (i + 1) ? ?) -IHT12 [2: /2 by arith4/ |3: /2/ ] (* just /2/ is too slow *)
  -Hdi Hide >arith_c1 >arith_c1x #T #HT1 #HT2
  @ex2_1_intro [2,3: @tps_bind | skip ] (**) (* explicit constructors *)
  [3: @HV1 |4: @HT1 |5: // |1,2: skip | /3 width=5/ ]
| #L #I #V1 #V2 #T1 #T2 #d #e #_ #_ #IHV12 #IHT12 #i #Hdi #Hide
  elim (IHV12 i ? ?) -IHV12 // elim (IHT12 i ? ?) -IHT12 //
  -Hdi Hide /3 width=5/
]
qed.

lemma tps_inv_lift1_up: ∀L,U1,U2,dt,et. L ⊢ U1 [dt, et] ≫ U2 →
                        ∀K,d,e. ↓[d, e] L ≡ K → ∀T1. ↑[d, e] T1 ≡ U1 →
                        d ≤ dt → dt ≤ d + e → d + e ≤ dt + et →
                        ∃∃T2. K ⊢ T1 [d, dt + et - (d + e)] ≫ T2 & ↑[d, e] T2 ≡ U2.
#L #U1 #U2 #dt #et #HU12 #K #d #e #HLK #T1 #HTU1 #Hddt #Hdtde #Hdedet
elim (tps_split_up … HU12 (d + e) ? ?) -HU12 // -Hdedet #U #HU1 #HU2
lapply (tps_weak … HU1 d e ? ?) -HU1 // <plus_minus_m_m_comm // -Hddt Hdtde #HU1
lapply (tps_inv_lift1_eq … HU1 … HTU1) -HU1 #HU1 destruct -U1;
elim (tps_inv_lift1_ge … HU2 … HLK … HTU1 ?) -HU2 HLK HTU1 // <minus_plus_m_m /2/
qed.
