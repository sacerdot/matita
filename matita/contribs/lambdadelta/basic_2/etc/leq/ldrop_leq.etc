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

include "ground_2/ynat/ynat_plus.ma".
include "basic_2/grammar/leq.ma".
include "basic_2/relocation/ldrop.ma".

(* BASIC SLICING FOR LOCAL ENVIRONMENTS *************************************)

lemma ldrop_leq_conf_ge: ∀L1,L2,d,e. L1 ≃[d, e] L2 →
                         ∀I,K,V,i. ⇩[O, i]L1 ≡ K.ⓑ{I}V → d + e ≤ i →
                         ⇩[O, i]L2 ≡ K.ⓑ{I}V.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
[ #d #e #J #K #W #i #H elim (ldrop_inv_atom1 … H) -H
  #H destruct
| #I #L1 #L2 #V #HL12 #IHL12 #J #K #W #i #H #_ elim (ldrop_inv_O1_pair1 … H) -H
  * #H1 #H2
  [ -IHL12 lapply (leq_inv_O2 … HL12) -HL12
    #H3 destruct //
  | -HL12 /4 width=1 by ldrop_ldrop_lt, yle_inj/
  ]
| #I1 #I2 #L1 #L2 #V1 #V2 #e #_ #IHL12 #J #K #W #i #H1 >yplus_succ_swap
  #Hei elim (yle_inv_inj2 … Hei) -Hei
  #x #Hei #H elim (yplus_inv_inj … H) -H normalize
  #y #z >commutative_plus
  #H1 #H2 #H3 destruct elim (le_inv_plus_l … Hei) -Hei
  #Hzi #Hi lapply (ldrop_inv_ldrop1_lt … H1 ?) -H1
  /4 width=1 by ldrop_ldrop_lt, yle_inj/
| #I #L1 #L2 #V #d #e #_ #IHL12 #J #K #W #i #H0 #Hdei elim (yle_inv_inj2 … Hdei) -Hdei
  #x #Hdei #H elim (yplus_inv_inj … H) -H
  #y #z >commutative_plus
  #H1 #H2 #H3 destruct elim (ysucc_inv_inj_dx … H2) -H2
  #x #H1 #H2 destruct elim (le_inv_plus_l … Hdei)
  #_ #Hi lapply (ldrop_inv_ldrop1_lt … H0 ?) -H0
  [2: #H0 @ldrop_ldrop_lt ] [2,3: /2 width=3 by lt_to_le_to_lt/ ]
  /4 width=3 by yle_inj, monotonic_pred/
]
qed-.

lemma ldrop_leq_conf_be: ∀L1,L2,d,e. L1 ≃[d, e] L2 →
                         ∀I1,K1,V1,i. ⇩[O, i]L1 ≡ K1.ⓑ{I1}V1 → d ≤ i → i < d + e →
                         ∃∃I2,K2,V2. K1 ≃[0, ⫰(d+e-i)] K2 & ⇩[O, i]L2 ≡ K2.ⓑ{I2}V2.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
[ #d #e #J1 #K1 #W1 #i #H elim (ldrop_inv_atom1 … H) -H
  #H destruct
| #I #L1 #L2 #V #HL12 #IHL12 #J1 #K1 #W1 #i #_ #_ #H elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V1 #V2 #e #HL12 >yplus_O1 >yplus_O1
  #IHL12 #J1 #K1 #W1 #i #H #_ elim (eq_or_gt i) #Hi destruct [ -IHL12 | -HL12 ]
  [ #_ lapply (ldrop_inv_O2 … H) -H
    #H destruct >ypred_succ /2 width=5 by ldrop_pair, ex2_3_intro/
  | lapply (ldrop_inv_ldrop1_lt … H ?) -H //
    #H <(ylt_inv_O1 i) /2 width=1 by ylt_inj/
    #Hie lapply (ylt_inv_succ … Hie) -Hie
    #Hie elim (IHL12 … H) -IHL12 -H //
    >yminus_succ /3 width=5 by ldrop_ldrop_lt, ex2_3_intro/
  ]
| #I #L1 #L2 #V #d #e #_ #IHL12 #J1 #K1 #W1 #i #H #Hdi lapply (ylt_yle_trans 0 … Hdi ?) //
  #Hi <(ylt_inv_O1 … Hi) >yplus_succ1 >yminus_succ elim (yle_inv_succ1 … Hdi) -Hdi
  #Hdi #_ #Hide lapply (ylt_inv_succ … Hide)
  #Hide lapply (ylt_inv_inj … Hi) -Hi
  #Hi lapply (ldrop_inv_ldrop1_lt … H ?) -H //
  #H elim (IHL12 … H) -IHL12 -H
  /3 width=5 by ldrop_ldrop_lt, ex2_3_intro/
] 
qed-.

lemma ldrop_leq_conf_lt: ∀L1,L2,d,e. L1 ≃[d, e] L2 →
                         ∀I,K1,V,i. ⇩[O, i]L1 ≡ K1.ⓑ{I}V → i < d →
                         ∃∃K2. K1 ≃[⫰(d-i), e] K2 & ⇩[O, i]L2 ≡ K2.ⓑ{I}V.
#L1 #L2 #d #e #H elim H -L1 -L2 -d -e
[ #d #e #J #K1 #W #i #H elim (ldrop_inv_atom1 … H) -H
  #H destruct
| #I #L1 #L2 #V #_ #_ #J #K1 #W #i #_ #H elim (ylt_yle_false … H) //
| #I1 #I2 #L1 #L2 #V1 #V2 #e #_ #_ #J #K1 #W #i #_ #H elim (ylt_yle_false … H) //
| #I #L1 #L2 #V #d #e #HL12 #IHL12 #J #K1 #W #i #H elim (eq_or_gt i) #Hi destruct [ -IHL12 | -HL12 ]
  [ #_ lapply (ldrop_inv_O2 … H) -H
    #H destruct >ypred_succ /2 width=5 by ldrop_pair, ex2_intro/
  | lapply (ldrop_inv_ldrop1_lt … H ?) -H //
    #H <(ylt_inv_O1 i) /2 width=1 by ylt_inj/
    #Hie lapply (ylt_inv_succ … Hie) -Hie
    #Hie elim (IHL12 … H) -IHL12 -H
    >yminus_succ /3 width=5 by ldrop_ldrop_lt, ex2_intro/
  ]
]
qed-.
