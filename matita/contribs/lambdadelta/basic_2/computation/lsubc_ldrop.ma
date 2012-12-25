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

include "basic_2/static/aaa_lift.ma".
include "basic_2/computation/lsubc.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR ABSTRACT CANDIDATES OF REDUCIBILITY *****)

(* Properties concerning basic local environment slicing ********************)

(* Basic_1: was: csubc_drop_conf_O *)
(* Note: the constant 0 can not be generalized *)
lemma lsubc_ldrop_O1_trans: ∀RP,L1,L2. L1 ⊑[RP] L2 → ∀K2,e. ⇩[0, e] L2 ≡ K2 →
                            ∃∃K1. ⇩[0, e] L1 ≡ K1 & K1 ⊑[RP] K2.
#RP #L1 #L2 #H elim H -L1 -L2
[ #X #e #H
  >(ldrop_inv_atom1 … H) -H /2 width=3/
| #I #L1 #L2 #V #_ #IHL12 #X #e #H
  elim (ldrop_inv_O1 … H) -H * #He #H destruct
  [ elim (IHL12 L2 0 ?) -IHL12 // #X #H <(ldrop_inv_refl … H) -H /3 width=3/
  | elim (IHL12 … H) -L2 /3 width=3/
  ]
| #L1 #L2 #V #W #A #HV #HW #_ #IHL12 #X #e #H
  elim (ldrop_inv_O1 … H) -H * #He #H destruct
  [ elim (IHL12 L2 0 ?) -IHL12 // #X #H <(ldrop_inv_refl … H) -H /3 width=7/
  | elim (IHL12 … H) -L2 /3 width=3/
  ]
qed-.

(* Basic_1: was: csubc_drop_conf_rev *)
lemma ldrop_lsubc_trans: ∀RR,RS,RP.
                         acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                         ∀L1,K1,d,e. ⇩[d, e] L1 ≡ K1 → ∀K2. K1 ⊑[RP] K2 →
                         ∃∃L2. L1 ⊑[RP] L2 & ⇩[d, e] L2 ≡ K2.
#RR #RS #RP #Hacp #Hacr #L1 #K1 #d #e #H elim H -L1 -K1 -d -e
[ #d #e #X #H
  >(lsubc_inv_atom1 … H) -H /2 width=3/
| #L1 #I #V1 #X #H
  elim (lsubc_inv_pair1 … H) -H *
  [ #K1 #HLK1 #H destruct /3 width=3/
  | #K1 #W1 #A #HV1 #HW1 #HLK1 #H1 #H2 destruct /3 width=3/
  ]
| #L1 #K1 #I #V1 #e #_ #IHLK1 #K2 #HK12
  elim (IHLK1 … HK12) -K1 /3 width=5/
| #L1 #K1 #I #V1 #V2 #d #e #HLK1 #HV21 #IHLK1 #X #H
  elim (lsubc_inv_pair1 … H) -H *
  [ #K2 #HK12 #H destruct
    elim (IHLK1 … HK12) -K1 /3 width=5/
  | #K2 #W2 #A #HV2 #HW2 #HK12 #H1 #H2 destruct
    elim (IHLK1 … HK12) #K #HL1K #HK2
    lapply (aacr_acr … Hacp Hacr A) -Hacp -Hacr #HA
    lapply (s7 … HA … HV2 … HLK1 HV21) -HV2
    elim (lift_total W2 d e) /4 width=9/
  ]
]
qed-.
