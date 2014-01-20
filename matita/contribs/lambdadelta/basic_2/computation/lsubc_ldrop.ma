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
lemma lsubc_ldrop_O1_trans: ∀RP,G,L1,L2. G ⊢ L1 ⊑[RP] L2 → ∀K2,s,e. ⇩[s, 0, e] L2 ≡ K2 →
                            ∃∃K1. ⇩[s, 0, e] L1 ≡ K1 & G ⊢ K1 ⊑[RP] K2.
#RP #G #L1 #L2 #H elim H -L1 -L2
[ #X #s #e #H elim (ldrop_inv_atom1 … H) -H /4 width=3 by ldrop_atom, ex2_intro/
| #I #L1 #L2 #V #_ #IHL12 #X #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #H destruct
  [ elim (IHL12 L2 s 0) -IHL12 // #X #H <(ldrop_inv_O2 … H) -H
    /3 width=3 by lsubc_pair, ldrop_pair, ex2_intro/
  | elim (IHL12 … H) -L2 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
| #L1 #L2 #V #W #A #HV #H1W #H2W #_ #IHL12 #X #s #e #H
  elim (ldrop_inv_O1_pair1 … H) -H * #He #H destruct
  [ elim (IHL12 L2 s 0) -IHL12 // #X #H <(ldrop_inv_O2 … H) -H
    /3 width=8 by lsubc_abbr, ldrop_pair, ex2_intro/
  | elim (IHL12 … H) -L2 /3 width=3 by ldrop_drop_lt, ex2_intro/
  ]
]
qed-.

(* Basic_1: was: csubc_drop_conf_rev *)
lemma ldrop_lsubc_trans: ∀RR,RS,RP.
                         acp RR RS RP → acr RR RS RP (λG,L,T. RP G L T) →
                         ∀G,L1,K1,d,e. ⇩[Ⓕ, d, e] L1 ≡ K1 → ∀K2. G ⊢ K1 ⊑[RP] K2 →
                         ∃∃L2. G ⊢ L1 ⊑[RP] L2 & ⇩[Ⓕ, d, e] L2 ≡ K2.
#RR #RS #RP #Hacp #Hacr #G #L1 #K1 #d #e #H elim H -L1 -K1 -d -e
[ #d #e #He #X #H elim (lsubc_inv_atom1 … H) -H
  >He /2 width=3 by ex2_intro/
| #L1 #I #V1 #X #H
  elim (lsubc_inv_pair1 … H) -H *
  [ #K1 #HLK1 #H destruct /3 width=3 by lsubc_pair, ldrop_pair, ex2_intro/
  | #K1 #V #W1 #A #HV1 #H1W1 #H2W1 #HLK1 #H1 #H2 #H3 destruct
    /3 width=4 by lsubc_abbr, ldrop_pair, ex2_intro/
  ]
| #I #L1 #K1 #V1 #e #_ #IHLK1 #K2 #HK12
  elim (IHLK1 … HK12) -K1 /3 width=5 by lsubc_pair, ldrop_drop, ex2_intro/
| #I #L1 #K1 #V1 #V2 #d #e #HLK1 #HV21 #IHLK1 #X #H
  elim (lsubc_inv_pair1 … H) -H *
  [ #K2 #HK12 #H destruct
    elim (IHLK1 … HK12) -K1 /3 width=5 by lsubc_pair, ldrop_skip, ex2_intro/
  | #K2 #V #W2 #A #HV2 #H1W2 #H2W2 #HK12 #H1 #H2 #H3 destruct
    elim (lift_inv_flat1 … HV21) -HV21 #W3 #V3 #HW23 #HV3 #H destruct
    elim (IHLK1 … HK12) #K #HL1K #HK2
    lapply (aacr_acr … Hacp Hacr A) -Hacp -Hacr #HA
    lapply (s8 … HA … HV2 … HLK1 HV3) -HV2
    lapply (s8 … HA … H1W2 … HLK1 HW23) -H1W2
    /4 width=11 by lsubc_abbr, aaa_lift, ldrop_skip, ex2_intro/
  ]
]
qed-.
