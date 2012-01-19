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

include "Basic_2/unfold/gr2_gr2.ma".
include "Basic_2/unfold/lifts_lifts.ma".
include "Basic_2/unfold/ldrops_ldrops.ma".
include "Basic_2/static/aaa.ma".
include "Basic_2/computation/lsubc.ma".

(* NOTE: The constant (0) can not be generalized *)
axiom lsubc_ldrop_trans: ∀RP,L1,L2. L1 [RP] ⊑ L2 → ∀K2,e. ⇩[0, e] L2 ≡ K2 →
                         ∃∃K1. ⇩[0, e] L1 ≡ K1 & K1 [RP] ⊑ K2.

axiom ldrops_lsubc_trans: ∀RP,L1,K1,des. ⇩*[des] L1 ≡ K1 → ∀K2. K1 [RP] ⊑ K2 →
                          ∃∃L2. L1 [RP] ⊑ L2 & ⇩*[des] L2 ≡ K2.

(* ABSTRACT COMPUTATION PROPERTIES ******************************************)

(* Main propertis ***********************************************************)

axiom aacr_aaa_csubc_lifts: ∀RR,RS,RP.
                              acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
                              ∀L1,T,A. L1 ⊢ T ÷ A → ∀L0,des. ⇩*[des] L0 ≡ L1 →
                              ∀T0. ⇧*[des] T ≡ T0 → ∀L2. L2 [RP] ⊑ L0 →
                              ⦃L2, T0⦄ [RP] ϵ 〚A〛.
(*
#RR #RS #RP #H1RP #H2RP #L1 #T #A #H elim H -L1 -T -A
[ #L #k #L0 #des #HL0 #X #H #L2 #HL20
  >(lifts_inv_sort1 … H) -H
  lapply (aacr_acr … H1RP H2RP 𝕒) #HAtom
  @(s2 … HAtom … ◊) // /2 width=2/
| #I #L1 #K1 #V1 #B #i #HLK1 #_ #IHB #L0 #des #HL01 #X #H #L2 #HL20
  lapply (aacr_acr … H1RP H2RP B) #HB
  elim (lifts_inv_lref1 … H) -H #i1 #Hi1 #H destruct
  lapply (ldrop_fwd_ldrop2 … HLK1) #HK1b
  elim (ldrops_ldrop_trans … HL01 … HLK1) #X #des1 #i0 #HL0 #H #Hi0 #Hdes1
  >(at_mono … Hi1 … Hi0) -i1
  elim (ldrops_inv_skip2 … Hdes1 … H) -des1 #K0 #V0 #des0 #Hdes0 #HK01 #HV10 #H destruct
  elim (lsubc_ldrop_trans … HL20 … HL0) -HL0 #X #HLK2 #H
  elim (lift_total V0 0 (i0 +1)) #V #HV0
  elim (lsubc_inv_pair2 … H) -H *
  [ #K2 #HK20 #H destruct
    generalize in match HLK2; generalize in match I; -HLK2 -I * #HLK2
    [ @(s4 … HB … ◊ … HV0 HLK2)
      @(IHB … HL20) [2: /2 width=6/ | skip ] 
      | skip 
      ]
(⇧*[des0]V1≡V0) → (⇧[O,i0+1]V0≡V) → (@[i]des≡i0) → (des+1▭i+1≡des0+1) →
⇧*[{O,i+1}::des]V1≡V) 
    
      Theorem lift1_free: (hds:?; i:?; t:?)
                          (lift1 hds (lift (S i) (0) t)) =
                          (lift (S (trans hds i)) (0) (lift1 (ptrans hds i) t)).
    
    
    
    
    | @(s2 … HB … ◊) // /2 width=3/
    ]
  | #K2 #V2 #A2 #HV2 #HV0 #HK20 #H1 #H2 destruct 
  ]
| #L #V #T #B #A #_ #_ #IHB #IHA #L0 #des #HL0 #X #H #L2 #HL20
  elim (lifts_inv_bind1 … H) -H #V0 #T0 #HV0 #HT0 #H destruct
  lapply (aacr_acr … H1RP H2RP A) #HA
  lapply (aacr_acr … H1RP H2RP B) #HB
  lapply (s1 … HB) -HB #HB
  @(s5 … HA … ◊ ◊) // /3 width=5/
| #L #W #T #B #A #_ #_ #IHB #IHA #L0 #des #HL0 #X #H #L2 #HL02
  elim (lifts_inv_bind1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
  @(aacr_abst  … H1RP H2RP)
  [ lapply (aacr_acr … H1RP H2RP B) #HB
    @(s1 … HB) /2 width=5/
  | #L3 #V3 #T3 #des3 #HL32 #HT03 #HB
    elim (lifts_total des3 W0) #W2 #HW02
    elim (ldrops_lsubc_trans … HL32 … HL02) -L2 #L2 #HL32 #HL20
    @(IHA (L2. 𝕓{Abst} W2) … (des + 1 @ des3 + 1))
    /2 width=3/ /3 width=5/ /4 width=6/
  ]
| #L #V #T #B #A #_ #_ #IHB #IHA #L0 #des #HL0 #X #H #L2 #HL20
  elim (lifts_inv_flat1 … H) -H #V0 #T0 #HV0 #HT0 #H destruct
  /3 width=10/
| #L #V #T #A #_ #_ #IH1A #IH2A #L0 #des #HL0 #X #H #L2 #HL20
  elim (lifts_inv_flat1 … H) -H #V0 #T0 #HV0 #HT0 #H destruct
  lapply (aacr_acr … H1RP H2RP A) #HA
  lapply (s1 … HA) #H
  @(s6 … HA … ◊) /2 width=5/ /3 width=5/
]
*)
lemma acp_aaa: ∀RR,RS,RP. acp RR RS RP → acr RR RS RP (λL,T. RP L T) →
               ∀L,T,A. L ⊢ T ÷ A → RP L T.
#RR #RS #RP #H1RP #H2RP #L #T #A #HT
lapply (aacr_acr … H1RP H2RP A) #HA
@(s1 … HA) /2 width=8/
qed.
