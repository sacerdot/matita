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

include "basic_2/multiple/lifts_lifts.ma".
include "basic_2/multiple/drops_drops.ma".
include "basic_2/static/aaa_lifts.ma".
include "basic_2/static/aaa_aaa.ma".
include "basic_2/computation/lsubc_drops.ma".

(* GENERIC COMPUTATION PROPERTIES *******************************************)

(* Main properties **********************************************************)

(* Basic_1: was: sc3_arity_csubc *)
theorem acr_aaa_csubc_lifts: ∀RR,RS,RP.
                             gcp RR RS RP → gcr RR RS RP RP →
                             ∀G,L1,T,A. ⦃G, L1⦄ ⊢ T ⁝ A → ∀L0,des. ⇩*[Ⓕ, des] L0 ≡ L1 →
                             ∀T0. ⇧*[des] T ≡ T0 → ∀L2. G ⊢ L2 ⫃[RP] L0 →
                             ⦃G, L2, T0⦄ ϵ[RP] 〚A〛.
#RR #RS #RP #H1RP #H2RP #G #L1 #T #A #H elim H -G -L1 -T -A
[ #G #L #k #L0 #des #HL0 #X #H #L2 #HL20
  >(lifts_inv_sort1 … H) -H
  lapply (acr_gcr … H1RP H2RP (⓪)) #HAtom
  @(s4 … HAtom … (◊)) //
| #I #G #L1 #K1 #V1 #B #i #HLK1 #HKV1B #IHB #L0 #des #HL01 #X #H #L2 #HL20
  lapply (acr_gcr … H1RP H2RP B) #HB
  elim (lifts_inv_lref1 … H) -H #i1 #Hi1 #H destruct
  lapply (drop_fwd_drop2 … HLK1) #HK1b
  elim (drops_drop_trans … HL01 … HLK1) #X #des1 #i0 #HL0 #H #Hi0 #Hdes1
  >(at_mono … Hi1 … Hi0) -i1
  elim (drops_inv_skip2 … Hdes1 … H) -des1 #K0 #V0 #des0 #Hdes0 #HK01 #HV10 #H destruct
  elim (lsubc_drop_O1_trans … HL20 … HL0) -HL0 #X #HLK2 #H
  elim (lsubc_inv_pair2 … H) -H *
  [ #K2 #HK20 #H destruct
    elim (lift_total V0 0 (i0 +1)) #V #HV0
    elim (lifts_lift_trans  … Hi0 … Hdes0 … HV10 … HV0) -HV10 #V2 #HV12 #HV2
    @(s5 … HB … (◊) … HV0 HLK2) /3 width=7 by drops_cons, lifts_cons/ (* Note: uses IHB HL20 V2 HV0 *)
  | -HLK1 -IHB -HL01 -HL20 -HK1b -Hi0 -Hdes0
    #K2 #V2 #A2 #HKV2A #H1KV0A #H2KV0A #_ #H1 #H2 destruct
    lapply (drop_fwd_drop2 … HLK2) #HLK2b
    lapply (aaa_lifts … HK01 … HV10 HKV1B) -HKV1B -HK01 -HV10 #HKV0B
    lapply (aaa_mono … H2KV0A … HKV0B) #H destruct -H2KV0A -HKV0B
    elim (lift_total V0 0 (i0 +1)) #V3 #HV03
    elim (lift_total V2 0 (i0 +1)) #V #HV2
    @(s5 … HB … (◊) … (ⓝV3.V) … HLK2) [2: /2 width=1 by lift_flat/ ]
    @(s7 … HB … (◊)) [ @(s0 … HB … HKV2A) // | @(s0 … HB … H1KV0A) // ]
  ]
| #a #G #L #V #T #B #A #_ #_ #IHB #IHA #L0 #des #HL0 #X #H #L2 #HL20
  elim (lifts_inv_bind1 … H) -H #V0 #T0 #HV0 #HT0 #H destruct
  lapply (acr_gcr … H1RP H2RP A) #HA
  lapply (acr_gcr … H1RP H2RP B) #HB
  lapply (s1 … HB) -HB #HB
  @(s6 … HA … (◊) (◊)) /3 width=5 by lsubc_pair, drops_skip, liftv_nil/
| #a #G #L #W #T #B #A #HLWB #_ #IHB #IHA #L0 #des #HL0 #X #H #L2 #HL02
  elim (lifts_inv_bind1 … H) -H #W0 #T0 #HW0 #HT0 #H destruct
  @(acr_abst  … H1RP H2RP) [ /2 width=5 by/ ]
  #L3 #V3 #W3 #T3 #des3 #HL32 #HW03 #HT03 #H1B #H2B
  elim (drops_lsubc_trans … H1RP H2RP … HL32 … HL02) -L2 #L2 #HL32 #HL20
  lapply (aaa_lifts … L2 W3 … (des @@ des3) … HLWB) -HLWB /2 width=4 by drops_trans, lifts_trans/ #HLW2B
  @(IHA (L2. ⓛW3) … (des + 1 @@ des3 + 1)) -IHA 
  /3 width=5 by lsubc_beta, drops_trans, drops_skip, lifts_trans/
| #G #L #V #T #B #A #_ #_ #IHB #IHA #L0 #des #HL0 #X #H #L2 #HL20
  elim (lifts_inv_flat1 … H) -H #V0 #T0 #HV0 #HT0 #H destruct
  /3 width=10 by drops_nil, lifts_nil/
| #G #L #V #T #A #_ #_ #IH1A #IH2A #L0 #des #HL0 #X #H #L2 #HL20
  elim (lifts_inv_flat1 … H) -H #V0 #T0 #HV0 #HT0 #H destruct
  lapply (acr_gcr … H1RP H2RP A) #HA
  @(s7 … HA … (◊)) /2 width=5 by/
]
qed.

(* Basic_1: was: sc3_arity *)
lemma acr_aaa: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
               ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → ⦃G, L, T⦄ ϵ[RP] 〚A〛.
/2 width=8 by drops_nil, lifts_nil, acr_aaa_csubc_lifts/ qed.

lemma gcr_aaa: ∀RR,RS,RP. gcp RR RS RP → gcr RR RS RP RP →
               ∀G,L,T,A. ⦃G, L⦄ ⊢ T ⁝ A → RP G L T.
#RR #RS #RP #H1RP #H2RP #G #L #T #A #HT
lapply (acr_gcr … H1RP H2RP A) #HA
@(s1 … HA) /2 width=4 by acr_aaa/
qed.
