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

include "static_2/static/aaa_aaa.ma".
include "static_2/static/lsubc_drops.ma".

(* GENERIC COMPUTATION PROPERTIES *******************************************)

(* Main properties **********************************************************)

(* Basic_1: was: sc3_arity_csubc *)
theorem acr_aaa_lsubc_lifts (RR) (RS) (RP):
        gcp RR RS RP → gcr RR RS RP RP →
        ∀G,L1,T,A. ❨G,L1❩ ⊢ T ⁝ A → ∀b,f,L0. ⇩*[b,f] L0 ≘ L1 →
        ∀T0. ⇧*[f] T ≘ T0 → ∀L2. G ⊢ L2 ⫃[RP] L0 →
        ❨G,L2,T0❩ ϵ ⟦A⟧[RP].
#RR #RS #RP #H1RP #H2RP #G #L1 #T @(fqup_wf_ind_eq (Ⓣ) … G L1 T) -G -L1 -T
#Z #Y #X #IH #G #L1 * [ * | * [ #p ] * ]
[ #s #HG #HL #HT #A #HA #b #f #L0 #HL01 #X0 #H0 #L2 #HL20 destruct -IH
  lapply (aaa_inv_sort … HA) -HA #H destruct
  >(lifts_inv_sort1 … H0) -H0
  lapply (acr_gcr … H1RP H2RP (⓪)) #HAtom
  lapply (s2 … HAtom G L2 (Ⓔ)) /3 width=7 by cp1, simple_atom/
| #i #HG #HL #HT #A #HA #b #f #L0 #HL01 #X0 #H0 #L2 #HL20 destruct
  elim (aaa_inv_lref_drops … HA) -HA #I #K1 #V1 #HLK1 #HKV1
  elim (lifts_inv_lref1 … H0) -H0 #j #Hf #H destruct
  lapply (acr_gcr … H1RP H2RP A) #HA
  lapply (drops_trans … HL01 … HLK1 ??) -HL01 [3: |*: // ] #H
  elim (drops_split_trans … H) -H [ |*: /2 width=6 by pr_after_nat_uni/ ] #Y #HLK0 #HY
  lapply (drops_tls_at … Hf … HY) -Hf -HY #HY
  elim (drops_inv_skip2 … HY) -HY #Z #K0 #HK01 #HZ #H destruct
  elim (liftsb_inv_pair_sn … HZ) -HZ #V0 #HV10 #H destruct
  elim (lifts_total V0 (𝐔❨↑j❩)) #V #HV0
  elim (lsubc_drops_trans_isuni … HL20 … HLK0) -HL20 -HLK0 // #Y #HLK2 #H
  elim (lsubc_inv_bind2 … H) -H *
  [ #K2 #HK20 #H destruct
    lapply (drops_isuni_fwd_drop2 … HLK2) // #HLK2b
    lapply (s5 … HA ? G ? ? (Ⓔ) … HV0 ?) -HA
    /4 width=11 by acr_lifts, fqup_lref, drops_inv_gen/
  | #K2 #V2 #W2 #B #HKV2 #HK2V0 #HKV0B #_ #H1 #H2 destruct -IH -HLK1
    lapply (drops_isuni_fwd_drop2 … HLK2) // #HLK2b
    lapply (aaa_lifts … HKV1 … HK01 … HV10) -HKV1 -HK01 -HV10 #HKV0A
    lapply (aaa_mono … HKV0B … HKV0A) #H destruct -HKV0B -HKV0A
    elim (lifts_total V2 (𝐔❨↑j❩)) #V3 #HV23
    lapply (s5 … HA … G … (Ⓔ) … (ⓝW2.V2) (ⓝV.V3) ????)
    [3: |*: /2 width=9 by drops_inv_gen, lifts_flat/ ] -HLK2
    lapply (s7 … HA G L2 (Ⓔ)) -HA /3 width=7 by acr_lifts/
  ]
| #l #HG #HL #HT #A #HA #b #f #L0 #HL01 #X0 #H0 #L2 #HL20 destruct -IH
  elim (aaa_inv_gref … HA)
| #V #T #HG #HL #HT #A #HA #b #f #L0 #HL01 #X0 #H0 #L2 #HL20 destruct
  elim (aaa_inv_abbr … HA) -HA #B #HV #HT
  elim (lifts_inv_bind1 … H0) -H0 #V0 #T0 #HV0 #HT0 #H destruct
  lapply (acr_gcr … H1RP H2RP A) #HA
  lapply (acr_gcr … H1RP H2RP B) #HB
  lapply (s1 … HB) -HB #HB
  lapply (s6 … HA G L2 (Ⓔ) (Ⓔ)) /5 width=10 by lsubc_bind, liftsv_nil, drops_skip, ext2_pair/
| #W #T #HG #HL #HT #Z0 #HA #b #f #L0 #HL01 #X0 #H0 #L2 #HL20 destruct
  elim (aaa_inv_abst … HA) -HA #B #A #HW #HT #H destruct
  elim (lifts_inv_bind1 … H0) -H0 #W0 #T0 #HW0 #HT0 #H destruct
  @(acr_abst  … H1RP H2RP) /2 width=10 by/
  #b3 #f3 #L3 #V3 #W3 #T3 #HL32 #HW03 #HT03 #H1B #H2B
  elim (drops_lsubc_trans … H1RP … HL32 … HL20) -L2 #L2 #HL32 #HL20
  lapply (aaa_lifts … HW … (f3∘f) L2 … W3 ?) -HW
  [4: |*: /2 width=8 by drops_trans, lifts_trans/ ] #HW3
  @(IH … ((⫯f3)∘⫯f) … (L2. ⓛW3)) -IH
  /4 width=12 by lsubc_beta, drops_trans, drops_skip, lifts_trans, ext2_pair/
| #V #T #HG #HL #HT #A #HA #b #f #L0 #HL01 #X0 #H0 #L2 #HL20 destruct
  elim (aaa_inv_appl … HA) -HA #B #HV #HT
  elim (lifts_inv_flat1 … H0) -H0 #V0 #T0 #HV0 #HT0 #H destruct
  lapply (IH … HT … HL01 … HT0 … HL20) -HT -HT0
  /3 width=10 by drops_refl, lifts_refl/
| #W #T #HG #HL #HT #A #HA #b #f #L0 #HL01 #X0 #H0 #L2 #HL20 destruct
  elim (aaa_inv_cast … HA) -HA #HW #HT
  elim (lifts_inv_flat1 … H0) -H0 #W0 #T0 #HW0 #HT0 #H destruct
  lapply (acr_gcr … H1RP H2RP A) #HA
  lapply (s7 … HA G L2 (Ⓔ)) /3 width=10 by/
]
qed.

(* Basic_1: was: sc3_arity *)
lemma acr_aaa (RR) (RS) (RP):
      gcp RR RS RP → gcr RR RS RP RP →
      ∀G,L,T,A. ❨G,L❩ ⊢ T ⁝ A → ❨G,L,T❩ ϵ ⟦A⟧[RP].
/3 width=9 by drops_refl, lifts_refl, acr_aaa_lsubc_lifts/ qed.

lemma gcr_aaa (RR) (RS) (RP):
      gcp RR RS RP → gcr RR RS RP RP →
      ∀G,L,T,A. ❨G,L❩ ⊢ T ⁝ A → RP G L T.
#RR #RS #RP #H1RP #H2RP #G #L #T #A #HT
lapply (acr_gcr … H1RP H2RP A) #HA
@(s1 … HA) /2 width=4 by acr_aaa/
qed.
