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

include "basic_2/relocation/drops_drops.ma".
include "basic_2/s_computation/fqup_weight.ma".
include "basic_2/s_computation/fqup_drops.ma".
include "basic_2/static/aaa.ma".

(* ATONIC ARITY ASSIGNMENT ON TERMS *****************************************)

(* Advanced properties ******************************************************)

(* Basic_2A1: was: aaa_lref *)
lemma aaa_lref_drops: ∀I,G,K,V,B,i,L. ⬇*[i] L ≡ K.ⓑ{I}V → ⦃G, K⦄ ⊢ V ⁝ B → ⦃G, L⦄ ⊢ #i ⁝ B.
#I #G #K #V #B #i elim i -i
[ #L #H lapply (drops_fwd_isid … H ?) -H //
  #H destruct /2 width=1 by aaa_zero/
| #i #IH #L <uni_succ #H #HB lapply (drops_inv_pair2_isuni_next … H) -H // *
  #Z #Y #X #HY #H destruct /3 width=1 by aaa_lref/
]
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: was: aaa_inv_lref *)
lemma aaa_inv_lref_drops: ∀G,A,i,L. ⦃G, L⦄ ⊢ #i ⁝ A →
                          ∃∃I,K,V. ⬇*[i] L ≡ K.ⓑ{I}V & ⦃G, K⦄ ⊢ V ⁝ A.
#G #A #i elim i -i
[ #L #H elim (aaa_inv_zero … H) -H /3 width=5 by drops_refl, ex2_3_intro/
| #i #IH #L #H elim (aaa_inv_lref … H) -H
  #I #K #V #H #HA destruct elim (IH … HA) -IH -HA /3 width=5 by drops_drop, ex2_3_intro/
]
qed-.

(* Properties with generic slicing for local environments *******************)

(* Basic_2A1: includes: aaa_lift *)
(* Note: it should use drops_split_trans_pair2 *)
lemma aaa_lifts: ∀G,L1,T1,A. ⦃G, L1⦄ ⊢ T1 ⁝ A → ∀b,f,L2. ⬇*[b, f] L2 ≡ L1 →
                 ∀T2. ⬆*[f] T1 ≡ T2 → ⦃G, L2⦄ ⊢ T2 ⁝ A.
@fqup_wf_ind_eq #G0 #L0 #T0 #IH #G #L1 * *
[ #s #HG #HL #HT #A #H #b #f #L2 #HL21 #X #HX -b -IH
  lapply (aaa_inv_sort … H) -H #H destruct
  >(lifts_inv_sort1 … HX) -HX //
| #i1 #HG #HL #HT #A #H #b #f #L2 #HL21 #X #HX
  elim (aaa_inv_lref_drops … H) -H #J #K1 #V1 #HLK1 #HA
  elim (lifts_inv_lref1 … HX) -HX #i2 #Hf #H destruct
  lapply (drops_trans … HL21 … HLK1 ??) -HL21 [1,2: // ] #H
  elim (drops_split_trans … H) -H [ |*: /2 width=6 by after_uni_dx/ ] #Y #HLK2 #HY
  lapply (drops_tls_at … Hf … HY) -HY #HY -Hf
  elim (drops_inv_skip2 … HY) -HY #K2 #V2 #HK21 #HV12 #H destruct
  /4 width=12 by aaa_lref_drops, fqup_lref, drops_inv_gen/
| #l #HG #HL #HT #A #H #b #f #L2 #HL21 #X #HX -b -f -IH
  elim (aaa_inv_gref … H)
| #p * #V1 #T1 #HG #HL #HT #A #H #b #f #L2 #HL21 #X #HX
  [ elim (aaa_inv_abbr … H) -H #B #HB #HA
    elim (lifts_inv_bind1 …  HX) -HX #V2 #T2 #HV12 #HT12 #H destruct
    /4 width=9 by aaa_abbr, drops_skip/
  | elim (aaa_inv_abst … H) -H #B #A0 #HB #HA #H0
    elim (lifts_inv_bind1 …  HX) -HX #V2 #T2 #HV12 #HT12 #H destruct
    /4 width=8 by aaa_abst, drops_skip/
  ]
| * #V1 #T1 #HG #HL #HT #A #H #b #f #L2 #HL21 #X #HX
  [ elim (aaa_inv_appl … H) -H #B #HB #HA
    elim (lifts_inv_flat1 …  HX) -HX #V2 #T2 #HV12 #HT12 #H destruct
    /3 width=10 by aaa_appl/
  | elim (aaa_inv_cast … H) -H #H1A #H2A
    elim (lifts_inv_flat1 …  HX) -HX #V2 #T2 #HV12 #HT12 #H destruct
    /3 width=8 by aaa_cast/
  ]
]
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_2A1: includes: aaa_inv_lift *)
lemma aaa_inv_lifts: ∀G,L2,T2,A. ⦃G, L2⦄ ⊢ T2 ⁝ A → ∀b,f,L1. ⬇*[b, f] L2 ≡ L1 →
                     ∀T1. ⬆*[f] T1 ≡ T2 → ⦃G, L1⦄ ⊢ T1 ⁝ A.
@fqup_wf_ind_eq #G0 #L0 #T0 #IH #G #L2 * *
[ #s #HG #HL #HT #A #H #b #f #L1 #HL21 #X #HX -b -IH
  lapply (aaa_inv_sort … H) -H #H destruct
  >(lifts_inv_sort2 … HX) -HX //
| #i2 #HG #HL #HT #A #H #b #f #L1 #HL21 #X #HX
  elim (aaa_inv_lref_drops … H) -H #J #K2 #V2 #HLK2 #HA
  elim (lifts_inv_lref2 … HX) -HX #i1 #Hf #H destruct
  lapply (drops_split_div … HL21 (𝐔❴i1❵) ???) -HL21 [4: * |*: // ] #Y #HLK1 #HY
  lapply (drops_conf … HLK2 … HY ??) -HY [1,2: /2 width=6 by after_uni_dx/ ] #HY
  lapply (drops_tls_at … Hf … HY) -HY #HY -Hf
  elim (drops_inv_skip1 … HY) -HY #K1 #V1 #HK21 #HV12 #H destruct
  /4 width=12 by aaa_lref_drops, fqup_lref, drops_inv_F/
| #l #HG #HL #HT #A #H #b #f #L1 #HL21 #X #HX -IH -b -f
  elim (aaa_inv_gref … H)
| #p * #V2 #T2 #HG #HL #HT #A #H #b #f #L1 #HL21 #X #HX
  [ elim (aaa_inv_abbr … H) -H #B #HB #HA
    elim (lifts_inv_bind2 …  HX) -HX #V1 #T1 #HV12 #HT12 #H destruct
    /4 width=9 by aaa_abbr, drops_skip/
  | elim (aaa_inv_abst … H) -H #B #A0 #HB #HA #H0
    elim (lifts_inv_bind2 …  HX) -HX #V1 #T1 #HV12 #HT12 #H destruct
    /4 width=8 by aaa_abst, drops_skip/
  ]
| * #V2 #T2 #HG #HL #HT #A #H #b #f #L1 #HL21 #X #HX
  [ elim (aaa_inv_appl … H) -H #B #HB #HA
    elim (lifts_inv_flat2 …  HX) -HX #V1 #T1 #HV12 #HT12 #H destruct
    /3 width=10 by aaa_appl/
  | elim (aaa_inv_cast … H) -H #H1A #H2A
    elim (lifts_inv_flat2 …  HX) -HX #V1 #T1 #HV12 #HT12 #H destruct
    /3 width=8 by aaa_cast/
  ]
]
qed-.
