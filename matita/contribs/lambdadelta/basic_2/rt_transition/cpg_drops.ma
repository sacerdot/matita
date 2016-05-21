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
include "basic_2/rt_transition/cpg.ma".

(* COUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Advanced properties ******************************************************)

lemma cpg_delta_drops: ∀c,h,G,K,V,V2,i,L,T2. ⬇*[i] L ≡ K.ⓓV → ⦃G, K⦄ ⊢ V ➡[c, h] V2 →
                       ⬆*[⫯i] V2 ≡ T2 →  ⦃G, L⦄ ⊢ #i ➡[c, h] T2.
#c #h #G #K #V #V2 #i elim i -i
[ #L #T2 #HLK lapply (drops_fwd_isid … HLK ?) // #H destruct /3 width=3 by cpg_delta/
| #i #IH #L0 #T0 #H0 #HV2 #HVT2
  elim (drops_inv_succ … H0) -H0 #I #L #V0 #HLK #H destruct
  elim (lifts_split_trans … HVT2 (𝐔❴⫯i❵) (𝐔❴1❵) ?) -HVT2 /3 width=3 by cpg_lref/
]
qed.

lemma cpg_ell_drops: ∀c,h,G,K,V,V2,i,L,T2. ⬇*[i] L ≡ K.ⓛV → ⦃G, K⦄ ⊢ V ➡[c, h] V2 →
                     ⬆*[⫯i] V2 ≡ T2 →  ⦃G, L⦄ ⊢ #i ➡[(↓c)+𝟘𝟙, h] T2.
#c #h #G #K #V #V2 #i elim i -i
[ #L #T2 #HLK lapply (drops_fwd_isid … HLK ?) // #H destruct /3 width=3 by cpg_ell/
| #i #IH #L0 #T0 #H0 #HV2 #HVT2
  elim (drops_inv_succ … H0) -H0 #I #L #V0 #HLK #H destruct
  elim (lifts_split_trans … HVT2 (𝐔❴⫯i❵) (𝐔❴1❵) ?) -HVT2 /3 width=3 by cpg_lref/
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpg_inv_lref1_drops: ∀c,h,G,i,L,T2. ⦃G, L⦄ ⊢ #i ➡[c, h] T2 →
                           ∨∨ T2 = #i ∧ c = 𝟘𝟘
                            | ∃∃cV,K,V,V2. ⬇*[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V ➡[cV, h] V2 &
                                           ⬆*[⫯i] V2 ≡ T2 & c = cV
                            | ∃∃cV,K,V,V2. ⬇*[i] L ≡ K.ⓛV & ⦃G, K⦄ ⊢ V ➡[cV, h] V2 &
                                           ⬆*[⫯i] V2 ≡ T2 & c = (↓cV) + 𝟘𝟙.
#c #h #G #i elim i -i
[ #L #T2 #H elim (cpg_inv_zero1 … H) -H * /3 width=1 by or3_intro0, conj/
  /4 width=8 by drops_refl, ex4_4_intro, or3_intro2, or3_intro1/
| #i #IH #L #T2 #H elim (cpg_inv_lref1 … H) -H * /3 width=1 by or3_intro0, conj/
  #I #K #V #V2 #H #HVT2 #H0 destruct elim (IH … H) -IH -H
  [ * #H1 #H2 destruct lapply (lifts_inv_lref1_uni … HVT2) -HVT2 #H destruct /3 width=1 by or3_intro0, conj/ ] *
  #cV #L #W #W2 #HKL #HW2 #HWV2 #H destruct
  lapply (lifts_trans … HWV2 … HVT2 ??) -V2
  /4 width=8 by drops_drop, ex4_4_intro, or3_intro2, or3_intro1/
]
qed-.

lemma cpg_inv_atom1_drops: ∀c,h,I,G,L,T2. ⦃G, L⦄ ⊢ ⓪{I} ➡[c, h] T2 →
                           ∨∨ T2 = ⓪{I} ∧ c = 𝟘𝟘
                            | ∃∃s. T2 = ⋆(next h s) & I = Sort s & c = 𝟘𝟙
                            | ∃∃cV,i,K,V,V2. ⬇*[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V ➡[cV, h] V2 &
                                             ⬆*[⫯i] V2 ≡ T2 & I = LRef i & c = cV
                            | ∃∃cV,i,K,V,V2. ⬇*[i] L ≡ K.ⓛV & ⦃G, K⦄ ⊢ V ➡[cV, h] V2 &
                                             ⬆*[⫯i] V2 ≡ T2 & I = LRef i & c = (↓cV) + 𝟘𝟙.
#c #h * #n #G #L #T2 #H
[ elim (cpg_inv_sort1 … H) -H *
  /3 width=3 by or4_intro0, or4_intro1, ex3_intro, conj/
| elim (cpg_inv_lref1_drops … H) -H *
  /3 width=10 by or4_intro0, or4_intro2, or4_intro3, ex5_5_intro, conj/
| elim (cpg_inv_gref1 … H) -H
  /3 width=1 by or4_intro0, conj/
]
qed-.

(* Properties with generic slicing for local environments *******************)

lemma cpg_lifts: ∀c,h,G. d_liftable2 (cpg h c G).
#c #h #G #K #T generalize in match c; -c
@(fqup_wf_ind_eq … G K T) -G -K -T #G0 #K0 #T0 #IH #G #K * *
[ #s #HG #HK #HT #c #X2 #H2 #b #f #L #HLK #X1 #H1 destruct -IH
  lapply (lifts_inv_sort1 … H1) -H1 #H destruct
  elim (cpg_inv_sort1 … H2) -H2 * #H1 #H2 destruct
  /2 width=3 by cpg_atom, cpg_ess, lifts_sort, ex2_intro/
| #i1 #HG #HK #HT #c #T2 #H2 #b #f #L #HLK #X1 #H1 destruct
  elim (cpg_inv_lref1_drops … H2) -H2 *
  [ #H1 #H2 destruct /2 width=3 by ex2_intro/ ]
  #cV #K0 #V #V2 #HK0 #HV2 #HVT2 #H destruct
  elim (lifts_inv_lref1 … H1) -H1 #i2 #Hf #H destruct
  lapply (drops_trans … HLK … HK0 ??) -HLK [3,6: |*: // ] #H
  elim (drops_split_trans … H) -H [1,6: |*: /2 width=6 by after_uni_dx/ ] #Y #HL0 #HY
  lapply (drops_inv_tls_at … Hf … HY) -HY #HY
  elim (drops_inv_skip2 … HY) -HY #L0 #W #HLK0 #HVW #H destruct
  elim (IH … HV2 … HLK0 … HVW) -IH /2 width=2 by fqup_lref/ -K -K0 -V #W2 #HVW2 #HW2
  elim (lifts_total W2 (𝐔❴⫯i2❵)) #U2 #HWU2
  lapply (lifts_trans … HVW2 … HWU2 ??) -HVW2 [3,6: |*: // ] #HVU2
  lapply (lifts_conf … HVT2 … HVU2 f ?) -V2 [1,3: /2 width=3 by after_uni_succ_sn/ ]
  /4 width=8 by cpg_ell_drops, cpg_delta_drops, drops_inv_gen, ex2_intro/
| #l #HG #HK #HT #c #X2 #H2 #b #f #L #HLK #X1 #H1 destruct -IH
  lapply (lifts_inv_gref1 … H1) -H1 #H destruct
  elim (cpg_inv_gref1 … H2) -H2 #H1 #H2 destruct
  /2 width=3 by cpg_atom, lifts_gref, ex2_intro/
| #p #I #V1 #T1 #HG #HK #HT #c #X2 #H2 #b #f #L #HLK #X1 #H1 destruct
  elim (lifts_inv_bind1 … H1) -H1 #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (cpg_inv_bind1 … H2) -H2 *
  [ #cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct
    elim (IH … HV12 … HLK … HVW1) -HV12 //
    elim (IH … HT12 … HTU1) -IH -HT12 -HTU1 [ |*: /3 width=3 by drops_skip/ ]
    /3 width=5 by cpg_bind, lifts_bind, ex2_intro/
  | #cT #T2 #HT12 #HXT2 #H1 #H2 #H3 destruct
    elim (IH … HT12 … HTU1) -IH -HT12 -HTU1 [ |*: /3 width=3 by drops_skip/ ] #U2 #HTU2 #HU12
    lapply (lifts_trans … HXT2 … HTU2 ??) -T2 [3: |*: // ] #HXU2
    elim (lifts_split_trans … HXU2 f (𝐔❴⫯O❵)) [2: /2 width=1 by after_uni_one_dx/ ]
    /3 width=5 by cpg_zeta, ex2_intro/
  ]
| #I #V1 #T1 #HG #HK #HT #c #X2 #H2 #b #f #L #HLK #X1 #H1 destruct
  elim (lifts_inv_flat1 … H1) -H1 #W1 #U1 #HVW1 #HTU1 #H destruct
  elim (cpg_inv_flat1 … H2) -H2 *
  [ #cV #cT #V2 #T2 #HV12 #HT12 #H1 #H2 destruct
    elim (IH … HV12 … HLK … HVW1) -HV12 -HVW1 //
    elim (IH … HT12 … HLK … HTU1) -IH -HT12 -HLK -HTU1 //
    /3 width=5 by cpg_flat, lifts_flat, ex2_intro/
  | #cT #HT12 #H1 #H2 destruct
    elim (IH … HT12 … HLK … HTU1) -IH -HT12 -HLK -HTU1 //
    /3 width=3 by cpg_eps, ex2_intro/
  | #cV #HV12 #H1 #H2 destruct
    elim (IH … HV12 … HLK … HVW1) -IH -HV12 -HLK -HVW1 //
    /3 width=3 by cpg_ee, ex2_intro/
  | #cV #cY #cT #a #V2 #Y1 #Y2 #T0 #T2 #HV12 #HY12 #HT12 #H1 #H2 #H3 #H4 destruct
    elim (lifts_inv_bind1 … HTU1) -HTU1 #Z1 #U0 #HYZ1 #HTU1 #H destruct
    elim (IH … HV12 … HLK … HVW1) -HV12 -HVW1 //
    elim (IH … HY12 … HLK … HYZ1) -HY12 //
    elim (IH … HT12 … HTU1) -IH -HT12 -HTU1 [ |*: /3 width=3 by drops_skip/ ]
    /4 width=7 by cpg_beta, lifts_bind, lifts_flat, ex2_intro/
  | #cV #cY #cT #a #V2 #V20 #Y1 #Y2 #T0 #T2 #HV12 #HV20 #HY12 #HT12 #H1 #H2 #H3 #H4 destruct
    elim (lifts_inv_bind1 … HTU1) -HTU1 #Z1 #U0 #HYZ1 #HTU1 #H destruct
    elim (IH … HV12 … HLK … HVW1) -HV12 -HVW1 // #W2 #HVW2 #HW12
    elim (IH … HY12 … HLK … HYZ1) -HY12 //
    elim (IH … HT12 … HTU1) -IH -HT12 -HTU1 [ |*: /3 width=3 by drops_skip/ ]
    elim (lifts_total W2 (𝐔❴1❵)) #W20 #HW20
    lapply (lifts_trans … HVW2 … HW20 ??) -HVW2 [3: |*: // ] #H
    lapply (lifts_conf … HV20 … H (↑f) ?) -V2 /2 width=3 by after_uni_one_sn/
    /4 width=9 by cpg_theta, lifts_bind, lifts_flat, ex2_intro/
  ]
]
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

lemma cpg_inv_lifts1: ∀c,h,G. d_deliftable2_sn (cpg h c G).
#c #h #G #L #U generalize in match c; -c
@(fqup_wf_ind_eq … G L U) -G -L -U #G0 #L0 #U0 #IH #G #L * *
[ #s #HG #HL #HU #c #X2 #H2 #b #f #K #HLK #X1 #H1 destruct -IH
  lapply (lifts_inv_sort2 … H1) -H1 #H destruct
  elim (cpg_inv_sort1 … H2) -H2 * #H1 #H2 destruct
  /2 width=3 by cpg_atom, cpg_ess, lifts_sort, ex2_intro/
| #i2 #HG #HL #HU #c #U2 #H2 #b #f #K #HLK #X1 #H1 destruct
  elim (cpg_inv_lref1_drops … H2) -H2 *
  [ #H1 #H2 destruct /2 width=3 by ex2_intro/ ]
  #cW #L0 #W #W2 #HL0 #HW2 #HWU2 #H destruct
  elim (lifts_inv_lref2 … H1) -H1 #i1 #Hf #H destruct
  lapply (drops_split_div … HLK (𝐔❴i1❵) ???) -HLK [4,8: * |*: // ] #Y0 #HK0 #HLY0
  lapply (drops_conf … HL0 … HLY0 ??) -HLY0 [3,6: |*: /2 width=6 by after_uni_dx/ ] #HLY0
  lapply (drops_inv_tls_at … Hf … HLY0) -HLY0 #HLY0
  elim (drops_inv_skip1 … HLY0) -HLY0 #K0 #V #HLK0 #HVW #H destruct
  elim (IH … HW2 … HLK0 … HVW) -IH /2 width=2 by fqup_lref/ -L -L0 -W #V2 #HVW2 #HV2
  lapply (lifts_trans … HVW2 … HWU2 ??) -W2 [3,6: |*: // ] #HVU2
  elim (lifts_split_trans … HVU2 ? f) -HVU2 [1,4: |*: /2 width=4 by after_uni_succ_sn/ ]
  /4 width=8 by cpg_ell_drops, cpg_delta_drops, drops_inv_F, ex2_intro/
| #l #HG #HL #HU #c #X2 #H2 #b #f #K #HLK #X1 #H1 destruct -IH
  lapply (lifts_inv_gref2 … H1) -H1 #H destruct
  elim (cpg_inv_gref1 … H2) -H2 #H1 #H2 destruct
  /2 width=3 by cpg_atom, lifts_gref, ex2_intro/
| #p #I #W1 #U1 #HG #HL #HU #c #X2 #H2 #b #f #K #HLK #X1 #H1 destruct
  elim (lifts_inv_bind2 … H1) -H1 #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (cpg_inv_bind1 … H2) -H2 *
  [ #cW #cU #W2 #U2 #HW12 #HU12 #H1 #H2 destruct
    elim (IH … HW12 … HLK … HVW1) -HW12 //
    elim (IH … HU12 … HTU1) -IH -HU12 -HTU1 [ |*: /3 width=3 by drops_skip/ ]
    /3 width=5 by cpg_bind, lifts_bind, ex2_intro/
  | #cU #U2 #HU12 #HXU2 #H1 #H2 #H3 destruct
    elim (IH … HU12 … HTU1) -IH -HU12 -HTU1 [ |*: /3 width=3 by drops_skip/ ] #T2 #HTU2 #HT12
    elim (lifts_div4_one … HTU2 … HXU2) -U2 /3 width=5 by cpg_zeta, ex2_intro/
  ]
| #I #W1 #U1 #HG #HL #HU #c #X2 #H2 #b #f #K #HLK #X1 #H1 destruct
  elim (lifts_inv_flat2 … H1) -H1 #V1 #T1 #HVW1 #HTU1 #H destruct
  elim (cpg_inv_flat1 … H2) -H2 *
  [ #cW #cU #W2 #U2 #HW12 #HU12 #H1 #H2 destruct
    elim (IH … HW12 … HLK … HVW1) -HW12 -HVW1 //
    elim (IH … HU12 … HLK … HTU1) -IH -HU12 -HLK -HTU1 //
    /3 width=5 by cpg_flat, lifts_flat, ex2_intro/
  | #cU #HU12 #H1 #H2 destruct
    elim (IH … HU12 … HLK … HTU1) -IH -HU12 -HLK -HTU1 //
    /3 width=3 by cpg_eps, ex2_intro/
  | #cW #HW12 #H1 #H2 destruct
    elim (IH … HW12 … HLK … HVW1) -IH -HW12 -HLK -HVW1 //
    /3 width=3 by cpg_ee, ex2_intro/
  | #cW #cZ #cU #a #W2 #Z1 #Z2 #U0 #U2 #HW12 #HZ12 #HU12 #H1 #H2 #H3 #H4 destruct
    elim (lifts_inv_bind2 … HTU1) -HTU1 #Y1 #T0 #HYZ1 #HTU1 #H destruct
    elim (IH … HW12 … HLK … HVW1) -HW12 -HVW1 //
    elim (IH … HZ12 … HLK … HYZ1) -HZ12 //
    elim (IH … HU12 … HTU1) -IH -HU12 -HTU1 [ |*: /3 width=3 by drops_skip/ ]
    /4 width=7 by cpg_beta, lifts_bind, lifts_flat, ex2_intro/
  | #cW #cZ #cU #a #W2 #W20 #Z1 #Z2 #U0 #U2 #HW12 #HW20 #HZ12 #HU12 #H1 #H2 #H3 #H4 destruct
    elim (lifts_inv_bind2 … HTU1) -HTU1 #Y1 #T0 #HYZ1 #HTU1 #H destruct
    elim (IH … HW12 … HLK … HVW1) -HW12 -HVW1 // #V2 #HVW2 #HV12
    elim (IH … HZ12 … HLK … HYZ1) -HZ12 //
    elim (IH … HU12 … HTU1) -IH -HU12 -HTU1 [ |*: /3 width=3 by drops_skip/ ]
    lapply (lifts_trans … HVW2 … HW20 ??) -W2 [3: |*: // ] #H
    elim (lifts_split_trans … H ? (↑f)) -H [ |*: /2 width=3 by after_uni_one_sn/ ]
    /4 width=9 by cpg_theta, lifts_bind, lifts_flat, ex2_intro/
  ]
]
qed-.
