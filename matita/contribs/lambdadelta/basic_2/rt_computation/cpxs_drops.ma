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

include "basic_2/relocation/drops_lstar.ma".
include "basic_2/rt_transition/cpx_drops.ma".
include "basic_2/rt_computation/cpxs.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS ************)

(* Advanced properties ******************************************************)

lemma cpxs_delta: ∀h,I,G,K,V1,V2. ⦃G, K⦄ ⊢ V1 ⬈*[h] V2 →
                  ∀W2. ⬆*[1] V2 ≡ W2 → ⦃G, K.ⓑ{I}V1⦄ ⊢ #0 ⬈*[h] W2.
#h #I #G #K #V1 #V2 #H @(cpxs_ind … H) -V2
[ /3 width=3 by cpx_cpxs, cpx_delta/
| #V #V2 #_ #HV2 #IH #W2 #HVW2
  elim (lifts_total V (𝐔❴1❵)) #W #HVW
  elim (cpx_lifts … HV2 (Ⓣ) … (K.ⓑ{I}V1) … HVW) -HV2
  [ #V0 #HV20 <(lifts_mono … HVW2 … HV20) -V2 -V0 /3 width=3 by cpxs_strap1/
  | /3 width=1 by drops_refl, drops_drop/
  ]
]
qed.

lemma cpxs_lref: ∀h,I,G,K,V,T,i. ⦃G, K⦄ ⊢ #i ⬈*[h] T →
                 ∀U. ⬆*[1] T ≡ U → ⦃G, K.ⓑ{I}V⦄ ⊢ #⫯i ⬈*[h] U.
#h #I #G #K #V #T #i #H @(cpxs_ind … H) -T
[ /3 width=3 by cpx_cpxs, cpx_lref/
| #T0 #T #_ #HT2 #IH #U #HTU
  elim (lifts_total T0 (𝐔❴1❵)) #U0 #HTU0
  elim (cpx_lifts … HT2 (Ⓣ) … (K.ⓑ{I}V) … HTU0) -HT2
  [ #X #HTX <(lifts_mono … HTU … HTX) -T -X /3 width=3 by cpxs_strap1/
  | /3 width=1 by drops_refl, drops_drop/
  ]
]
qed.

(* Basic_2A1: was: cpxs_delta *)
lemma cpxs_delta_drops: ∀h,I,G,L,K,V1,V2,i.
                        ⬇*[i] L ≡ K.ⓑ{I}V1 → ⦃G, K⦄ ⊢ V1 ⬈*[h] V2 →
                        ∀W2. ⬆*[⫯i] V2 ≡ W2 → ⦃G, L⦄ ⊢ #i ⬈*[h] W2.
#h #I #G #L #K #V1 #V2 #i #HLK #H @(cpxs_ind … H) -V2
[ /3 width=7 by cpx_cpxs, cpx_delta_drops/
| #V #V2 #_ #HV2 #IH #W2 #HVW2
  elim (lifts_total V (𝐔❴⫯i❵)) #W #HVW
  elim (cpx_lifts … HV2 (Ⓣ) … L … HVW) -HV2
  [ #V0 #HV20 <(lifts_mono … HVW2 … HV20) -V2 -V0 /3 width=3 by cpxs_strap1/
  | /2 width=3 by drops_isuni_fwd_drop2/
  ]
]
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpxs_inv_zero1: ∀h,G,L,T2. ⦃G, L⦄ ⊢ #0 ⬈*[h] T2 →
                      T2 = #0 ∨
                      ∃∃I,K,V1,V2. ⦃G, K⦄ ⊢ V1 ⬈*[h] V2 & ⬆*[1] V2 ≡ T2 &
                                   L = K.ⓑ{I}V1.
#h #G #L #T2 #H @(cpxs_ind … H) -T2 /2 width=1 by or_introl/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpx_inv_zero1 … HT2) -HT2 /2 width=1 by or_introl/
  * /4 width=7 by cpx_cpxs, ex3_4_intro, or_intror/
| * #I #K #V1 #T1 #HVT1 #HT1 #H destruct
  elim (cpx_inv_lifts … HT2 (Ⓣ) … K … HT1) -T
  /4 width=7 by cpxs_strap1, drops_refl, drops_drop, ex3_4_intro, or_intror/
]
qed-.

lemma cpxs_inv_lref1: ∀h,G,L,T2,i. ⦃G, L⦄ ⊢ #⫯i ⬈*[h] T2 →
                      T2 = #(⫯i) ∨
                      ∃∃I,K,V,T. ⦃G, K⦄ ⊢ #i ⬈*[h] T & ⬆*[1] T ≡ T2 & L = K.ⓑ{I}V.
#h #G #L #T2 #i #H @(cpxs_ind … H) -T2 /2 width=1 by or_introl/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpx_inv_lref1 … HT2) -HT2 /2 width=1 by or_introl/
  * /4 width=7 by cpx_cpxs, ex3_4_intro, or_intror/
| * #I #K #V1 #T1 #Hi #HT1 #H destruct
  elim (cpx_inv_lifts … HT2 (Ⓣ) … K … HT1) -T
  /4 width=7 by cpxs_strap1, drops_refl, drops_drop, ex3_4_intro, or_intror/
]
qed-.

(* Basic_2A1: was: cpxs_inv_lref1 *)
lemma cpxs_inv_lref1_drops: ∀h,G,L,T2,i. ⦃G, L⦄ ⊢ #i ⬈*[h] T2 →
                            T2 = #i ∨
                            ∃∃I,K,V1,T1. ⬇*[i] L ≡ K.ⓑ{I}V1 & ⦃G, K⦄ ⊢ V1 ⬈*[h] T1 &
                                         ⬆*[⫯i] T1 ≡ T2.
#h #G #L #T2 #i #H @(cpxs_ind … H) -T2 /2 width=1 by or_introl/
#T #T2 #_ #HT2 *
[ #H destruct
  elim (cpx_inv_lref1_drops … HT2) -HT2 /2 width=1 by or_introl/
  * /4 width=7 by cpx_cpxs, ex3_4_intro, or_intror/
| * #I #K #V1 #T1 #HLK #HVT1 #HT1
  lapply (drops_isuni_fwd_drop2 … HLK) // #H0LK
  elim (cpx_inv_lifts … HT2 … H0LK … HT1) -H0LK -T
  /4 width=7 by cpxs_strap1, ex3_4_intro, or_intror/
]
qed-.

(* Properties with generic relocation ***************************************)

(* Basic_2A1: includes: cpxs_lift *)
lemma cpxs_lifts: ∀h,G. d_liftable2 (cpxs h G).
/3 width=10 by cpx_lifts, cpxs_strap1, d2_liftable_LTC/ qed-.

(* Inversion lemmas with generic relocation *********************************)

(* Basic_2A1: includes: cpxs_inv_lift1 *)
lemma cpxs_inv_lifts: ∀h,G. d_deliftable2_sn (cpxs h G).
/3 width=6 by d2_deliftable_sn_LTC, cpx_inv_lifts/ qed-.