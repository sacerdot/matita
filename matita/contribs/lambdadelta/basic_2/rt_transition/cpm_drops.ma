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

include "basic_2/rt_transition/cpg_drops.ma".
include "basic_2/rt_transition/cpm.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS ***************)

(* Advanced properties ******************************************************)

(* Basic_1: includes: pr2_delta1 *)
(* Basic_2A1: includes: cpr_delta *)
lemma cpm_delta_drops: ∀n,h,G,L,K,V,V2,W2,i.
                       ⬇*[i] L ≡ K.ⓓV → ⦃G, K⦄ ⊢ V ➡[n, h] V2 →
                       ⬆*[⫯i] V2 ≡ W2 → ⦃G, L⦄ ⊢ #i ➡[n, h] W2.
#n #h #G #L #K #V #V2 #W2 #i #HLK *
/3 width=8 by cpg_delta_drops, ex2_intro/
qed.

lemma cpm_ell_drops: ∀n,h,G,L,K,V,V2,W2,i.
                     ⬇*[i] L ≡ K.ⓛV → ⦃G, K⦄ ⊢ V ➡[n, h] V2 →
                     ⬆*[⫯i] V2 ≡ W2 → ⦃G, L⦄ ⊢ #i ➡[⫯n, h] W2.
#n #h #G #L #K #V #V2 #W2 #i #HLK *
/3 width=8 by cpg_ell_drops, isrt_succ, ex2_intro/
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpm_inv_atom1_drops: ∀n,h,I,G,L,T2. ⦃G, L⦄ ⊢ ⓪{I} ➡[n, h] T2 →
                           ∨∨ T2 = ⓪{I} ∧ n = 0
                            | ∃∃s. T2 = ⋆(next h s) & I = Sort s & n = 1
                            | ∃∃K,V,V2,i. ⬇*[i] L ≡ K.ⓓV & ⦃G, K⦄ ⊢ V ➡[n, h] V2 &
                                          ⬆*[⫯i] V2 ≡ T2 & I = LRef i
                            | ∃∃k,K,V,V2,i. ⬇*[i] L ≡ K.ⓛV & ⦃G, K⦄ ⊢ V ➡[k, h] V2 &
                                            ⬆*[⫯i] V2 ≡ T2 & I = LRef i & n = ⫯k.
#n #h #I #G #L #T2 * #c #Hc #H elim (cpg_inv_atom1_drops … H) -H *
[ #H1 #H2 destruct lapply (isrt_inv_00 … Hc) -Hc
  /3 width=1 by or4_intro0, conj/
| #s #H1 #H2 #H3 destruct lapply (isrt_inv_01 … Hc) -Hc
  /4 width=3 by or4_intro1, ex3_intro, sym_eq/ (**) (* sym_eq *)
| #cV #i #K #V1 #V2 #HLK #HV12 #HVT2 #H1 #H2 destruct
  /4 width=8 by ex4_4_intro, ex2_intro, or4_intro2/
| #cV #i #K #V1 #V2 #HLK #HV12 #HVT2 #H1 #H2 destruct
  elim (isrt_inv_plus_SO_dx … Hc) -Hc
  /4 width=10 by ex5_5_intro, ex2_intro, or4_intro3/
]
qed-.

lemma cpm_inv_lref1_drops: ∀n,h,G,L,T2,i. ⦃G, L⦄ ⊢ #i ➡[n, h] T2 →
                           ∨∨ T2 = #i ∧ n = 0
                            | ∃∃K,V,V2. ⬇*[i] L ≡ K. ⓓV & ⦃G, K⦄ ⊢ V ➡[n, h] V2 &
                                        ⬆*[⫯i] V2 ≡ T2
                            | ∃∃k,K,V,V2. ⬇*[i] L ≡ K. ⓛV & ⦃G, K⦄ ⊢ V ➡[k, h] V2 &
                                          ⬆*[⫯i] V2 ≡ T2 & n = ⫯k.
#n #h #G #L #T2 #i * #c #Hc #H elim (cpg_inv_lref1_drops … H) -H *
[ #H1 #H2 destruct lapply (isrt_inv_00 … Hc) -Hc
  /3 width=1 by or3_intro0, conj/
| #cV #K #V1 #V2 #HLK #HV12 #HVT2 #H destruct
  /4 width=6 by ex3_3_intro, ex2_intro, or3_intro1/
| #cV #K #V1 #V2 #HLK #HV12 #HVT2 #H destruct
  elim (isrt_inv_plus_SO_dx … Hc) -Hc
  /4 width=8 by ex4_4_intro, ex2_intro, or3_intro2/
]
qed-.

(* Properties with generic slicing for local environments *******************)

(* Basic_1: includes: pr0_lift pr2_lift *)
(* Basic_2A1: includes: cpr_lift *)
lemma cpm_lifts_sn: ∀n,h,G. d_liftable2_sn (cpm n h G).
#n #h #G #K #T1 #T2 * #c #Hc #HT12 #b #f #L #HLK #U1 #HTU1
elim (cpg_lifts_sn … HT12 … HLK … HTU1) -K -T1
/3 width=5 by ex2_intro/
qed-.

lemma cpm_lifts_bi: ∀n,h,G. d_liftable2_bi (cpm n h G).
/3 width=9 by cpm_lifts_sn, d_liftable2_sn_bi/ qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_1: includes: pr0_gen_lift pr2_gen_lift *)
(* Basic_2A1: includes: cpr_inv_lift1 *)
lemma cpm_inv_lifts_sn: ∀n,h,G. d_deliftable2_sn (cpm n h G).
#n #h #G #L #U1 #U2 * #c #Hc #HU12 #b #f #K #HLK #T1 #HTU1
elim (cpg_inv_lifts_sn … HU12 … HLK … HTU1) -L -U1
/3 width=5 by ex2_intro/
qed-.

lemma cpm_inv_lifts_bi: ∀n,h,G. d_deliftable2_bi (cpm n h G).
/3 width=9 by cpm_inv_lifts_sn, d_deliftable2_sn_bi/ qed-.
