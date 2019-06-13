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

(* Properties with generic slicing for local environments *******************)

(* Basic_1: includes: pr0_lift pr2_lift *)
(* Basic_2A1: includes: cpr_lift *)
lemma cpm_lifts_sn: ∀n,h,G. d_liftable2_sn … lifts (λL. cpm h G L n).
#n #h #G #K #T1 #T2 * #c #Hc #HT12 #b #f #L #HLK #U1 #HTU1
elim (cpg_lifts_sn … HT12 … HLK … HTU1) -K -T1
/3 width=5 by ex2_intro/
qed-.

lemma cpm_lifts_bi: ∀n,h,G. d_liftable2_bi … lifts (λL. cpm h G L n).
#n #h #G #K #T1 #T2 * /3 width=11 by cpg_lifts_bi, ex2_intro/
qed-.

(* Inversion lemmas with generic slicing for local environments *************)

(* Basic_1: includes: pr0_gen_lift pr2_gen_lift *)
(* Basic_2A1: includes: cpr_inv_lift1 *)
lemma cpm_inv_lifts_sn: ∀n,h,G. d_deliftable2_sn … lifts (λL. cpm h G L n).
#n #h #G #L #U1 #U2 * #c #Hc #HU12 #b #f #K #HLK #T1 #HTU1
elim (cpg_inv_lifts_sn … HU12 … HLK … HTU1) -L -U1
/3 width=5 by ex2_intro/
qed-.

lemma cpm_inv_lifts_bi: ∀n,h,G. d_deliftable2_bi … lifts (λL. cpm h G L n).
#n #h #G #L #U1 #U2 * /3 width=11 by cpg_inv_lifts_bi, ex2_intro/
qed-.

(* Advanced properties ******************************************************)

(* Basic_1: includes: pr2_delta1 *)
(* Basic_2A1: includes: cpr_delta *)
lemma cpm_delta_drops: ∀n,h,G,L,K,V,V2,W2,i.
                       ⬇*[i] L ≘ K.ⓓV → ⦃G,K⦄ ⊢ V ➡[n,h] V2 →
                       ⬆*[↑i] V2 ≘ W2 → ⦃G,L⦄ ⊢ #i ➡[n,h] W2.
#n #h #G #L #K #V #V2 #W2 #i #HLK *
/3 width=8 by cpg_delta_drops, ex2_intro/
qed.

lemma cpm_ell_drops: ∀n,h,G,L,K,V,V2,W2,i.
                     ⬇*[i] L ≘ K.ⓛV → ⦃G,K⦄ ⊢ V ➡[n,h] V2 →
                     ⬆*[↑i] V2 ≘ W2 → ⦃G,L⦄ ⊢ #i ➡[↑n,h] W2.
#n #h #G #L #K #V #V2 #W2 #i #HLK *
/3 width=8 by cpg_ell_drops, isrt_succ, ex2_intro/
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpm_inv_atom1_drops: ∀n,h,I,G,L,T2. ⦃G,L⦄ ⊢ ⓪{I} ➡[n,h] T2 →
                           ∨∨ T2 = ⓪{I} ∧ n = 0
                            | ∃∃s. T2 = ⋆(next h s) & I = Sort s & n = 1
                            | ∃∃K,V,V2,i. ⬇*[i] L ≘ K.ⓓV & ⦃G,K⦄ ⊢ V ➡[n,h] V2 &
                                          ⬆*[↑i] V2 ≘ T2 & I = LRef i
                            | ∃∃m,K,V,V2,i. ⬇*[i] L ≘ K.ⓛV & ⦃G,K⦄ ⊢ V ➡[m,h] V2 &
                                            ⬆*[↑i] V2 ≘ T2 & I = LRef i & n = ↑m.
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

lemma cpm_inv_lref1_drops: ∀n,h,G,L,T2,i. ⦃G,L⦄ ⊢ #i ➡[n,h] T2 →
                           ∨∨ T2 = #i ∧ n = 0
                            | ∃∃K,V,V2. ⬇*[i] L ≘ K.ⓓV & ⦃G,K⦄ ⊢ V ➡[n,h] V2 &
                                        ⬆*[↑i] V2 ≘ T2
                            | ∃∃m,K,V,V2. ⬇*[i] L ≘ K. ⓛV & ⦃G,K⦄ ⊢ V ➡[m,h] V2 &
                                          ⬆*[↑i] V2 ≘ T2 & n = ↑m.
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

(* Advanced forward lemmas **************************************************)

fact cpm_fwd_plus_aux (n) (h): ∀G,L,T1,T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 →
                               ∀n1,n2. n1+n2 = n →
                               ∃∃T. ⦃G,L⦄ ⊢ T1 ➡[n1,h] T & ⦃G,L⦄ ⊢ T ➡[n2,h] T2.
#n #h #G #L #T1 #T2 #H @(cpm_ind … H) -G -L -T1 -T2 -n
[ #I #G #L #n1 #n2 #H
  elim (plus_inv_O3 … H) -H #H1 #H2 destruct
  /2 width=3 by ex2_intro/
| #G #L #s #x1 #n2 #H
  elim (plus_inv_S3_sn … H) -H *
  [ #H1 #H2 destruct /2 width=3 by ex2_intro/
  | #n1 #H1 #H elim (plus_inv_O3 … H) -H #H2 #H3 destruct
    /2 width=3 by ex2_intro/
  ]
| #n #G #K #V1 #V2 #W2 #_ #IH #HVW2 #n1 #n2 #H destruct
  elim IH [|*: // ] -IH #V #HV1 #HV2
  elim (lifts_total V 𝐔❴↑O❵) #W #HVW
  /5 width=11 by cpm_lifts_bi, cpm_delta, drops_refl, drops_drop, ex2_intro/
| #n #G #K #V1 #V2 #W2 #HV12 #IH #HVW2 #x1 #n2 #H
  elim (plus_inv_S3_sn … H) -H *
  [ #H1 #H2 destruct -IH /3 width=3 by cpm_ell, ex2_intro/
  | #n1 #H1 #H2 destruct -HV12
    elim (IH n1) [|*: // ] -IH #V #HV1 #HV2
    elim (lifts_total V 𝐔❴↑O❵) #W #HVW
    /5 width=11 by cpm_lifts_bi, cpm_ell, drops_refl, drops_drop, ex2_intro/
  ]
| #n #I #G #K #T2 #U2 #i #_ #IH #HTU2 #n1 #n2 #H destruct
  elim IH [|*: // ] -IH #T #HT1 #HT2
  elim (lifts_total T 𝐔❴↑O❵) #U #HTU
  /5 width=11 by cpm_lifts_bi, cpm_lref, drops_refl, drops_drop, ex2_intro/
| #n #p #I #G #L #V1 #V2 #T1 #T2 #HV12 #_ #_ #IHT #n1 #n2 #H destruct
  elim IHT [|*: // ] -IHT #T #HT1 #HT2
  /3 width=5 by cpm_bind, ex2_intro/
| #n #G #L #V1 #V2 #T1 #T2 #HV12 #_ #_ #IHT #n1 #n2 #H destruct
  elim IHT [|*: // ] -IHT #T #HT1 #HT2
  /3 width=5 by cpm_appl, ex2_intro/
| #n #G #L #U1 #U2 #T1 #T2 #_ #_ #IHU #IHT #n1 #n2 #H destruct
  elim IHU [|*: // ] -IHU #U #HU1 #HU2
  elim IHT [|*: // ] -IHT #T #HT1 #HT2
  /3 width=5 by cpm_cast, ex2_intro/
| #n #G #K #V #U1 #T1 #T2 #HTU1 #_ #IH #n1 #n2 #H destruct
  elim IH [|*: // ] -IH #T #HT1 #HT2
  /3 width=3 by cpm_zeta, ex2_intro/
| #n #G #L #U #T1 #T2 #_ #IH #n1 #n2 #H destruct
  elim IH [|*: // ] -IH #T #HT1 #HT2
  /3 width=3 by cpm_eps, ex2_intro/
| #n #G #L #U1 #U2 #T #HU12 #IH #x1 #n2 #H
  elim (plus_inv_S3_sn … H) -H *
  [ #H1 #H2 destruct -IH /3 width=4 by cpm_ee, cpm_cast, ex2_intro/
  | #n1 #H1 #H2 destruct -HU12
    elim (IH n1) [|*: // ] -IH #U #HU1 #HU2
    /3 width=3 by cpm_ee, ex2_intro/
  ]
| #n #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #_ #_ #_ #IH #n1 #n2 #H destruct
  elim IH [|*: // ] -IH #T #HT1 #HT2
  /4 width=7 by cpm_beta, cpm_appl, cpm_bind, ex2_intro/
| #n #p #G #L #V1 #V2 #U2 #W1 #W2 #T1 #T2 #HV12 #HW12 #_ #_ #_ #IH #HVU2 #n1 #n2 #H destruct
  elim IH [|*: // ] -IH #T #HT1 #HT2
  /4 width=7 by cpm_theta, cpm_appl, cpm_bind, ex2_intro/
]
qed-.

lemma cpm_fwd_plus (h) (G) (L): ∀n1,n2,T1,T2. ⦃G,L⦄ ⊢ T1 ➡[n1+n2,h] T2 →
                                ∃∃T. ⦃G,L⦄ ⊢ T1 ➡[n1,h] T & ⦃G,L⦄ ⊢ T ➡[n2,h] T2.
/2 width=3 by cpm_fwd_plus_aux/ qed-.
