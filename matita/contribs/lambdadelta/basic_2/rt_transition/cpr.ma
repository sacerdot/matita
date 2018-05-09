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

include "basic_2/rt_transition/cpm.ma".

(* CONTEXT-SENSITIVE PARALLEL R-TRANSITION FOR TERMS ************************)

(* Basic properties *********************************************************)

(* Note: cpr_flat: does not hold in basic_1 *)
(* Basic_1: includes: pr2_thin_dx *)
lemma cpr_flat: ∀h,I,G,L,V1,V2,T1,T2.
                ⦃G, L⦄ ⊢ V1 ➡[h] V2 → ⦃G, L⦄ ⊢ T1 ➡[h] T2 →
                ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ➡[h] ⓕ{I}V2.T2.
#h * /2 width=1 by cpm_cast, cpm_appl/
qed. 

(* Basic_1: was: pr2_head_1 *)
lemma cpr_pair_sn: ∀h,I,G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 →
                   ∀T. ⦃G, L⦄ ⊢ ②{I}V1.T ➡[h] ②{I}V2.T.
#h * /2 width=1 by cpm_bind, cpr_flat/
qed.

(* Basic inversion properties ***********************************************)

lemma cpr_inv_atom1: ∀h,J,G,L,T2. ⦃G, L⦄ ⊢ ⓪{J} ➡[h] T2 →
                     ∨∨ T2 = ⓪{J}
                      | ∃∃K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡[h] V2 & ⬆*[1] V2 ≘ T2 &
                                   L = K.ⓓV1 & J = LRef 0
                      | ∃∃I,K,T,i. ⦃G, K⦄ ⊢ #i ➡[h] T & ⬆*[1] T ≘ T2 &
                                   L = K.ⓘ{I} & J = LRef (↑i).
#h #J #G #L #T2 #H elim (cpm_inv_atom1 … H) -H *
/3 width=8 by tri_lt, or3_intro0, or3_intro1, or3_intro2, ex4_4_intro, ex4_3_intro/
#n #_ #_ #H destruct
qed-.

(* Basic_1: includes: pr0_gen_sort pr2_gen_sort *)
lemma cpr_inv_sort1: ∀h,G,L,T2,s. ⦃G, L⦄ ⊢ ⋆s ➡[h] T2 → T2 = ⋆s.
#h #G #L #T2 #s #H elim (cpm_inv_sort1 … H) -H * // #_ #H destruct
qed-.

lemma cpr_inv_zero1: ∀h,G,L,T2. ⦃G, L⦄ ⊢ #0 ➡[h] T2 →
                     ∨∨ T2 = #0
                      | ∃∃K,V1,V2. ⦃G, K⦄ ⊢ V1 ➡[h] V2 & ⬆*[1] V2 ≘ T2 &
                                   L = K.ⓓV1.
#h #G #L #T2 #H elim (cpm_inv_zero1 … H) -H *
/3 width=6 by ex3_3_intro, or_introl, or_intror/
#n #K #V1 #V2 #_ #_ #_ #H destruct
qed-.

lemma cpr_inv_lref1: ∀h,G,L,T2,i. ⦃G, L⦄ ⊢ #↑i ➡[h] T2 →
                     ∨∨ T2 = #(↑i)
                      | ∃∃I,K,T. ⦃G, K⦄ ⊢ #i ➡[h] T & ⬆*[1] T ≘ T2 & L = K.ⓘ{I}.
#h #G #L #T2 #i #H elim (cpm_inv_lref1 … H) -H *
/3 width=6 by ex3_3_intro, or_introl, or_intror/
qed-.

lemma cpr_inv_gref1: ∀h,G,L,T2,l. ⦃G, L⦄ ⊢ §l ➡[h] T2 → T2 = §l.
#h #G #L #T2 #l #H elim (cpm_inv_gref1 … H) -H //
qed-.

(* Basic_1: includes: pr0_gen_cast pr2_gen_cast *)
lemma cpr_inv_cast1: ∀h,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓝ V1.U1 ➡[h] U2 →
                     ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 & ⦃G, L⦄ ⊢ U1 ➡[h] T2 &
                                 U2 = ⓝV2.T2
                      | ⦃G, L⦄ ⊢ U1 ➡[h] U2.
#h #G #L #V1 #U1 #U2 #H elim (cpm_inv_cast1 … H) -H
/2 width=1 by or_introl, or_intror/ * #n #_ #H destruct
qed-.

lemma cpr_inv_flat1: ∀h,I,G,L,V1,U1,U2. ⦃G, L⦄ ⊢ ⓕ{I}V1.U1 ➡[h] U2 →
                     ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 & ⦃G, L⦄ ⊢ U1 ➡[h] T2 &
                                 U2 = ⓕ{I}V2.T2
                      | (⦃G, L⦄ ⊢ U1 ➡[h] U2 ∧ I = Cast)
                      | ∃∃p,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 & ⦃G, L⦄ ⊢ W1 ➡[h] W2 &
                                            ⦃G, L.ⓛW1⦄ ⊢ T1 ➡[h] T2 & U1 = ⓛ{p}W1.T1 &
                                            U2 = ⓓ{p}ⓝW2.V2.T2 & I = Appl
                      | ∃∃p,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h] V & ⬆*[1] V ≘ V2 &
                                              ⦃G, L⦄ ⊢ W1 ➡[h] W2 & ⦃G, L.ⓓW1⦄ ⊢ T1 ➡[h] T2 &
                                              U1 = ⓓ{p}W1.T1 &
                                              U2 = ⓓ{p}W2.ⓐV2.T2 & I = Appl.
#h * #G #L #V1 #U1 #U2 #H
[ elim (cpm_inv_appl1 … H) -H *
  /3 width=13 by or4_intro0, or4_intro2, or4_intro3, ex7_7_intro, ex6_6_intro, ex3_2_intro/
| elim (cpr_inv_cast1 … H) -H [ * ]
  /3 width=5 by or4_intro0, or4_intro1, ex3_2_intro, conj/
]
qed-.

(* Basic eliminators ********************************************************)

lemma cpr_ind (h): ∀R:relation4 genv lenv term term.
                   (∀I,G,L. R G L (⓪{I}) (⓪{I})) →
                   (∀G,K,V1,V2,W2. ⦃G, K⦄ ⊢ V1 ➡[h] V2 → R G K V1 V2 →
                     ⬆*[1] V2 ≘ W2 → R G (K.ⓓV1) (#0) W2
                   ) → (∀I,G,K,T,U,i. ⦃G, K⦄ ⊢ #i ➡[h] T → R G K (#i) T →
                     ⬆*[1] T ≘ U → R G (K.ⓘ{I}) (#↑i) (U)
                   ) → (∀p,I,G,L,V1,V2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 → ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡[h] T2 →
                     R G L V1 V2 → R G (L.ⓑ{I}V1) T1 T2 → R G L (ⓑ{p,I}V1.T1) (ⓑ{p,I}V2.T2)
                   ) → (∀I,G,L,V1,V2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 → ⦃G, L⦄ ⊢ T1 ➡[h] T2 →
                     R G L V1 V2 → R G L T1 T2 → R G L (ⓕ{I}V1.T1) (ⓕ{I}V2.T2)
                   ) → (∀G,L,V,T1,T,T2. ⦃G, L.ⓓV⦄ ⊢ T1 ➡[h] T → R G (L.ⓓV) T1 T →
                     ⬆*[1] T2 ≘ T → R G L (+ⓓV.T1) T2
                   ) → (∀G,L,V,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h] T2 → R G L T1 T2 →
                     R G L (ⓝV.T1) T2
                   ) → (∀p,G,L,V1,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 → ⦃G, L⦄ ⊢ W1 ➡[h] W2 → ⦃G, L.ⓛW1⦄ ⊢ T1 ➡[h] T2 →
                     R G L V1 V2 → R G L W1 W2 → R G (L.ⓛW1) T1 T2 →
                     R G L (ⓐV1.ⓛ{p}W1.T1) (ⓓ{p}ⓝW2.V2.T2)
                   ) → (∀p,G,L,V1,V,V2,W1,W2,T1,T2. ⦃G, L⦄ ⊢ V1 ➡[h] V → ⦃G, L⦄ ⊢ W1 ➡[h] W2 → ⦃G, L.ⓓW1⦄ ⊢ T1 ➡[h] T2 →
                     R G L V1 V → R G L W1 W2 → R G (L.ⓓW1) T1 T2 →
                     ⬆*[1] V ≘ V2 → R G L (ⓐV1.ⓓ{p}W1.T1) (ⓓ{p}W2.ⓐV2.T2)
                   ) →
                   ∀G,L,T1,T2. ⦃G, L⦄ ⊢ T1 ➡[h] T2 → R G L T1 T2.
#h #R #IH1 #IH2 #IH3 #IH4 #IH5 #IH6 #IH7 #IH8 #IH9 #G #L #T1 #T2
* #c #HC #H generalize in match HC; -HC
elim H -c -G -L -T1 -T2
[ /2 width=3 by ex2_intro/
| #G #L #s #H
  lapply (isrt_inv_01 … H) -H #H destruct
| /3 width=4 by ex2_intro/
| #c #G #L #V1 #V2 #W2 #_ #_ #_ #H
  elim (isrt_inv_plus_SO_dx … H) -H // #n #_ #H destruct
| /3 width=4 by ex2_intro/
| #cV #cT #p #I #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #IHV #IHT #H
  elim (isrt_O_inv_max … H) -H #HcV #HcT
  /4 width=3 by isr_inv_shift, ex2_intro/
| #cV #cT #G #L #V1 #V2 #T1 #T2 #HV12 #HT12 #IHV #IHT #H
  elim (isrt_O_inv_max … H) -H #HcV #HcT
  /4 width=3 by isr_inv_shift, ex2_intro/
| #cU #cT #G #L #U1 #U2 #T1 #T2 #HUT #HU12 #HT12 #IHU #IHT #H
  elim (isrt_O_inv_max … H) -H #HcV #HcT
  /3 width=3 by ex2_intro/
| /4 width=4 by isrt_inv_plus_O_dx, ex2_intro/
| /4 width=4 by isrt_inv_plus_O_dx, ex2_intro/
| #c #G #L #U1 #U2 #T #_ #_ #H
  elim (isrt_inv_plus_SO_dx … H) -H // #n #_ #H destruct
| #cV #cW #cT #p #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HW12 #HT12 #IHV #IHW #IHT #H
  lapply (isrt_inv_plus_O_dx … H ?) -H // #H
  elim (isrt_O_inv_max … H) -H #H #HcT
  elim (isrt_O_inv_max … H) -H #HcV #HcW
  /4 width=3 by isr_inv_shift, ex2_intro/
| #cV #cW #cT #p #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HW12 #HT12 #IHV #IHW #IHT #H
  lapply (isrt_inv_plus_O_dx … H ?) -H // #H
  elim (isrt_O_inv_max … H) -H #H #HcT
  elim (isrt_O_inv_max … H) -H #HcV #HcW
  /4 width=4 by isr_inv_shift, ex2_intro/
]
qed-.

(* Basic_1: removed theorems 12:
            pr0_subst0_back pr0_subst0_fwd pr0_subst0
            pr0_delta1
            pr2_head_2 pr2_cflat clear_pr2_trans
            pr2_gen_csort pr2_gen_cflat pr2_gen_cbind
            pr2_gen_ctail pr2_ctail
*)
