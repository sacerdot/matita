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

(* Basic_1: removed theorems 12:
            pr0_subst0_back pr0_subst0_fwd pr0_subst0
            pr0_delta1
            pr2_head_2 pr2_cflat clear_pr2_trans
            pr2_gen_csort pr2_gen_cflat pr2_gen_cbind
            pr2_gen_ctail pr2_ctail
*)
