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

include "basic_2/static/ssta.ma".
include "basic_2/computation/cprs.ma".
include "basic_2/equivalence/cpcs.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED STATIC TYPE ASSIGNMENT *******)

(* Note: this is not transitive *)
inductive lsubss (h:sh) (g:sd h): relation lenv ≝
| lsubss_atom: lsubss h g (⋆) (⋆)
| lsubss_pair: ∀I,L1,L2,V. lsubss h g L1 L2 →
               lsubss h g (L1. ⓑ{I} V) (L2. ⓑ{I} V)
| lsubss_abbr: ∀L1,L2,V1,V2,W1,W2,l. L1 ⊢ W1 ⬌* W2 →
               ⦃h, L1⦄ ⊢ V1 •[g] ⦃l+1, W1⦄ → ⦃h, L2⦄ ⊢ W2 •[g] ⦃l, V2⦄ →
               lsubss h g L1 L2 → lsubss h g (L1. ⓓV1) (L2. ⓛW2)
.

interpretation
  "local environment refinement (stratified static type assigment)"
  'CrSubEqS h g L1 L2 = (lsubss h g L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubss_inv_atom1_aux: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 → L1 = ⋆ → L2 = ⋆.
#h #g #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V1 #V2 #W1 #W2 #l #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubss_inv_atom1: ∀h,g,L2. h ⊢ ⋆ •⊑[g] L2 → L2 = ⋆.
/2 width=5 by lsubss_inv_atom1_aux/ qed-.

fact lsubss_inv_pair1_aux: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 →
                           ∀I,K1,V1. L1 = K1. ⓑ{I} V1 →
                           (∃∃K2. h ⊢ K1 •⊑[g] K2 & L2 = K2. ⓑ{I} V1) ∨
                           ∃∃K2,W1,W2,V2,l. ⦃h, K1⦄ ⊢ V1 •[g] ⦃l+1, W1⦄ & ⦃h, K2⦄ ⊢ W2 •[g] ⦃l, V2⦄ &
                                            K1 ⊢ W1 ⬌* W2 & h ⊢ K1 •⊑[g] K2 & L2 = K2. ⓛW2 & I = Abbr.
#h #g #L1 #L2 * -L1 -L2
[ #J #K1 #U1 #H destruct
| #I #L1 #L2 #V #HL12 #J #K1 #U1 #H destruct /3 width=3/
| #L1 #L2 #V1 #V2 #W1 #W2 #l #HW12 #HVW1 #HWV2 #HL12 #J #K1 #U1 #H destruct /3 width=10/
]
qed-.

lemma lsubss_inv_pair1: ∀h,g,I,K1,L2,V1. h ⊢ K1. ⓑ{I} V1 •⊑[g] L2 →
                        (∃∃K2. h ⊢ K1 •⊑[g] K2 & L2 = K2. ⓑ{I} V1) ∨
                        ∃∃K2,W1,W2,V2,l. ⦃h, K1⦄ ⊢ V1 •[g] ⦃l+1, W1⦄ & ⦃h, K2⦄ ⊢ W2 •[g] ⦃l, V2⦄ &
                                         K1 ⊢ W1 ⬌* W2 & h ⊢ K1 •⊑[g] K2 & L2 = K2. ⓛW2 & I = Abbr.
/2 width=3 by lsubss_inv_pair1_aux/ qed-.

fact lsubss_inv_atom2_aux: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 → L2 = ⋆ → L1 = ⋆.
#h #g #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V1 #V2 #W1 #W2 #l #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubss_inv_atom2: ∀h,g,L1. h ⊢ L1 •⊑[g] ⋆ → L1 = ⋆.
/2 width=5 by lsubss_inv_atom2_aux/ qed-.

fact lsubss_inv_pair2_aux: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 →
                           ∀I,K2,W2. L2 = K2. ⓑ{I} W2 →
                           (∃∃K1. h ⊢ K1 •⊑[g] K2 & L1 = K1. ⓑ{I} W2) ∨
                           ∃∃K1,W1,V1,V2,l. ⦃h, K1⦄ ⊢ V1 •[g] ⦃l+1, W1⦄ & ⦃h, K2⦄ ⊢ W2 •[g] ⦃l, V2⦄ &
                                            K1 ⊢ W1 ⬌* W2 & h ⊢ K1 •⊑[g] K2 & L1 = K1. ⓓV1 & I = Abst.
#h #g #L1 #L2 * -L1 -L2
[ #J #K2 #U2 #H destruct
| #I #L1 #L2 #V #HL12 #J #K2 #U2 #H destruct /3 width=3/
| #L1 #L2 #V1 #V2 #W1 #W2 #l #HW12 #HVW1 #HWV2 #HL12 #J #K2 #U2 #H destruct /3 width=10/
]
qed-.

lemma lsubss_inv_pair2: ∀h,g,I,L1,K2,W2. h ⊢ L1 •⊑[g] K2. ⓑ{I} W2 →
                        (∃∃K1. h ⊢ K1 •⊑[g] K2 & L1 = K1. ⓑ{I} W2) ∨
                        ∃∃K1,W1,V1,V2,l. ⦃h, K1⦄ ⊢ V1 •[g] ⦃l+1, W1⦄ & ⦃h, K2⦄ ⊢ W2 •[g] ⦃l, V2⦄ &
                                         K1 ⊢ W1 ⬌* W2 & h ⊢ K1 •⊑[g] K2 & L1 = K1. ⓓV1 & I = Abst.
/2 width=3 by lsubss_inv_pair2_aux/ qed-.

(* Basic_forward lemmas *****************************************************)

lemma lsubss_fwd_lsubr1: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 → L1 ⊑[0, |L1|] L2.
#h #g #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

lemma lsubss_fwd_lsubr2: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 → L1 ⊑[0, |L2|] L2.
#h #g #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

(* Basic properties *********************************************************)

lemma lsubss_refl: ∀h,g,L. h ⊢ L •⊑[g] L.
#h #g #L elim L -L // /2 width=1/
qed.

lemma lsubss_cprs_trans: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 →
                         ∀T1,T2. L2 ⊢ T1 ➡* T2 → L1 ⊢ T1 ➡* T2.
/3 width=5 by lsubss_fwd_lsubr2, cprs_lsubr_trans/
qed-.