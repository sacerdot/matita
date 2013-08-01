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

include "basic_2/notation/relations/lrsubeqv_4.ma".
include "basic_2/dynamic/snv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Note: this is not transitive *)
inductive lsubsv (h:sh) (g:sd h): relation lenv ≝
| lsubsv_atom: lsubsv h g (⋆) (⋆)
| lsubsv_pair: ∀I,L1,L2,V. lsubsv h g L1 L2 →
               lsubsv h g (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lsubsv_abbr: ∀L1,L2,W,V,W1,V2,l. ⦃h, L1⦄ ⊢ ⓝW.V ¡[h, g] → ⦃h, L2⦄ ⊢ W ¡[h, g] →
               ⦃h, L1⦄ ⊢ V •[h, g] ⦃l+1, W1⦄ → ⦃h, L2⦄ ⊢ W •[h, g] ⦃l, V2⦄ →
               lsubsv h g L1 L2 → lsubsv h g (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (stratified native validity)"
  'LRSubEqV h g L1 L2 = (lsubsv h g L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubsv_inv_atom1_aux: ∀h,g,L1,L2. h ⊢ L1 ¡⊑[h, g] L2 → L1 = ⋆ → L2 = ⋆.
#h #g #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #V1 #V2 #l #_ #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubsv_inv_atom1: ∀h,g,L2. h ⊢ ⋆ ¡⊑[h, g] L2 → L2 = ⋆.
/2 width=5 by lsubsv_inv_atom1_aux/ qed-.

fact lsubsv_inv_pair1_aux: ∀h,g,L1,L2. h ⊢ L1 ¡⊑[h, g] L2 →
                           ∀I,K1,X. L1 = K1.ⓑ{I}X →
                           (∃∃K2. h ⊢ K1 ¡⊑[h, g] K2 & L2 = K2.ⓑ{I}X) ∨
                           ∃∃K2,W,V,W1,V2,l. ⦃h, K1⦄ ⊢ X ¡[h, g] & ⦃h, K2⦄ ⊢ W ¡[h, g] &
                                             ⦃h, K1⦄ ⊢ V •[h, g] ⦃l+1, W1⦄ & ⦃h, K2⦄ ⊢ W •[h, g] ⦃l, V2⦄ &
                                             h ⊢ K1 ¡⊑[h, g] K2 &
                                             I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
#h #g #L1 #L2 * -L1 -L2
[ #J #K1 #X #H destruct
| #I #L1 #L2 #V #HL12 #J #K1 #X #H destruct /3 width=3/
| #L1 #L2 #W #V #W1 #V2 #l #HV #HW #HW1 #HV2 #HL12 #J #K1 #X #H destruct /3 width=12/
]
qed-.

lemma lsubsv_inv_pair1: ∀h,g,I,K1,L2,X. h ⊢ K1.ⓑ{I}X ¡⊑[h, g] L2 →
                        (∃∃K2. h ⊢ K1 ¡⊑[h, g] K2 & L2 = K2.ⓑ{I}X) ∨
                        ∃∃K2,W,V,W1,V2,l. ⦃h, K1⦄ ⊢ X ¡[h, g] & ⦃h, K2⦄ ⊢ W ¡[h, g] &
                                          ⦃h, K1⦄ ⊢ V •[h, g] ⦃l+1, W1⦄ & ⦃h, K2⦄ ⊢ W •[h, g] ⦃l, V2⦄ &
                                          h ⊢ K1 ¡⊑[h, g] K2 &
                                          I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
/2 width=3 by lsubsv_inv_pair1_aux/ qed-.

fact lsubsv_inv_atom2_aux: ∀h,g,L1,L2. h ⊢ L1 ¡⊑[h, g] L2 → L2 = ⋆ → L1 = ⋆.
#h #g #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #V1 #V2 #l #_ #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubsv_inv_atom2: ∀h,g,L1. h ⊢ L1 ¡⊑[h, g] ⋆ → L1 = ⋆.
/2 width=5 by lsubsv_inv_atom2_aux/ qed-.

fact lsubsv_inv_pair2_aux: ∀h,g,L1,L2. h ⊢ L1 ¡⊑[h, g] L2 →
                           ∀I,K2,W. L2 = K2.ⓑ{I}W →
                           (∃∃K1. h ⊢ K1 ¡⊑[h, g] K2 & L1 = K1.ⓑ{I}W) ∨
                           ∃∃K1,V,W1,V2,l. ⦃h, K1⦄ ⊢ ⓝW.V ¡[h, g] & ⦃h, K2⦄ ⊢ W ¡[h, g] &
                                           ⦃h, K1⦄ ⊢ V •[h, g] ⦃l+1, W1⦄ & ⦃h, K2⦄ ⊢ W •[h, g] ⦃l, V2⦄ &
                                           h ⊢ K1 ¡⊑[h, g] K2 & I = Abst & L1 = K1. ⓓⓝW.V.
#h #g #L1 #L2 * -L1 -L2
[ #J #K2 #U #H destruct
| #I #L1 #L2 #V #HL12 #J #K2 #U #H destruct /3 width=3/
| #L1 #L2 #W #V #W1 #V2 #l #HV #HW #HW1 #HV2 #HL12 #J #K2 #U #H destruct /3 width=10/
]
qed-.

lemma lsubsv_inv_pair2: ∀h,g,I,L1,K2,W. h ⊢ L1 ¡⊑[h, g] K2.ⓑ{I}W →
                        (∃∃K1. h ⊢ K1 ¡⊑[h, g] K2 & L1 = K1.ⓑ{I}W) ∨
                        ∃∃K1,V,W1,V2,l. ⦃h, K1⦄ ⊢ ⓝW.V ¡[h, g] & ⦃h, K2⦄ ⊢ W ¡[h, g] &
                                        ⦃h, K1⦄ ⊢ V •[h, g] ⦃l+1, W1⦄ & ⦃h, K2⦄ ⊢ W •[h, g] ⦃l, V2⦄ &
                                        h ⊢ K1 ¡⊑[h, g] K2 & I = Abst & L1 = K1. ⓓⓝW.V.
/2 width=3 by lsubsv_inv_pair2_aux/ qed-.

(* Basic_forward lemmas *****************************************************)

lemma lsubsv_fwd_lsubr: ∀h,g,L1,L2. h ⊢ L1 ¡⊑[h, g] L2 → L1 ⊑ L2.
#h #g #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

(* Basic properties *********************************************************)

lemma lsubsv_refl: ∀h,g,L. h ⊢ L ¡⊑[h, g] L.
#h #g #L elim L -L // /2 width=1/
qed.

lemma lsubsv_cprs_trans: ∀h,g,L1,L2. h ⊢ L1 ¡⊑[h, g] L2 →
                         ∀T1,T2. L2 ⊢ T1 ➡* T2 → L1 ⊢ T1 ➡* T2.
/3 width=5 by lsubsv_fwd_lsubr, lsubr_cprs_trans/
qed-.
