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

include "basic_2/notation/relations/lrsubeqv_5.ma".
include "basic_2/dynamic/snv.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED NATIVE VALIDITY **************)

(* Note: this is not transitive *)
inductive lsubsv (h) (g) (G): relation lenv ≝
| lsubsv_atom: lsubsv h g G (⋆) (⋆)
| lsubsv_pair: ∀I,L1,L2,V. lsubsv h g G L1 L2 →
               lsubsv h g G (L1.ⓑ{I}V) (L2.ⓑ{I}V)
| lsubsv_abbr: ∀L1,L2,W,V,l. ⦃G, L1⦄ ⊢ W ¡[h, g] → ⦃G, L1⦄ ⊢ V ¡[h, g] →
               scast h g l G L1 V W → ⦃G, L2⦄ ⊢ W ¡[h, g] →
               ⦃G, L1⦄ ⊢ V ▪[h, g] l+1 → ⦃G, L2⦄ ⊢ W ▪[h, g] l →
               lsubsv h g G L1 L2 → lsubsv h g G (L1.ⓓⓝW.V) (L2.ⓛW)
.

interpretation
  "local environment refinement (stratified native validity)"
  'LRSubEqV h g G L1 L2 = (lsubsv h g G L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubsv_inv_atom1_aux: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 → L1 = ⋆ → L2 = ⋆.
#h #g #G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #l #_ #_ #_ #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubsv_inv_atom1: ∀h,g,G,L2. G ⊢ ⋆ ¡⊑[h, g] L2 → L2 = ⋆.
/2 width=6 by lsubsv_inv_atom1_aux/ qed-.

fact lsubsv_inv_pair1_aux: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 →
                           ∀I,K1,X. L1 = K1.ⓑ{I}X →
                           (∃∃K2. G ⊢ K1 ¡⊑[h, g] K2 & L2 = K2.ⓑ{I}X) ∨
                           ∃∃K2,W,V,l. ⦃G, K1⦄ ⊢ W ¡[h, g] & ⦃G, K1⦄ ⊢ V ¡[h, g] &
                                       scast h g l G K1 V W & ⦃G, K2⦄ ⊢ W ¡[h, g] &
                                       ⦃G, K1⦄ ⊢ V ▪[h, g] l+1 & ⦃G, K2⦄ ⊢ W ▪[h, g] l &
                                       G ⊢ K1 ¡⊑[h, g] K2 &
                                       I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
#h #g #G #L1 #L2 * -L1 -L2
[ #J #K1 #X #H destruct
| #I #L1 #L2 #V #HL12 #J #K1 #X #H destruct /3 width=3/
| #L1 #L2 #W #V #l #H1W #HV #HVW #H2W #H1l #H2l #HL12 #J #K1 #X #H destruct /3 width=13/
]
qed-.

lemma lsubsv_inv_pair1: ∀h,g,I,G,K1,L2,X. G ⊢ K1.ⓑ{I}X ¡⊑[h, g] L2 →
                        (∃∃K2. G ⊢ K1 ¡⊑[h, g] K2 & L2 = K2.ⓑ{I}X) ∨
                        ∃∃K2,W,V,l. ⦃G, K1⦄ ⊢ W ¡[h, g] & ⦃G, K1⦄ ⊢ V ¡[h, g] &
                                    scast h g l G K1 V W & ⦃G, K2⦄ ⊢ W ¡[h, g] &
                                    ⦃G, K1⦄ ⊢ V ▪[h, g] l+1 & ⦃G, K2⦄ ⊢ W ▪[h, g] l &
                                    G ⊢ K1 ¡⊑[h, g] K2 &
                                    I = Abbr & L2 = K2.ⓛW & X = ⓝW.V.
/2 width=3 by lsubsv_inv_pair1_aux/ qed-.

fact lsubsv_inv_atom2_aux: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 → L2 = ⋆ → L1 = ⋆.
#h #g #G #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #W #V #l #_ #_ #_ #_ #_ #_ #_ #H destruct
]
qed-.

lemma lsubsv_inv_atom2: ∀h,g,G,L1. G ⊢ L1 ¡⊑[h, g] ⋆ → L1 = ⋆.
/2 width=6 by lsubsv_inv_atom2_aux/ qed-.

fact lsubsv_inv_pair2_aux: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 →
                           ∀I,K2,W. L2 = K2.ⓑ{I}W →
                           (∃∃K1. G ⊢ K1 ¡⊑[h, g] K2 & L1 = K1.ⓑ{I}W) ∨
                           ∃∃K1,V,l. ⦃G, K1⦄ ⊢ W ¡[h, g] & ⦃G, K1⦄ ⊢ V ¡[h, g] &
                                     scast h g l G K1 V W & ⦃G, K2⦄ ⊢ W ¡[h, g] &
                                     ⦃G, K1⦄ ⊢ V ▪[h, g] l+1 & ⦃G, K2⦄ ⊢ W ▪[h, g] l &
                                     G ⊢ K1 ¡⊑[h, g] K2 & I = Abst & L1 = K1. ⓓⓝW.V.
#h #g #G #L1 #L2 * -L1 -L2
[ #J #K2 #U #H destruct
| #I #L1 #L2 #V #HL12 #J #K2 #U #H destruct /3 width=3/
| #L1 #L2 #W #V #l #H1W #HV #HVW #H2W #H1l #H2l #HL12 #J #K2 #U #H destruct /3 width=10/
]
qed-.

lemma lsubsv_inv_pair2: ∀h,g,I,G,L1,K2,W. G ⊢ L1 ¡⊑[h, g] K2.ⓑ{I}W →
                        (∃∃K1. G ⊢ K1 ¡⊑[h, g] K2 & L1 = K1.ⓑ{I}W) ∨
                        ∃∃K1,V,l. ⦃G, K1⦄ ⊢ W ¡[h, g] & ⦃G, K1⦄ ⊢ V ¡[h, g] &
                                  scast h g l G K1 V W & ⦃G, K2⦄ ⊢ W ¡[h, g] &
                                  ⦃G, K1⦄ ⊢ V ▪[h, g] l+1 & ⦃G, K2⦄ ⊢ W ▪[h, g] l &
                                  G ⊢ K1 ¡⊑[h, g] K2 & I = Abst & L1 = K1. ⓓⓝW.V.
/2 width=3 by lsubsv_inv_pair2_aux/ qed-.

(* Basic_forward lemmas *****************************************************)

lemma lsubsv_fwd_lsubr: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 → L1 ⊑ L2.
#h #g #G #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

(* Basic properties *********************************************************)

lemma lsubsv_refl: ∀h,g,G,L. G ⊢ L ¡⊑[h, g] L.
#h #g #G #L elim L -L // /2 width=1/
qed.

lemma lsubsv_cprs_trans: ∀h,g,G,L1,L2. G ⊢ L1 ¡⊑[h, g] L2 →
                         ∀T1,T2. ⦃G, L2⦄ ⊢ T1 ➡* T2 → ⦃G, L1⦄ ⊢ T1 ➡* T2.
/3 width=6 by lsubsv_fwd_lsubr, lsubr_cprs_trans/
qed-.
