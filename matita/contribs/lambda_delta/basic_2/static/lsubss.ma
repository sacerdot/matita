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

(* LOCAL ENVIRONMENT REFINEMENT FOR STRATIFIED STATIC TYPE ASSIGNMENT *******)

(* Note: may not be transitive *)
inductive lsubss (h:sh) (g:sd h): relation lenv ≝
| lsubss_atom: lsubss h g (⋆) (⋆)
| lsubss_pair: ∀I,L1,L2,W. lsubss h g L1 L2 →
               lsubss h g (L1. ⓑ{I} W) (L2. ⓑ{I} W)
| lsubss_abbr: ∀L1,L2,V,W,l. ⦃h, L1⦄ ⊢ V •[g, l+1] W → ⦃h, L2⦄ ⊢ V •[g, l+1] W →
               lsubss h g L1 L2 → lsubss h g (L1. ⓓV) (L2. ⓛW)
.

interpretation
  "local environment refinement (stratified static type assigment)"
  'CrSubEqS h g L1 L2 = (lsubss h g L1 L2).

(* Basic inversion lemmas ***************************************************)

fact lsubss_inv_atom1_aux: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 → L1 = ⋆ → L2 = ⋆.
#h #g #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V #W #l #_ #_ #_ #H destruct
]
qed.

lemma lsubss_inv_atom1: ∀h,g,L2. h ⊢ ⋆ •⊑[g] L2 → L2 = ⋆.
/2 width=5/ qed-.

fact lsubss_inv_pair1_aux: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 →
                           ∀I,K1,V. L1 = K1. ⓑ{I} V →
                           (∃∃K2. h ⊢ K1 •⊑[g] K2 & L2 = K2. ⓑ{I} V) ∨
                           ∃∃K2,W,l. ⦃h, K1⦄ ⊢ V •[g,l+1] W & ⦃h, K2⦄ ⊢ V •[g,l+1] W &
                                     h ⊢ K1 •⊑[g] K2 & L2 = K2. ⓛW & I = Abbr.
#h #g #L1 #L2 * -L1 -L2
[ #I #K1 #V #H destruct
| #J #L1 #L2 #V #HL12 #I #K1 #W #H destruct /3 width=3/
| #L1 #L2 #V #W #l #H1VW #H2VW #HL12 #I #K1 #V1 #H destruct /3 width=7/
]
qed.

lemma lsubss_inv_pair1: ∀h,g,I,K1,L2,V. h ⊢ K1. ⓑ{I} V •⊑[g] L2 →
                        (∃∃K2. h ⊢ K1 •⊑[g] K2 & L2 = K2. ⓑ{I} V) ∨
                        ∃∃K2,W,l. ⦃h, K1⦄ ⊢ V •[g,l+1] W & ⦃h, K2⦄ ⊢ V •[g,l+1] W &
                                  h ⊢ K1 •⊑[g] K2 & L2 = K2. ⓛW & I = Abbr.
/2 width=3/ qed-.

fact lsubss_inv_atom2_aux: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 → L2 = ⋆ → L1 = ⋆.
#h #g #L1 #L2 * -L1 -L2
[ //
| #I #L1 #L2 #V #_ #H destruct
| #L1 #L2 #V #W #l #_ #_ #_ #H destruct
]
qed.

lemma lsubss_inv_atom2: ∀h,g,L1. h ⊢ L1 •⊑[g] ⋆ → L1 = ⋆.
/2 width=5/ qed-.

fact lsubss_inv_pair2_aux: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 →
                           ∀I,K2,W. L2 = K2. ⓑ{I} W →
                           (∃∃K1. h ⊢ K1 •⊑[g] K2 & L1 = K1. ⓑ{I} W) ∨
                           ∃∃K1,V,l. ⦃h, K1⦄ ⊢ V •[g,l+1] W & ⦃h, K2⦄ ⊢ V •[g,l+1] W &
                                     h ⊢ K1 •⊑[g] K2 & L1 = K1. ⓓV & I = Abst.
#h #g #L1 #L2 * -L1 -L2
[ #I #K2 #W #H destruct
| #J #L1 #L2 #V #HL12 #I #K2 #W #H destruct /3 width=3/
| #L1 #L2 #V #W #l #H1VW #H2VW #HL12 #I #K2 #W2 #H destruct /3 width=7/
]
qed.

lemma lsubss_inv_pair2: ∀h,g,I,L1,K2,W. h ⊢ L1 •⊑[g] K2. ⓑ{I} W →
                        (∃∃K1. h ⊢ K1 •⊑[g] K2 & L1 = K1. ⓑ{I} W) ∨
                        ∃∃K1,V,l. ⦃h, K1⦄ ⊢ V •[g,l+1] W & ⦃h, K2⦄ ⊢ V •[g,l+1] W &
                                  h ⊢ K1 •⊑[g] K2 & L1 = K1. ⓓV & I = Abst.
/2 width=3/ qed-.

(* Basic_forward lemmas *****************************************************)

lemma lsubss_fwd_lsubs1: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 → L1 ≼[0, |L1|] L2.
#h #g #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

lemma lsubss_fwd_lsubs2: ∀h,g,L1,L2. h ⊢ L1 •⊑[g] L2 → L1 ≼[0, |L2|] L2.
#h #g #L1 #L2 #H elim H -L1 -L2 // /2 width=1/
qed-.

(* Basic properties *********************************************************)

lemma lsubss_refl: ∀h,g,L. h ⊢ L •⊑[g] L.
#h #g #L elim L -L // /2 width=1/
qed.
