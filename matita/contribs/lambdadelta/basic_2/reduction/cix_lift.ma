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

include "basic_2/reduction/crx_lift.ma".
include "basic_2/reduction/cix.ma".

(* IRREDUCIBLE TERMS FOR CONTEXT-SENSITIVE EXTENDED REDUCTION ***************)

(* Advanced properties ******************************************************)

lemma cix_lref: ∀h,o,G,L,i. ⬇[i] L ≡ ⋆ → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃#i⦄.
#h #o #G #L #i #HL #H elim (crx_inv_lref … H) -h #I #K #V #HLK
lapply (drop_mono … HLK … HL) -L -i #H destruct
qed.

(* Properties on relocation *************************************************)

lemma cix_lift: ∀h,o,G,K,T. ⦃G, K⦄ ⊢ ➡[h, o] 𝐈⦃T⦄ → ∀L,c,l,k. ⬇[c, l, k] L ≡ K →
                ∀U. ⬆[l, k] T ≡ U → ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃U⦄.
/3 width=8 by crx_inv_lift/ qed.

lemma cix_inv_lift: ∀h,o,G,L,U. ⦃G, L⦄ ⊢ ➡[h, o] 𝐈⦃U⦄ → ∀K,c,l,k. ⬇[c, l, k] L ≡ K →
                    ∀T. ⬆[l, k] T ≡ U → ⦃G, K⦄ ⊢ ➡[h, o] 𝐈⦃T⦄.
/3 width=8 by crx_lift/ qed-.
