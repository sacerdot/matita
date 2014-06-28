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

lemma cix_lref: ∀h,g,G,L,i. ⇩[i] L ≡ ⋆ → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃#i⦄.
#h #g #G #L #i #HL #H elim (crx_inv_lref … H) -h #I #K #V #HLK
lapply (drop_mono … HLK … HL) -L -i #H destruct
qed.

(* Properties on relocation *************************************************)

lemma cix_lift: ∀h,g,G,K,T. ⦃G, K⦄ ⊢ ➡[h, g] 𝐈⦃T⦄ → ∀L,s,d,e. ⇩[s, d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃U⦄.
/3 width=8 by crx_inv_lift/ qed.

lemma cix_inv_lift: ∀h,g,G,L,U. ⦃G, L⦄ ⊢ ➡[h, g] 𝐈⦃U⦄ → ∀K,s,d,e. ⇩[s, d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃G, K⦄ ⊢ ➡[h, g] 𝐈⦃T⦄.
/3 width=8 by crx_lift/ qed-.
