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

(* CONTEXT-SENSITIVE EXTENDED IRREDUCIBLE TERMS *****************************)

(* Advanced properties ******************************************************)

lemma cix_lref: ∀h,g,G,L,i. ⇩[0, i] L ≡ ⋆ → ⦃G, L⦄ ⊢ 𝐈[h, g]⦃#i⦄.
#h #g #G #L #i #HL #H elim (crx_inv_lref … H) -h #I #K #V #HLK
lapply (ldrop_mono … HLK … HL) -L -i #H destruct
qed.

(* Properties on relocation *************************************************)

lemma cix_lift: ∀h,g,G,K,T. ⦃G, K⦄ ⊢ 𝐈[h, g]⦃T⦄ → ∀L,d,e. ⇩[d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃G, L⦄ ⊢ 𝐈[h, g]⦃U⦄.
/3 width=7 by crx_inv_lift/ qed.

lemma cix_inv_lift: ∀h,g,G,L,U. ⦃G, L⦄ ⊢ 𝐈[h, g]⦃U⦄ → ∀K,d,e. ⇩[d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃G, K⦄ ⊢ 𝐈[h, g]⦃T⦄.
/3 width=7/ qed-.
