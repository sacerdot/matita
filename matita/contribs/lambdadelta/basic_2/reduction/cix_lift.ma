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

lemma cix_lref: ∀h,g,L,i. ⇩[0, i] L ≡ ⋆ → ⦃h, L⦄ ⊢ 𝐈[g]⦃#i⦄.
#h #g #L #i #HL #H elim (crx_inv_lref … H) -h #I #K #V #HLK
lapply (ldrop_mono … HLK … HL) -L -i #H destruct
qed.

(* Properties on relocation *************************************************)

lemma cix_lift: ∀h,g,K,T. ⦃h, K⦄ ⊢ 𝐈[g]⦃T⦄ → ∀L,d,e. ⇩[d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃h, L⦄ ⊢ 𝐈[g]⦃U⦄.
/3 width=7 by crx_inv_lift/ qed.

lemma cix_inv_lift: ∀h,g,L,U. ⦃h, L⦄ ⊢ 𝐈[g]⦃U⦄ → ∀K,d,e. ⇩[d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃h, K⦄ ⊢ 𝐈[g]⦃T⦄.
/3 width=7/ qed-.
