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

include "basic_2/reduction/crr_lift.ma".
include "basic_2/reduction/cir.ma".

(* IRREDUCIBLE TERMS FOR CONTEXT-SENSITIVE REDUCTION ************************)

(* Properties on relocation *************************************************)

lemma cir_lift: ∀G,K,T. ⦃G, K⦄ ⊢ ➡ 𝐈⦃T⦄ → ∀L,s,d,e. ⇩[s, d, e] L ≡ K →
                ∀U. ⇧[d, e] T ≡ U → ⦃G, L⦄ ⊢ ➡ 𝐈⦃U⦄.
/3 width=8 by crr_inv_lift/ qed.

lemma cir_inv_lift: ∀G,L,U. ⦃G, L⦄ ⊢ ➡ 𝐈⦃U⦄ → ∀K,s,d,e. ⇩[s, d, e] L ≡ K →
                    ∀T. ⇧[d, e] T ≡ U → ⦃G, K⦄ ⊢ ➡ 𝐈⦃T⦄.
/3 width=8 by crr_lift/ qed-.
