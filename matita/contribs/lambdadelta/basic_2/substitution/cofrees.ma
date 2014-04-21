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

include "basic_2/notation/relations/cofreestar_3.ma".
include "basic_2/substitution/cpys.ma".

(* CONTEXT-SENSITIVE EXCLUSION FROM FREE VARIABLES **************************)

definition cofrees: relation3 nat lenv term ≝
                    λd,L,U1. ∀U2. ⦃⋆, L⦄ ⊢ U1 ▶*[d, ∞] U2 → ∃T2. ⇧[d, 1] T2 ≡ U2.

interpretation
   "context-sensitive exclusion from free variables (term)"
   'CoFreeStar d L T = (cofrees d L T).

(* Basic forward lemmas *****************************************************)

lemma cofrees_fwd_lift: ∀L,U,d. d ~ϵ 𝐅*⦃L, U⦄ → ∃T. ⇧[d, 1] T ≡ U.
/2 width=1 by/ qed-.

lemma nlift_frees: ∀L,U,d. (∀T. ⇧[d, 1] T ≡ U → ⊥) → (d ~ϵ 𝐅*⦃L, U⦄ → ⊥).
#L #U #d #HnTU #H elim (cofrees_fwd_lift … H) -H /2 width=2 by/
qed-.
