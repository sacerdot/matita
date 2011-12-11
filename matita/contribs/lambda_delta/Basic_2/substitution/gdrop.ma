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

include "Basic_2/substitution/ldrop.ma".

(* GLOBAL ENVIRONMENT SLICING ***********************************************)

inductive gdrop (e:nat) (G1:lenv) : predicate lenv ≝
| gdrop_lt: ∀G2. e < |G1| → ↓[0, |G1| - (e + 1)] G1 ≡ G2 → gdrop e G1 G2
| gdrop_ge: |G1| ≤ e → gdrop e G1 (⋆)
.

interpretation "global slicing" 'RDrop e G1 G2 = (gdrop e G1 G2).

(* basic inversion lemmas ***************************************************)

fact gdrop_inv_atom2_aux: ∀G1,G2,e. ↓[e] G1 ≡ G2 → G2 = ⋆ → |G1| ≤ e.
#G1 #G2 #e * -G2 //
#G2 #He #HG12 #H destruct
lapply (ldrop_fwd_O1_length … HG12) -HG12
>minus_le_minus_minus_comm // -He >le_plus_minus_comm // <minus_n_n
>(commutative_plus e) normalize #H destruct
qed.

lemma gdrop_inv_atom2: ∀G1,e. ↓[e] G1 ≡ ⋆ → |G1| ≤ e.
/2 width=3/ qed-.

lemma gdrop_inv_ge: ∀G1,G2,e. ↓[e] G1 ≡ G2 → |G1| ≤ e → G2 = ⋆.
#G1 #G2 #e * // #G2 #H1 #_ #H2
lapply (lt_to_le_to_lt … H1 H2) -H1 -H2 #He
elim (lt_refl_false … He)
qed-.
