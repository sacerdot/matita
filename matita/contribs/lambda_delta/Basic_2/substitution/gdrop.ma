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

include "Basic_2/grammar/genv.ma".

(* GLOBAL ENVIRONMENT SLICING ***********************************************)

inductive gdrop (e:nat): relation genv ≝
| gdrop_gt: ∀G. |G| ≤ e → gdrop e G (⋆)
| gdrop_eq: ∀G. |G| = e + 1 → gdrop e G G
| gdrop_lt: ∀I,G1,G2,V. e < |G1| → gdrop e G1 G2 → gdrop e (G1. 𝕓{I} V) G2
.

interpretation "global slicing" 
   'RLDrop e G1 G2 = (gdrop e G1 G2).

(* basic inversion lemmas ***************************************************)

lemma gdrop_inv_gt: ∀G1,G2,e. ⇓[e] G1 ≡ G2 → |G1| ≤ e → G2 = ⋆.
#G1 #G2 #e * -G1 -G2 //
[ #G #H >H -H >commutative_plus #H
  lapply (le_plus_to_le_r … 0 H) -H #H
  lapply (le_n_O_to_eq … H) -H #H destruct
| #I #G1 #G2 #V #H1 #_ #H2
  lapply (le_to_lt_to_lt … H2 H1) -H2 -H1 normalize in ⊢ (? % ? → ?); >commutative_plus #H
  lapply (lt_plus_to_lt_l … 0 H) -H #H
  elim (lt_zero_false … H)
]
qed-.

lemma gdrop_inv_eq: ∀G1,G2,e. ⇓[e] G1 ≡ G2 → |G1| = e + 1 → G1 = G2.
#G1 #G2 #e * -G1 -G2 //
[ #G #H1 #H2 >H2 in H1; -H2 >commutative_plus #H
  lapply (le_plus_to_le_r … 0 H) -H #H
  lapply (le_n_O_to_eq … H) -H #H destruct
| #I #G1 #G2 #V #H1 #_ normalize #H2
  <(injective_plus_l … H2) in H1; -H2 #H
  elim (lt_refl_false … H)
]
qed-.

fact gdrop_inv_lt_aux: ∀I,G,G1,G2,V,e. ⇓[e] G ≡ G2 → G = G1. 𝕓{I} V →
                       e < |G1| → ⇓[e] G1 ≡ G2.
#I #G #G1 #G2 #V #e * -G -G2
[ #G #H1 #H destruct #H2
  lapply (le_to_lt_to_lt … H1 H2) -H1 -H2 normalize in ⊢ (? % ? → ?); >commutative_plus #H
  lapply (lt_plus_to_lt_l … 0 H) -H #H
  elim (lt_zero_false … H)
| #G #H1 #H2 destruct >(injective_plus_l … H1) -H1 #H
  elim (lt_refl_false … H)
| #J #G #G2 #W #_ #HG2 #H destruct //
]
qed.

lemma gdrop_inv_lt: ∀I,G1,G2,V,e.
                    ⇓[e] G1. 𝕓{I} V ≡ G2 → e < |G1| → ⇓[e] G1 ≡ G2.
/2 width=5/ qed-.

(* Basic properties *********************************************************)

lemma gdrop_total: ∀e,G1. ∃G2. ⇓[e] G1 ≡ G2.
#e #G1 elim G1 -G1 /3 width=2/
#I #V #G1 * #G2 #HG12
elim (lt_or_eq_or_gt e (|G1|)) #He
[ /3 width=2/
| destruct /3 width=2/
| @ex_intro [2: @gdrop_gt normalize /2 width=1/ | skip ] (**) (* explicit constructor *)
]
qed.
