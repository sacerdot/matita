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

include "basic_2/notation/relations/rdrop_3.ma".
include "basic_2/grammar/genv.ma".

(* GLOBAL ENVIRONMENT READING ***********************************************)

inductive gget (e:nat): relation genv ≝
| gget_gt: ∀G. |G| ≤ e → gget e G (⋆)
| gget_eq: ∀G. |G| = e + 1 → gget e G G
| gget_lt: ∀I,G1,G2,V. e < |G1| → gget e G1 G2 → gget e (G1. ⓑ{I} V) G2
.

interpretation "global reading"
   'RDrop e G1 G2 = (gget e G1 G2).

(* basic inversion lemmas ***************************************************)

lemma gget_inv_gt: ∀G1,G2,e. ⇩[e] G1 ≡ G2 → |G1| ≤ e → G2 = ⋆.
#G1 #G2 #e * -G1 -G2 //
[ #G #H >H -H >commutative_plus #H (**) (* lemma needed here *)
  lapply (le_plus_to_le_r … 0 H) -H #H
  lapply (le_n_O_to_eq … H) -H #H destruct
| #I #G1 #G2 #V #H1 #_ #H2
  lapply (le_to_lt_to_lt … H2 H1) -H2 -H1 normalize in ⊢ (? % ? → ?); >commutative_plus #H
  lapply (lt_plus_to_lt_l … 0 H) -H #H
  elim (lt_zero_false … H)
]
qed-.

lemma gget_inv_eq: ∀G1,G2,e. ⇩[e] G1 ≡ G2 → |G1| = e + 1 → G1 = G2.
#G1 #G2 #e * -G1 -G2 //
[ #G #H1 #H2 >H2 in H1; -H2 >commutative_plus #H (**) (* lemma needed here *)
  lapply (le_plus_to_le_r … 0 H) -H #H
  lapply (le_n_O_to_eq … H) -H #H destruct
| #I #G1 #G2 #V #H1 #_ normalize #H2
  <(injective_plus_l … H2) in H1; -H2 #H
  elim (lt_refl_false … H)
]
qed-.

fact gget_inv_lt_aux: ∀I,G,G1,G2,V,e. ⇩[e] G ≡ G2 → G = G1. ⓑ{I} V →
                      e < |G1| → ⇩[e] G1 ≡ G2.
#I #G #G1 #G2 #V #e * -G -G2
[ #G #H1 #H destruct #H2
  lapply (le_to_lt_to_lt … H1 H2) -H1 -H2 normalize in ⊢ (? % ? → ?); >commutative_plus #H
  lapply (lt_plus_to_lt_l … 0 H) -H #H
  elim (lt_zero_false … H)
| #G #H1 #H2 destruct >(injective_plus_l … H1) -H1 #H
  elim (lt_refl_false … H)
| #J #G #G2 #W #_ #HG2 #H destruct //
]
qed-.

lemma gget_inv_lt: ∀I,G1,G2,V,e.
                    ⇩[e] G1. ⓑ{I} V ≡ G2 → e < |G1| → ⇩[e] G1 ≡ G2.
/2 width=5 by gget_inv_lt_aux/ qed-.

(* Basic properties *********************************************************)

lemma gget_total: ∀e,G1. ∃G2. ⇩[e] G1 ≡ G2.
#e #G1 elim G1 -G1 /3 width=2/
#I #V #G1 * #G2 #HG12
elim (lt_or_eq_or_gt e (|G1|)) #He
[ /3 width=2/
| destruct /3 width=2/
| @ex_intro [2: @gget_gt normalize /2 width=1/ | skip ] (**) (* explicit constructor *)
]
qed-.
