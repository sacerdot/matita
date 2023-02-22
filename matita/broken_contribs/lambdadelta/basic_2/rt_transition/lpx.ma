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

include "basic_2/notation/relations/predtysn_3.ma".
include "static_2/relocation/lex.ma".
include "basic_2/rt_transition/cpx_ext.ma".

(* EXTENDED PARALLEL RT-TRANSITION FOR FULL LOCAL ENVIRONMENTS **************)

definition lpx (G): relation lenv ≝ lex (cpx G).

interpretation
  "extended parallel rt-transition on all entries (local environment)"
  'PRedTySn G L1 L2 = (lpx G L1 L2).

(* Basic properties *********************************************************)

lemma lpx_bind (G):
      ∀K1,K2. ❨G,K1❩ ⊢ ⬈ K2 → ∀I1,I2. ❨G,K1❩ ⊢ I1 ⬈ I2 →
      ❨G,K1.ⓘ[I1]❩ ⊢ ⬈ K2.ⓘ[I2].
/2 width=1 by lex_bind/ qed.

lemma lpx_refl (G): reflexive … (lpx G).
/2 width=1 by lex_refl/ qed.

(* Advanced properties ******************************************************)

lemma lpx_bind_refl_dx (G):
      ∀K1,K2. ❨G,K1❩ ⊢ ⬈ K2 →
      ∀I. ❨G,K1.ⓘ[I]❩ ⊢ ⬈ K2.ⓘ[I].
/2 width=1 by lex_bind_refl_dx/ qed.

lemma lpx_pair (G):
      ∀K1,K2. ❨G,K1❩ ⊢ ⬈ K2 → ∀V1,V2. ❨G,K1❩ ⊢ V1 ⬈ V2 →
      ∀I.❨G,K1.ⓑ[I]V1❩ ⊢ ⬈ K2.ⓑ[I]V2.
/2 width=1 by lex_pair/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: was: lpx_inv_atom1 *)
lemma lpx_inv_atom_sn (G):
      ∀L2. ❨G,⋆❩ ⊢ ⬈ L2 → L2 = ⋆.
/2 width=2 by lex_inv_atom_sn/ qed-.

lemma lpx_inv_bind_sn (G):
      ∀I1,L2,K1. ❨G,K1.ⓘ[I1]❩ ⊢ ⬈ L2 →
      ∃∃I2,K2. ❨G,K1❩ ⊢ ⬈ K2 & ❨G,K1❩ ⊢ I1 ⬈ I2 & L2 = K2.ⓘ[I2].
/2 width=1 by lex_inv_bind_sn/ qed-.

(* Basic_2A1: was: lpx_inv_atom2 *)
lemma lpx_inv_atom_dx (G):
      ∀L1. ❨G,L1❩ ⊢ ⬈ ⋆ → L1 = ⋆.
/2 width=2 by lex_inv_atom_dx/ qed-.

lemma lpx_inv_bind_dx (G):
      ∀I2,L1,K2. ❨G,L1❩ ⊢ ⬈ K2.ⓘ[I2] →
      ∃∃I1,K1. ❨G,K1❩ ⊢ ⬈ K2 & ❨G,K1❩ ⊢ I1 ⬈ I2 & L1 = K1.ⓘ[I1].
/2 width=1 by lex_inv_bind_dx/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lpx_inv_unit_sn (G):
      ∀I,L2,K1. ❨G,K1.ⓤ[I]❩ ⊢ ⬈ L2 →
      ∃∃K2. ❨G,K1❩ ⊢ ⬈ K2 & L2 = K2.ⓤ[I].
/2 width=1 by lex_inv_unit_sn/ qed-.

(* Basic_2A1: was: lpx_inv_pair1 *)
lemma lpx_inv_pair_sn (G):
      ∀I,L2,K1,V1. ❨G,K1.ⓑ[I]V1❩ ⊢ ⬈ L2 →
      ∃∃K2,V2. ❨G,K1❩ ⊢ ⬈ K2 & ❨G,K1❩ ⊢ V1 ⬈ V2 & L2 = K2.ⓑ[I]V2.
/2 width=1 by lex_inv_pair_sn/ qed-.

lemma lpx_inv_unit_dx (G):
      ∀I,L1,K2. ❨G,L1❩ ⊢ ⬈ K2.ⓤ[I] →
      ∃∃K1. ❨G,K1❩ ⊢ ⬈ K2 & L1 = K1.ⓤ[I].
/2 width=1 by lex_inv_unit_dx/ qed-.

(* Basic_2A1: was: lpx_inv_pair2 *)
lemma lpx_inv_pair_dx (G):
      ∀I,L1,K2,V2. ❨G,L1❩ ⊢ ⬈ K2.ⓑ[I]V2 →
      ∃∃K1,V1. ❨G,K1❩ ⊢ ⬈ K2 & ❨G,K1❩ ⊢ V1 ⬈ V2 & L1 = K1.ⓑ[I]V1.
/2 width=1 by lex_inv_pair_dx/ qed-.

lemma lpx_inv_pair (G):
      ∀I1,I2,L1,L2,V1,V2. ❨G,L1.ⓑ[I1]V1❩ ⊢ ⬈ L2.ⓑ[I2]V2 →
      ∧∧ ❨G,L1❩ ⊢ ⬈ L2 & ❨G,L1❩ ⊢ V1 ⬈ V2 & I1 = I2.
/2 width=1 by lex_inv_pair/ qed-.
