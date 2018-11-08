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

include "static_2/relocation/lex.ma".
include "basic_2/notation/relations/pconveta_4.ma".
include "basic_2/rt_conversion/cpce_ext.ma".

(* PARALLEL ETA-CONVERSION FOR FULL LOCAL ENVIRONMENTS **********************)

definition lpce (h) (G): relation lenv ≝ lex (cpce h G).

interpretation
  "parallel eta-conversion on all entries (local environment)"
  'PConvEta h G L1 L2 = (lpce h G L1 L2).

(* Basic properties *********************************************************)

lemma lpce_bind (h) (G):
      ∀K1,K2. ⦃G,K1⦄ ⊢ ⬌η[h] K2 →
      ∀I1,I2. ⦃G,K1⦄ ⊢ I1 ⬌η[h] I2 → ⦃G,K1.ⓘ{I1}⦄ ⊢ ⬌η[h] K2.ⓘ{I2}.
/2 width=1 by lex_bind/ qed.

(* Advanced properties ******************************************************)

lemma lpce_pair (h) (G):
      ∀K1,K2,V1,V2. ⦃G,K1⦄ ⊢ ⬌η[h] K2 → ⦃G,K1⦄ ⊢ V1 ⬌η[h] V2 →
      ∀I. ⦃G,K1.ⓑ{I}V1⦄ ⊢ ⬌η[h] K2.ⓑ{I}V2.
/2 width=1 by lex_pair/ qed.

(* Basic inversion lemmas ***************************************************)

lemma lpce_inv_atom_sn (h) (G):
      ∀L2. ⦃G,⋆⦄ ⊢ ⬌η[h] L2 → L2 = ⋆.
/2 width=2 by lex_inv_atom_sn/ qed-.

lemma lpce_inv_bind_sn (h) (G):
      ∀I1,L2,K1. ⦃G,K1.ⓘ{I1}⦄ ⊢ ⬌η[h] L2 →
      ∃∃I2,K2. ⦃G,K1⦄ ⊢ ⬌η[h] K2 & ⦃G,K1⦄ ⊢ I1 ⬌η[h] I2 & L2 = K2.ⓘ{I2}.
/2 width=1 by lex_inv_bind_sn/ qed-.

lemma lpce_inv_atom_dx (h) (G):
      ∀L1. ⦃G,L1⦄ ⊢ ⬌η[h] ⋆ → L1 = ⋆.
/2 width=2 by lex_inv_atom_dx/ qed-.

lemma lpce_inv_bind_dx (h) (G):
      ∀I2,L1,K2. ⦃G,L1⦄ ⊢ ⬌η[h] K2.ⓘ{I2} →
      ∃∃I1,K1. ⦃G,K1⦄ ⊢ ⬌η[h] K2 & ⦃G,K1⦄ ⊢ I1 ⬌η[h] I2 & L1 = K1.ⓘ{I1}.
/2 width=1 by lex_inv_bind_dx/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lpce_inv_unit_sn (h) (G):
      ∀I,L2,K1. ⦃G,K1.ⓤ{I}⦄ ⊢ ⬌η[h] L2 →
      ∃∃K2. ⦃G, K1⦄ ⊢ ⬌η[h] K2 & L2 = K2.ⓤ{I}.
/2 width=1 by lex_inv_unit_sn/ qed-.

lemma lpce_inv_pair_sn (h) (G):
      ∀I,L2,K1,V1. ⦃G,K1.ⓑ{I}V1⦄ ⊢ ⬌η[h] L2 →
      ∃∃K2,V2. ⦃G,K1⦄ ⊢ ⬌η[h] K2 & ⦃G,K1⦄ ⊢ V1 ⬌η[h] V2 & L2 = K2.ⓑ{I}V2.
/2 width=1 by lex_inv_pair_sn/ qed-.

lemma lpce_inv_unit_dx (h) (G):
      ∀I,L1,K2. ⦃G,L1⦄ ⊢ ⬌η[h] K2.ⓤ{I} →
      ∃∃K1. ⦃G,K1⦄ ⊢ ⬌η[h] K2 & L1 = K1.ⓤ{I}.
/2 width=1 by lex_inv_unit_dx/ qed-.

lemma lpce_inv_pair_dx (h) (G):
      ∀I,L1,K2,V2. ⦃G,L1⦄ ⊢ ⬌η[h] K2.ⓑ{I}V2 →
      ∃∃K1,V1. ⦃G,K1⦄ ⊢ ⬌η[h] K2 & ⦃G,K1⦄ ⊢ V1 ⬌η[h] V2 & L1 = K1.ⓑ{I}V1.
/2 width=1 by lex_inv_pair_dx/ qed-.

lemma lpce_inv_pair (h) (G):
      ∀I1,I2,L1,L2,V1,V2. ⦃G,L1.ⓑ{I1}V1⦄ ⊢ ⬌η[h] L2.ⓑ{I2}V2 →
      ∧∧ ⦃G,L1⦄ ⊢ ⬌η[h] L2 & ⦃G,L1⦄ ⊢ V1 ⬌η[h] V2 & I1 = I2.
/2 width=1 by lex_inv_pair/ qed-.
