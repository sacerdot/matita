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

include "basic_2/notation/relations/predtysnstar_4.ma".
include "static_2/relocation/lex.ma".
include "basic_2/rt_computation/cpxs_ext.ma".

(* UNBOUND PARALLEL RT-COMPUTATION FOR FULL LOCAL ENVIRONMENTS **************)

definition lpxs (h) (G): relation lenv ≝
                         lex (cpxs h G).

interpretation
   "unbound parallel rt-computation on all entries (local environment)"
   'PRedTySnStar h G L1 L2 = (lpxs h G L1 L2).

(* Basic properties *********************************************************)

(* Basic_2A1: uses: lpxs_pair_refl *)
lemma lpxs_bind_refl_dx (h) (G): ∀L1,L2. ❪G,L1❫ ⊢ ⬈*[h] L2 →
                                 ∀I. ❪G,L1.ⓘ[I]❫ ⊢ ⬈*[h] L2.ⓘ[I].
/2 width=1 by lex_bind_refl_dx/ qed.

lemma lpxs_pair (h) (G): ∀L1,L2. ❪G,L1❫ ⊢ ⬈*[h] L2 →
                         ∀V1,V2. ❪G,L1❫ ⊢ V1 ⬈*[h] V2 →
                         ∀I. ❪G,L1.ⓑ[I]V1❫ ⊢ ⬈*[h] L2.ⓑ[I]V2.
/2 width=1 by lex_pair/ qed.

lemma lpxs_refl (h) (G): reflexive … (lpxs h G).
/2 width=1 by lex_refl/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: was: lpxs_inv_atom1 *)
lemma lpxs_inv_atom_sn (h) (G): ∀L2. ❪G,⋆❫ ⊢ ⬈*[h] L2 → L2 = ⋆.
/2 width=2 by lex_inv_atom_sn/ qed-.

lemma lpxs_inv_bind_sn (h) (G): ∀I1,L2,K1. ❪G,K1.ⓘ[I1]❫ ⊢ ⬈*[h] L2 →
                                ∃∃I2,K2. ❪G,K1❫ ⊢ ⬈*[h] K2 & ❪G,K1❫ ⊢ I1 ⬈*[h] I2 & L2 = K2.ⓘ[I2].
/2 width=1 by lex_inv_bind_sn/ qed-.

(* Basic_2A1: was: lpxs_inv_pair1 *)
lemma lpxs_inv_pair_sn (h) (G): ∀I,L2,K1,V1. ❪G,K1.ⓑ[I]V1❫ ⊢ ⬈*[h] L2 →
                                ∃∃K2,V2. ❪G,K1❫ ⊢ ⬈*[h] K2 & ❪G,K1❫ ⊢ V1 ⬈*[h] V2 & L2 = K2.ⓑ[I]V2.
/2 width=1 by lex_inv_pair_sn/ qed-.

(* Basic_2A1: was: lpxs_inv_atom2 *)
lemma lpxs_inv_atom_dx (h) (G): ∀L1. ❪G,L1❫ ⊢ ⬈*[h] ⋆ → L1 = ⋆.
/2 width=2 by lex_inv_atom_dx/ qed-.

(* Basic_2A1: was: lpxs_inv_pair2 *)
lemma lpxs_inv_pair_dx (h) (G): ∀I,L1,K2,V2. ❪G,L1❫ ⊢ ⬈*[h] K2.ⓑ[I]V2 →
                                ∃∃K1,V1. ❪G,K1❫ ⊢ ⬈*[h] K2 & ❪G,K1❫ ⊢ V1 ⬈*[h] V2 & L1 = K1.ⓑ[I]V1.
/2 width=1 by lex_inv_pair_dx/ qed-.

(* Basic eliminators ********************************************************)

(* Basic_2A1: was: lpxs_ind_alt *)
lemma lpxs_ind (h) (G): ∀Q:relation lenv.
                        Q (⋆) (⋆) → (
                          ∀I,K1,K2.
                          ❪G,K1❫ ⊢ ⬈*[h] K2 →
                          Q K1 K2 → Q (K1.ⓘ[I]) (K2.ⓘ[I])
                        ) → (
                          ∀I,K1,K2,V1,V2.
                          ❪G,K1❫ ⊢ ⬈*[h] K2 → ❪G,K1❫ ⊢ V1 ⬈*[h] V2 →
                          Q K1 K2 → Q (K1.ⓑ[I]V1) (K2.ⓑ[I]V2)
                        ) →
                        ∀L1,L2. ❪G,L1❫ ⊢ ⬈*[h] L2 → Q L1 L2.
/3 width=4 by lex_ind/ qed-.
