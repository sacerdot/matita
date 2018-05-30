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

include "basic_2/notation/relations/predsnstar_4.ma".
include "basic_2/relocation/lex.ma".
include "basic_2/rt_computation/cpms.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

definition lprs (h) (G): relation lenv ≝
                         lex (λL.cpms h G L 0).

interpretation
   "parallel r-computation on all entries (local environment)"
   'PRedSnStar h G L1 L2 = (lprs h G L1 L2).

(* Basic properties *********************************************************)

lemma lprs_refl (h) (G): ∀L. ⦃G, L⦄ ⊢ ➡*[h] L.
/2 width=1 by lex_refl/ qed.

(* Basic_2A1: uses: lprs_pair_refl *)
lemma lprs_bind_refl_dx (h) (G): ∀L1,L2. ⦃G, L1⦄ ⊢ ➡*[h] L2 →
                                 ∀I. ⦃G, L1.ⓘ{I}⦄ ⊢ ➡*[h] L2.ⓘ{I}.
/2 width=1 by lex_bind_refl_dx/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: uses: lprs_inv_atom1 *)
lemma lprs_inv_atom_sn (h) (G): ∀L2. ⦃G, ⋆⦄ ⊢ ➡*[h] L2 → L2 = ⋆.
/2 width=2 by lex_inv_atom_sn/ qed-.

(* Basic_2A1: uses: lprs_inv_atom2 *)
lemma lprs_inv_atom_dx (h) (G): ∀L1. ⦃G, L1⦄ ⊢ ➡*[h] ⋆ → L1 = ⋆.
/2 width=2 by lex_inv_atom_dx/ qed-.
