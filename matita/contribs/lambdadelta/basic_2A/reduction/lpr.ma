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

include "basic_2A/notation/relations/predsn_3.ma".
include "basic_2A/substitution/lpx_sn.ma".
include "basic_2A/reduction/cpr.ma".

(* SN PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS *****************************)

definition lpr: relation3 genv lenv lenv ≝ λG. lpx_sn (cpr G).

interpretation "parallel reduction (local environment, sn variant)"
   'PRedSn G L1 L2 = (lpr G L1 L2).

(* Basic inversion lemmas ***************************************************)

lemma lpr_inv_atom1: ∀G,L2. ⦃G, ⋆⦄ ⊢ ➡ L2 → L2 = ⋆.
/2 width=4 by lpx_sn_inv_atom1_aux/ qed-.

lemma lpr_inv_pair1: ∀I,G,K1,V1,L2. ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡ L2 →
                     ∃∃K2,V2. ⦃G, K1⦄ ⊢ ➡ K2 & ⦃G, K1⦄ ⊢ V1 ➡ V2 & L2 = K2.ⓑ{I}V2.
/2 width=3 by lpx_sn_inv_pair1_aux/ qed-.

lemma lpr_inv_atom2: ∀G,L1. ⦃G, L1⦄ ⊢ ➡ ⋆ → L1 = ⋆.
/2 width=4 by lpx_sn_inv_atom2_aux/ qed-.

lemma lpr_inv_pair2: ∀I,G,L1,K2,V2. ⦃G, L1⦄ ⊢ ➡ K2.ⓑ{I}V2 →
                     ∃∃K1,V1. ⦃G, K1⦄ ⊢ ➡ K2 & ⦃G, K1⦄ ⊢ V1 ➡ V2 & L1 = K1. ⓑ{I} V1.
/2 width=3 by lpx_sn_inv_pair2_aux/ qed-.

(* Basic properties *********************************************************)

(* Note: lemma 250 *)
lemma lpr_refl: ∀G,L. ⦃G, L⦄ ⊢ ➡ L.
/2 width=1 by lpx_sn_refl/ qed.

lemma lpr_pair: ∀I,G,K1,K2,V1,V2. ⦃G, K1⦄ ⊢ ➡ K2 → ⦃G, K1⦄ ⊢ V1 ➡ V2 →
                ⦃G, K1.ⓑ{I}V1⦄ ⊢ ➡ K2.ⓑ{I}V2.
/2 width=1 by lpx_sn_pair/ qed.

(* Basic forward lemmas *****************************************************)

lemma lpr_fwd_length: ∀G,L1,L2. ⦃G, L1⦄ ⊢ ➡ L2 → |L1| = |L2|.
/2 width=2 by lpx_sn_fwd_length/ qed-.
