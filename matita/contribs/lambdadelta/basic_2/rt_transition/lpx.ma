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

include "basic_2/notation/relations/predtysn_4.ma".
include "basic_2/relocation/lex.ma".
include "basic_2/rt_transition/cpx_ext.ma".

(* UNCOUNTED PARALLEL RT-TRANSITION FOR LOCAL ENVIRONMENTS ******************)

definition lpx: sh → genv → relation lenv ≝
                λh,G. lex (cpx h G).

interpretation
   "uncounted parallel rt-transition (local environment)"
   'PRedTySn h G L1 L2 = (lpx h G L1 L2).

(* Basic properties *********************************************************)

lemma lpx_bind: ∀h,G,K1,K2. ⦃G, K1⦄ ⊢ ⬈[h] K2 →
                ∀I1,I2. ⦃G, K1⦄ ⊢ I1 ⬈[h] I2 → ⦃G, K1.ⓘ{I1}⦄ ⊢ ⬈[h] K2.ⓘ{I2}.
/2 width=1 by lex_bind/ qed.

lemma lpx_refl: ∀h,G. reflexive … (lpx h G).
/2 width=1 by lex_refl/ qed.

(* Advanced properties ******************************************************)

lemma lpx_bind_refl_dx: ∀h,G,K1,K2. ⦃G, K1⦄ ⊢ ⬈[h] K2 →
                        ∀I. ⦃G, K1.ⓘ{I}⦄ ⊢ ⬈[h] K2.ⓘ{I}.
/2 width=1 by lex_bind_refl_dx/ qed.
(*
lemma lpx_pair: ∀h,g,I,G,K1,K2,V1,V2. ⦃G, K1⦄ ⊢ ⬈[h] K2 → ⦃G, K1⦄ ⊢ V1 ⬈[h] V2 →
                ⦃G, K1.ⓑ{I}V1⦄ ⊢ ⬈[h] K2.ⓑ{I}V2.
/2 width=1 by lpx_sn_pair/ qed.
*)
(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: was: lpx_inv_atom1 *)
lemma lpx_inv_atom_sn: ∀h,G,L2. ⦃G, ⋆⦄ ⊢ ⬈[h] L2 → L2 = ⋆.
/2 width=2 by lex_inv_atom_sn/ qed-.

lemma lpx_inv_bind_sn: ∀h,I1,G,L2,K1. ⦃G, K1.ⓘ{I1}⦄ ⊢ ⬈[h] L2 →
                       ∃∃I2,K2. ⦃G, K1⦄ ⊢ ⬈[h] K2 & ⦃G, K1⦄ ⊢ I1 ⬈[h] I2 &
                                L2 = K2.ⓘ{I2}.
/2 width=1 by lex_inv_bind_sn/ qed-.

(* Basic_2A1: was: lpx_inv_atom2 *)
lemma lpx_inv_atom_dx: ∀h,G,L1.  ⦃G, L1⦄ ⊢ ⬈[h] ⋆ → L1 = ⋆.
/2 width=2 by lex_inv_atom_dx/ qed-.

lemma lpx_inv_bind_dx: ∀h,I2,G,L1,K2.  ⦃G, L1⦄ ⊢ ⬈[h] K2.ⓘ{I2} →
                       ∃∃I1,K1. ⦃G, K1⦄ ⊢ ⬈[h] K2 & ⦃G, K1⦄ ⊢ I1 ⬈[h] I2 &
                                L1 = K1.ⓘ{I1}.
/2 width=1 by lex_inv_bind_dx/ qed-.

(* Advanced inversion lemmas ************************************************)

(* Basic_2A1: was: lpx_inv_pair1 *)
lemma lpx_inv_pair_sn: ∀h,I,G,L2,K1,V1. ⦃G, K1.ⓑ{I}V1⦄ ⊢ ⬈[h] L2 →
                       ∃∃K2,V2. ⦃G, K1⦄ ⊢ ⬈[h] K2 & ⦃G, K1⦄ ⊢ V1 ⬈[h] V2 &
                                L2 = K2.ⓑ{I}V2.
/2 width=1 by lex_inv_pair_sn/ qed-.

(* Basic_2A1: was: lpx_inv_pair2 *)
lemma lpx_inv_pair_dx: ∀h,I,G,L1,K2,V2.  ⦃G, L1⦄ ⊢ ⬈[h] K2.ⓑ{I}V2 →
                       ∃∃K1,V1. ⦃G, K1⦄ ⊢ ⬈[h] K2 & ⦃G, K1⦄ ⊢ V1 ⬈[h] V2 &
                                L1 = K1.ⓑ{I}V1.
/2 width=1 by lex_inv_pair_dx/ qed-.

lemma lpx_inv_pair: ∀h,I1,I2,G,L1,L2,V1,V2.  ⦃G, L1.ⓑ{I1}V1⦄ ⊢ ⬈[h] L2.ⓑ{I2}V2 →
                    ∧∧ ⦃G, L1⦄ ⊢ ⬈[h] L2 & ⦃G, L1⦄ ⊢ V1 ⬈[h] V2 & I1 = I2.
/2 width=1 by lex_inv_pair/ qed-.
