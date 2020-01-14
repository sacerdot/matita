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

include "basic_2/notation/relations/predsn_5.ma".
include "static_2/relocation/lex.ma".
include "basic_2/rt_transition/cpr_ext.ma".

(* PARALLEL R-TRANSITION FOR FULL LOCAL ENVIRONMENTS ************************)

definition lpr (h) (n) (G): relation lenv ≝
           lex (λL. cpm h G L n).

interpretation
   "parallel rt-transition (full local environment)"
   'PRedSn h n G L1 L2 = (lpr h n G L1 L2).

(* Basic properties *********************************************************)

lemma lpr_bind (h) (G): ∀K1,K2. ❪G,K1❫ ⊢ ➡[h,0] K2 →
                        ∀I1,I2. ❪G,K1❫ ⊢ I1 ➡[h,0] I2 → ❪G,K1.ⓘ[I1]❫ ⊢ ➡[h,0] K2.ⓘ[I2].
/2 width=1 by lex_bind/ qed.

(* Note: lemma 250 *)
lemma lpr_refl (h) (G): reflexive … (lpr h 0 G).
/2 width=1 by lex_refl/ qed.

(* Advanced properties ******************************************************)

lemma lpr_bind_refl_dx (h) (G): ∀K1,K2. ❪G,K1❫ ⊢ ➡[h,0] K2 →
                                ∀I. ❪G,K1.ⓘ[I]❫ ⊢ ➡[h,0] K2.ⓘ[I].
/2 width=1 by lex_bind_refl_dx/ qed.

lemma lpr_pair (h) (G): ∀K1,K2,V1,V2. ❪G,K1❫ ⊢ ➡[h,0] K2 → ❪G,K1❫ ⊢ V1 ➡[h,0] V2 →
                        ∀I. ❪G,K1.ⓑ[I]V1❫ ⊢ ➡[h,0] K2.ⓑ[I]V2.
/2 width=1 by lex_pair/ qed.

(* Basic inversion lemmas ***************************************************)

(* Basic_2A1: was: lpr_inv_atom1 *)
(* Basic_1: includes: wcpr0_gen_sort *)
lemma lpr_inv_atom_sn (h) (G): ∀L2. ❪G,⋆❫ ⊢ ➡[h,0] L2 → L2 = ⋆.
/2 width=2 by lex_inv_atom_sn/ qed-.

lemma lpr_inv_bind_sn (h) (G): ∀I1,L2,K1. ❪G,K1.ⓘ[I1]❫ ⊢ ➡[h,0] L2 →
                               ∃∃I2,K2. ❪G,K1❫ ⊢ ➡[h,0] K2 & ❪G,K1❫ ⊢ I1 ➡[h,0] I2 &
                                        L2 = K2.ⓘ[I2].
/2 width=1 by lex_inv_bind_sn/ qed-.

(* Basic_2A1: was: lpr_inv_atom2 *)
lemma lpr_inv_atom_dx (h) (G): ∀L1. ❪G,L1❫ ⊢ ➡[h,0] ⋆ → L1 = ⋆.
/2 width=2 by lex_inv_atom_dx/ qed-.

lemma lpr_inv_bind_dx (h) (G): ∀I2,L1,K2. ❪G,L1❫ ⊢ ➡[h,0] K2.ⓘ[I2] →
                               ∃∃I1,K1. ❪G,K1❫ ⊢ ➡[h,0] K2 & ❪G,K1❫ ⊢ I1 ➡[h,0] I2 &
                                        L1 = K1.ⓘ[I1].
/2 width=1 by lex_inv_bind_dx/ qed-.

(* Advanced inversion lemmas ************************************************)

lemma lpr_inv_unit_sn (h) (G): ∀I,L2,K1. ❪G,K1.ⓤ[I]❫ ⊢ ➡[h,0] L2 →
                               ∃∃K2. ❪G,K1❫ ⊢ ➡[h,0] K2 & L2 = K2.ⓤ[I].
/2 width=1 by lex_inv_unit_sn/ qed-.

(* Basic_2A1: was: lpr_inv_pair1 *)
(* Basic_1: includes: wcpr0_gen_head *)
lemma lpr_inv_pair_sn (h) (G): ∀I,L2,K1,V1. ❪G,K1.ⓑ[I]V1❫ ⊢ ➡[h,0] L2 →
                               ∃∃K2,V2. ❪G,K1❫ ⊢ ➡[h,0] K2 & ❪G,K1❫ ⊢ V1 ➡[h,0] V2 &
                                        L2 = K2.ⓑ[I]V2.
/2 width=1 by lex_inv_pair_sn/ qed-.

lemma lpr_inv_unit_dx (h) (G): ∀I,L1,K2. ❪G,L1❫ ⊢ ➡[h,0] K2.ⓤ[I] →
                               ∃∃K1. ❪G,K1❫ ⊢ ➡[h,0] K2 & L1 = K1.ⓤ[I].
/2 width=1 by lex_inv_unit_dx/ qed-.

(* Basic_2A1: was: lpr_inv_pair2 *)
lemma lpr_inv_pair_dx (h) (G): ∀I,L1,K2,V2. ❪G,L1❫ ⊢ ➡[h,0] K2.ⓑ[I]V2 →
                               ∃∃K1,V1. ❪G,K1❫ ⊢ ➡[h,0] K2 & ❪G,K1❫ ⊢ V1 ➡[h,0] V2 &
                                        L1 = K1.ⓑ[I]V1.
/2 width=1 by lex_inv_pair_dx/ qed-.

lemma lpr_inv_pair (h) (G): ∀I1,I2,L1,L2,V1,V2. ❪G,L1.ⓑ[I1]V1❫ ⊢ ➡[h,0] L2.ⓑ[I2]V2 →
                            ∧∧ ❪G,L1❫ ⊢ ➡[h,0] L2 & ❪G,L1❫ ⊢ V1 ➡[h,0] V2 & I1 = I2.
/2 width=1 by lex_inv_pair/ qed-.

(* Basic_1: removed theorems 3: wcpr0_getl wcpr0_getl_back
                                pr0_subst1_back
*)
