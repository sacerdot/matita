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

include "ground_2/lib/star.ma".
include "basic_2/notation/relations/predsubtystar_8.ma".
include "basic_2/rt_transition/fpbq.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

definition fpbs: ∀h. sd h → tri_relation genv lenv term ≝
                 λh,o. tri_TC … (fpbq h o).

interpretation "parallel rst-computation (closure)"
   'PRedSubTyStar  h o G1 L1 T1 G2 L2 T2 = (fpbs h o G1 L1 T1 G2 L2 T2).

(* Basic eliminators ********************************************************)

lemma fpbs_ind: ∀h,o,G1,L1,T1. ∀R:relation3 genv lenv term. R G1 L1 T1 →
                (∀G,G2,L,L2,T,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≽[h, o] ⦃G2, L2, T2⦄ → R G L T → R G2 L2 T2) →
                ∀G2,L2,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ → R G2 L2 T2.
/3 width=8 by tri_TC_star_ind/ qed-.

lemma fpbs_ind_dx: ∀h,o,G2,L2,T2. ∀R:relation3 genv lenv term. R G2 L2 T2 →
                   (∀G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G, L, T⦄ → ⦃G, L, T⦄ ≥[h, o] ⦃G2, L2, T2⦄ → R G L T → R G1 L1 T1) →
                   ∀G1,L1,T1. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄ → R G1 L1 T1.
/3 width=8 by tri_TC_star_ind_dx/ qed-.

(* Basic properties *********************************************************)

lemma fpbs_refl: ∀h,o. tri_reflexive … (fpbs h o).
/2 width=1 by tri_inj/ qed.

lemma fpbq_fpbs: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/2 width=1 by tri_inj/ qed.

lemma fpbs_strap1: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≽[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/2 width=5 by tri_step/ qed-.

lemma fpbs_strap2: ∀h,o,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≽[h, o] ⦃G, L, T⦄ →
                   ⦃G, L, T⦄ ≥[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/2 width=5 by tri_TC_strap/ qed-.

(* Basic_2A1: uses: lleq_fpbs *)
lemma ffdeq_fpbs: ∀h,o,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=1 by fpbq_fpbs, fpbq_ffdeq/ qed.

(* Basic_2A1: uses: fpbs_lleq_trans *)
lemma fpbs_ffdeq_trans: ∀h,o,G1,G,L1,L,T1,T. ⦃G1, L1, T1⦄ ≥[h, o] ⦃G, L, T⦄ →
                        ∀G2,L2,T2. ⦃G, L, T⦄ ≛[h, o] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=9 by fpbs_strap1, fpbq_ffdeq/ qed-.

(* Basic_2A1: uses: lleq_fpbs_trans *)
lemma ffdeq_fpbs_trans: ∀h,o,G,G2,L,L2,T,T2. ⦃G, L, T⦄ ≥[h, o] ⦃G2, L2, T2⦄ →
                        ∀G1,L1,T1. ⦃G1, L1, T1⦄ ≛[h, o] ⦃G, L, T⦄ → ⦃G1, L1, T1⦄ ≥[h, o] ⦃G2, L2, T2⦄.
/3 width=5 by fpbs_strap2, fpbq_ffdeq/ qed-.

(* Basic_2A1: removed theorems 3:
              fpb_fpbsa_trans fpbs_fpbsa fpbsa_inv_fpbs
*)
