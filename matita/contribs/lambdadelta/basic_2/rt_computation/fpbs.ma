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
include "basic_2/notation/relations/predsubtystar_7.ma".
include "basic_2/rt_transition/fpbq.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

definition fpbs: ∀h. tri_relation genv lenv term ≝
                 λh. tri_TC … (fpbq h).

interpretation "parallel rst-computation (closure)"
   'PRedSubTyStar  h G1 L1 T1 G2 L2 T2 = (fpbs h G1 L1 T1 G2 L2 T2).

(* Basic eliminators ********************************************************)

lemma fpbs_ind: ∀h,G1,L1,T1. ∀Q:relation3 genv lenv term. Q G1 L1 T1 →
                (∀G,G2,L,L2,T,T2. ❪G1,L1,T1❫ ≥[h] ❪G,L,T❫ → ❪G,L,T❫ ≽[h] ❪G2,L2,T2❫ → Q G L T → Q G2 L2 T2) →
                ∀G2,L2,T2. ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫ → Q G2 L2 T2.
/3 width=8 by tri_TC_star_ind/ qed-.

lemma fpbs_ind_dx: ∀h,G2,L2,T2. ∀Q:relation3 genv lenv term. Q G2 L2 T2 →
                   (∀G1,G,L1,L,T1,T. ❪G1,L1,T1❫ ≽[h] ❪G,L,T❫ → ❪G,L,T❫ ≥[h] ❪G2,L2,T2❫ → Q G L T → Q G1 L1 T1) →
                   ∀G1,L1,T1. ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫ → Q G1 L1 T1.
/3 width=8 by tri_TC_star_ind_dx/ qed-.

(* Basic properties *********************************************************)

lemma fpbs_refl: ∀h. tri_reflexive … (fpbs h).
/2 width=1 by tri_inj/ qed.

lemma fpbq_fpbs: ∀h,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≽[h] ❪G2,L2,T2❫ →
                 ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫.
/2 width=1 by tri_inj/ qed.

lemma fpbs_strap1: ∀h,G1,G,G2,L1,L,L2,T1,T,T2. ❪G1,L1,T1❫ ≥[h] ❪G,L,T❫ →
                   ❪G,L,T❫ ≽[h] ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫.
/2 width=5 by tri_step/ qed-.

lemma fpbs_strap2: ∀h,G1,G,G2,L1,L,L2,T1,T,T2. ❪G1,L1,T1❫ ≽[h] ❪G,L,T❫ →
                   ❪G,L,T❫ ≥[h] ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫.
/2 width=5 by tri_TC_strap/ qed-.

(* Basic_2A1: uses: lleq_fpbs fleq_fpbs *)
lemma feqx_fpbs: ∀h,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ≛ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫.
/3 width=1 by fpbq_fpbs, fpbq_feqx/ qed.

(* Basic_2A1: uses: fpbs_lleq_trans *)
lemma fpbs_feqx_trans: ∀h,G1,G,L1,L,T1,T. ❪G1,L1,T1❫ ≥[h] ❪G,L,T❫ →
                       ∀G2,L2,T2. ❪G,L,T❫ ≛ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫.
/3 width=9 by fpbs_strap1, fpbq_feqx/ qed-.

(* Basic_2A1: uses: lleq_fpbs_trans *)
lemma feqx_fpbs_trans: ∀h,G,G2,L,L2,T,T2. ❪G,L,T❫ ≥[h] ❪G2,L2,T2❫ →
                       ∀G1,L1,T1. ❪G1,L1,T1❫ ≛ ❪G,L,T❫ → ❪G1,L1,T1❫ ≥[h] ❪G2,L2,T2❫.
/3 width=5 by fpbs_strap2, fpbq_feqx/ qed-.

lemma teqx_reqx_lpx_fpbs: ∀h,T1,T2. T1 ≛ T2 → ∀L1,L0. L1 ≛[T2] L0 →
                          ∀G,L2. ❪G,L0❫ ⊢ ⬈[h] L2 → ❪G,L1,T1❫ ≥[h] ❪G,L2,T2❫.
/4 width=5 by feqx_fpbs, fpbs_strap1, fpbq_lpx, feqx_intro_dx/ qed.

(* Basic_2A1: removed theorems 3:
              fpb_fpbsa_trans fpbs_fpbsa fpbsa_inv_fpbs
*)
