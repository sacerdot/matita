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

include "basic_2/rt_transition/fpb_lpx.ma".
include "basic_2/rt_computation/fpbs_feqg.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with extended rt-transition on full local environments  *******)

lemma fpbs_lpx_trans (L):
      ∀G1,G2,L1,T1,T2. ❪G1,L1,T1❫ ≥ ❪G2,L,T2❫ →
      ∀L2. ❪G2,L❫ ⊢ ⬈ L2 → ❪G1,L1,T1❫ ≥ ❪G2,L2,T2❫.
/3 width=5 by fpbs_strap1, lpx_fpb/ qed-.

lemma teqg_reqg_lpx_fpbs (S):
      reflexive … S → symmetric … S →
      ∀T1,T2. T1 ≛[S] T2 → ∀L1,L0. L1 ≛[S,T2] L0 →
      ∀G,L2. ❪G,L0❫ ⊢ ⬈ L2 → ❪G,L1,T1❫ ≥ ❪G,L2,T2❫.
/4 width=7 by feqg_fpbs, fpbs_strap1, lpx_fpb, feqg_intro_dx/ qed.
