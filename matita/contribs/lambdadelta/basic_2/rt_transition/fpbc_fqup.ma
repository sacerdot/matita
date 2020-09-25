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

include "static_2/static/feqg_fqu.ma".
include "basic_2/rt_transition/fpb_fqup.ma".
include "basic_2/rt_transition/fpbc.ma".

(* PROPER PARALLEL RST-TRANSITION FOR CLOSURES ******************************)

(* Advanced properties ******************************************************)

(* Basic_2A1: uses: fpb_cpx *)
lemma cpx_fpbc (G) (L):
      ∀T1,T2. ❪G,L❫ ⊢ T1 ⬈ T2 → (T1 ≅ T2 → ⊥) → ❪G,L,T1❫ ≻ ❪G,L,T2❫.
/4 width=5 by fpbc_intro, cpx_fpb, feqg_fwd_teqg/ qed.

(* Basic_2A1: uses: fpb_fqu *)
lemma fqu_fpbc (G1) (G2) (L1) (L2) (T1) (T2):
      ❪G1,L1,T1❫ ⬂ ❪G2,L2,T2❫ → ❪G1,L1,T1❫ ≻ ❪G2,L2,T2❫.
/4 width=10 by fpbc_intro, fquq_fpb, fqu_fquq, fqu_fneqg/ qed.
