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

include "basic_2/rt_transition/cpm_fpb.ma".
include "basic_2/rt_transition/cpm_fpbc.ma".
include "basic_2/rt_computation/fpbg_fqup.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

(* Properties with t-bound rt-transition for terms **************************)

lemma cpm_tneqx_cpm_fpbg (h) (G) (L):
      ∀n1,T1,T. ❪G,L❫ ⊢ T1 ➡[h,n1] T → (T1 ≅ T → ⊥) →
      ∀n2,T2. ❪G,L❫ ⊢ T ➡[h,n2] T2 → ❪G,L,T1❫ > ❪G,L,T2❫.
/4 width=5 by fpbc_fpbs_fpbg, fpb_fpbs, cpm_fwd_fpbc, cpm_fwd_fpb/
qed.
