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

include "basic_2/rt_transition/fpbc_lpx.ma".
include "basic_2/rt_computation/fpbs_lpxs.ma".
include "basic_2/rt_computation/fpbg_fqup.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

(* Properties with extended rt-computation on full local environments *******)

(* Basic_2A1: uses: lpxs_fpbg *)
lemma lpxs_rneqx_fpbg:
      ∀G,L1,L2,T. ❪G,L1❫ ⊢ ⬈* L2 →
      (L1 ≅[T] L2 → ⊥) → ❪G,L1,T❫ > ❪G,L2,T❫.
#G #L1 #L2 #T #H #H0
elim (lpxs_rneqg_inv_step_sn … H … H0) -H -H0
/4 width=10 by fpbc_fpbs_fpbg, lpxs_feqg_fpbs, lpx_fpbc, feqg_intro_sn, sfull_dec/
qed.
