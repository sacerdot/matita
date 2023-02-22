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

include "basic_2/relocation/llpx_sn_lpx_sn.ma".
include "basic_2/reduction/lpr.ma".
include "basic_2/reduction/llpx.ma".

(* LAZY SN EXTENDED PARALLEL REDUCTION FOR LOCAL ENVIRONMENTS ***************)

(* Properties on sn parallel reduction **************************************)

(* Note: this should be moved *)
lemma lpr_llpx: ∀h,g,G,L1,L2,T,d. ⦃G, L1⦄ ⊢ ➡ L2 → ⦃G, L1⦄ ⊢ ➡[h, g, T, d] L2.
/3 width=4 by cpr_cpx, lpx_sn_llpx_sn, llpx_sn_co/ qed.
