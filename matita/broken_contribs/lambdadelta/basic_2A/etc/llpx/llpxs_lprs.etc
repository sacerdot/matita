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

include "basic_2/reduction/llpx_lpr.ma".
include "basic_2/computation/lprs.ma".
include "basic_2/computation/llpxs.ma".

(* LAZY SN EXTENDED PARALLEL COMPUTATION ON LOCAL ENVIRONMENTS **************)

(* Properties on sn parallel computation ************************************)

(* Note: this should be moved *)
lemma lprs_llpxs: ∀h,g,G,L1,L2,T,d. ⦃G, L1⦄ ⊢ ➡* L2 → ⦃G, L1⦄ ⊢ ➡*[h, g, T, d] L2.
normalize /3 width=3 by lpr_llpx, monotonic_TC/ qed.
