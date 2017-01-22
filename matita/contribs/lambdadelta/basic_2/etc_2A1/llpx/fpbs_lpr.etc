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

include "basic_2/reduction/cpx_lift.ma".
include "basic_2/reduction/llpx_lpr.ma".
include "basic_2/computation/fpbs.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Properties on sn parallel reduction for local environments ***************)

(* Note: this is used in the closure proof *)
(* Note: original proof: /4 width=5 by fpbs_strap1, lpr_fpb, cpr_fpb/ *)
(* Note: this should be moved *)
lemma cpr_lpr_fpbs: ∀h,g,G,L1,L2,T1,T2. ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                    ⦃G, L1, T1⦄ ≥[h, g] ⦃G, L2, T2⦄.
/5 width=5 by fpbs_strap1, cpr_fpb, fpb_llpx, lpr_llpx/ qed.

(* Note: this is used in the closure proof *)
(* Note: this should be moved *)
lemma cpr_lpr_ssta_fpbs: ∀h,g,G,L1,L2,T1,T2,U2,l2.
                         ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                         ⦃G, L2⦄ ⊢ T2 ▪[h, g] l2+1 → ⦃G, L2⦄ ⊢ T2 •[h, g] U2 →
                         ⦃G, L1, T1⦄ ≥[h, g] ⦃G, L2, U2⦄.
/4 width=5 by fpbs_strap1, cpr_lpr_fpbs, ssta_cpx, fpb_cpx/ qed.
