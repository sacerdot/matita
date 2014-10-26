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

include "basic_2/computation/cpxs_lift.ma".
include "basic_2/computation/fpbs.ma".

(* "QRST" PARALLEL COMPUTATION FOR CLOSURES *********************************)

(* Advanced properties ******************************************************)

lemma lstas_fpbs: ∀h,g,G,L,T1,T2,d2. ⦃G, L⦄ ⊢ T1 •*[h, d2] T2 →
                  ∀d1. d2 ≤ d1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] d1 → ⦃G, L, T1⦄ ≥[h, g] ⦃G, L, T2⦄.
/3 width=5 by cpxs_fpbs, lstas_cpxs/ qed.

lemma sta_fpbs: ∀h,g,G,L,T,U,d.
                ⦃G, L⦄ ⊢ T ▪[h, g] d+1 → ⦃G, L⦄ ⊢ T •*[h, 1] U →
                ⦃G, L, T⦄ ≥[h, g] ⦃G, L, U⦄.
/2 width=5 by lstas_fpbs/ qed.

(* Note: this is used in the closure proof *)
lemma cpr_lpr_sta_fpbs: ∀h,g,G,L1,L2,T1,T2,U2,d2.
                        ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                        ⦃G, L2⦄ ⊢ T2 ▪[h, g] d2+1 → ⦃G, L2⦄ ⊢ T2 •*[h, 1] U2 →
                        ⦃G, L1, T1⦄ ≥[h, g] ⦃G, L2, U2⦄.
/4 width=5 by fpbs_strap1, cpr_lpr_fpbs, sta_cpx, fpbq_cpx/ qed.
