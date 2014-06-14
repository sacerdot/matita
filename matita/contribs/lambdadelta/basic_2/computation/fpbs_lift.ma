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

include "basic_2/reduction/fpb_lift.ma".
include "basic_2/computation/cpxs_lift.ma".
include "basic_2/computation/fpbs.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Advanced properties ******************************************************)

lemma lstas_fpbs: ∀h,g,G,L,T1,T2,l2. ⦃G, L⦄ ⊢ T1 •*[h, l2] T2 →
                  ∀l1. l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 → ⦃G, L, T1⦄ ≥[h, g] ⦃G, L, T2⦄.
/3 width=5 by cpxs_fpbs, lstas_cpxs/ qed.

lemma sta_fpbs: ∀h,g,G,L,T,U,l.
                ⦃G, L⦄ ⊢ T ▪[h, g] l+1 → ⦃G, L⦄ ⊢ T •[h] U →
                ⦃G, L, T⦄ ≥[h, g] ⦃G, L, U⦄.
/4 width=2 by fpb_fpbs, sta_fpb/ qed.

(* Note: this is used in the closure proof *)
lemma cpr_lpr_sta_fpbs: ∀h,g,G,L1,L2,T1,T2,U2,l2.
                        ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                        ⦃G, L2⦄ ⊢ T2 ▪[h, g] l2+1 → ⦃G, L2⦄ ⊢ T2 •[h] U2 →
                        ⦃G, L1, T1⦄ ≥[h, g] ⦃G, L2, U2⦄.
/4 width=5 by fpbs_strap1, cpr_lpr_fpbs, sta_cpx, fpb_cpx/ qed.
