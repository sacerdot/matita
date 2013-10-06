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

include "basic_2/computation/fpbs_lift.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Main properties **********************************************************)

theorem fpbs_trans: ∀h,g. tri_transitive … (fpbs h g).
/2 width=5 by tri_TC_transitive/ qed-.

(* Advanced properties ******************************************************)

lemma cpr_lpr_ssta_fpbs: ∀h,g,G,L1,L2,T1,T2,U2,l2.
                         ⦃G, L1⦄ ⊢ T1 ➡ T2 → ⦃G, L1⦄ ⊢ ➡ L2 →
                         ⦃G, L2⦄ ⊢ T2 ▪[h, g] l2+1 → ⦃G, L2⦄ ⊢ T2 •[h, g] U2 →
                         ⦃G, L1, T1⦄ ≥[h, g] ⦃G, L2, U2⦄.
/3 width=5 by fpbs_trans, cpr_lpr_fpbs, ssta_fpbs/ qed.
