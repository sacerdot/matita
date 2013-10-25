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

include "basic_2/computation/fpbg_fpbg.ma".
include "basic_2/computation/fpbr.ma".

(* RESTRICTED "BIG TREE" ORDER FOR CLOSURES *********************************)

(* Advanced forward lemmas **************************************************)
lemma fpbr_fwd_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊃≥[h, g] ⦃G2, L2, T2⦄ →
                     ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
/3 width=5 by fpbr_fwd_fpbg, fpbg_fwd_fpbs/
qed-.

(* Main properties **********************************************************)

theorem fpbr_trans: ∀h,g. tri_transitive … (fpbr h g).
/3 width=5 by fpbr_fwd_fpbs, fpbr_fpbs_trans/ qed-.
