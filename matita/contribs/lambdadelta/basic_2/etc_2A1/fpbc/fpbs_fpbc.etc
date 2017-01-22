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

include "basic_2/reduction/fpbc.ma".
include "basic_2/computation/fpbs_fleq.ma".

(* "QRST" PARALLEL COMPUTATION FOR CLOSURES *********************************)

(* Properties on "qrst" proper parallel reduction for closures **************)

lemma fpbc_fpbs: ∀h,g,G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ≻≡[h, g] ⦃G2, L2, T2⦄ →
                 ⦃G1, L1, T1⦄ ≥[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G2 #L1 #L2 #T1 #T2 *
/3 width=5 by fpbu_fwd_fpb, fpbs_strap2, fleq_fpbs/
qed-.
