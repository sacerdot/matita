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

include "basic_2/rt_transition/fpbq_fpb.ma".
include "basic_2/rt_computation/fpbs.ma".

(* PARALLEL RST-COMPUTATION FOR CLOSURES ************************************)

(* Properties with proper parallel rst-reduction on closures ****************)

lemma fpb_fpbs: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ≻[h] ⦃G2,L2,T2⦄ →
                ⦃G1,L1,T1⦄ ≥[h] ⦃G2,L2,T2⦄.
/3 width=1 by fpbq_fpbs, fpb_fpbq/ qed.
