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

include "basic_2/rt_computation/fpbs_fqup.ma".
include "basic_2/rt_computation/fpbg.ma".

(* PROPER PARALLEL RST-COMPUTATION FOR CLOSURES *****************************)

(* Advanced properties with sort-irrelevant equivalence for terms ***********)

lemma fpbg_teqx_div: ∀h,G1,G2,L1,L2,T1,T. ⦃G1,L1,T1⦄ >[h] ⦃G2,L2,T⦄ →
                     ∀T2. T2 ≛ T → ⦃G1,L1,T1⦄ >[h] ⦃G2,L2,T2⦄.
/4 width=5 by fpbg_feqx_trans, teqx_feqx, teqx_sym/ qed-.

(* Properties with plus-iterated structural successor for closures **********)

(* Note: this is used in the closure proof *)
lemma fqup_fpbg: ∀h,G1,G2,L1,L2,T1,T2. ⦃G1,L1,T1⦄ ⬂+ ⦃G2,L2,T2⦄ → ⦃G1,L1,T1⦄ >[h] ⦃G2,L2,T2⦄.
#h #G1 #G2 #L1 #L2 #T1 #T2 #H elim (fqup_inv_step_sn … H) -H
/3 width=5 by fqus_fpbs, fpb_fqu, ex2_3_intro/
qed.
