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

include "basic_2/reducibility/ltpr_ltpss_sn.ma".
include "basic_2/reducibility/ltpr_ltpr.ma".
include "basic_2/reducibility/lfpr.ma".

(* FOCALIZED PARALLEL REDUCTION ON LOCAL ENVIRONMENTS ***********************)

(* Main properties **********************************************************)

theorem lfpr_conf: ∀L0,L1,L2. ⦃L0⦄ ➡ ⦃L1⦄ → ⦃L0⦄ ➡ ⦃L2⦄ →
                   ∃∃L. ⦃L1⦄ ➡ ⦃L⦄ & ⦃L2⦄ ➡ ⦃L⦄.
#K0 #L1 #L2 * #K1 #HK01 #HKL1 * #K2 #HK02 #HKL2
lapply (ltpr_fwd_length … HK01) #H
>(ltpr_fwd_length … HK02) in H; #H
elim (ltpr_conf … HK01 … HK02) -K0 #K #HK1 #HK2
lapply (ltpss_sn_fwd_length … HKL1) #H1
lapply (ltpss_sn_fwd_length … HKL2) #H2
>H1 in HKL1 H; -H1 #HKL1
>H2 in HKL2; -H2 #HKL2 #H
elim (ltpr_ltpss_sn_conf … HKL1 … HK1) -K1 #K1 #HK1 #HLK1
elim (ltpr_ltpss_sn_conf … HKL2 … HK2) -K2 #K2 #HK2 #HLK2
elim (ltpss_sn_conf … HK1 … HK2) -K #K #HK1 #HK2
lapply (ltpr_fwd_length … HLK1) #H1
lapply (ltpr_fwd_length … HLK2) #H2
/3 width=5/
qed.
