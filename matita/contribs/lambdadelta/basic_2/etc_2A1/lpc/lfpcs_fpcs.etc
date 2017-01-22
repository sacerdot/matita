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

include "basic_2/computation/fprs_cprs.ma".
include "basic_2/computation/lfprs_fprs.ma".
include "basic_2/equivalence/fpcs_fpcs.ma".
include "basic_2/equivalence/lfpcs_lfpcs.ma".

(* FOCALIZED PARALLEL EQUIVALENCE ON LOCAL ENVIRONMENTS *********************)

(* Inversion lemmas on context-free parallel equivalence for closures *******)

lemma lfpcs_inv_fpcs: ∀L1,L2. ⦃L1⦄ ⬌* ⦃L2⦄ → ∀T. ⦃L1, T⦄ ⬌* ⦃L2, T⦄.
#L1 #L2 #HL12 #T
elim (lfpcs_inv_lfprs … HL12) -HL12 #L #HL1 #HL2
lapply (lfprs_inv_fprs … HL1 T) -HL1
lapply (lfprs_inv_fprs … HL2 T) -HL2 /2 width=4/
qed-.

(* Properties on context-free parallel equivalence for closures *************)

lemma fpcs_lfpcs: ∀L1,L2,T1,T2. ⦃L1, T1⦄ ⬌* ⦃L2, T2⦄ → ⦃L1⦄ ⬌* ⦃L2⦄.
#L1 #L2 #T1 #T2 #HT12
elim (fpcs_inv_fprs … HT12) -HT12 /3 width=5 by fprs_lfprs, lfprs_div/ (**) (* auto too slow without trace *)
qed.

lemma fpcs_lift: ∀K1,K2,T1,T2. ⦃K1, T1⦄ ⬌* ⦃K2, T2⦄ →
                 ∀L1,L2. ⦃L1⦄ ⬌* ⦃L2⦄ →
                 ∀d,e. ⇩[d, e] L1 ≡ K1 → ⇩[d, e] L2 ≡ K2 →
                 ∀U1,U2. ⇧[d, e] T1 ≡ U1 → ⇧[d, e] T2 ≡ U2 →
                 ⦃L1, U1⦄ ⬌* ⦃L2, U2⦄.
#K1 #K2 #T1 #T2 #HT12 #L1 #L2 #HL12 #d #e #HLK1 #HLK2 #U1 #U2 #HTU1 #HTU2
elim (fpcs_inv_fprs … HT12) -HT12 #K #T #HT1 #HT2
elim (lift_total T d e) #U #HTU
elim (fprs_lift … HT1 … HLK1 … HTU1 HTU) -K1 -T1 #K1 #HU1 #_
elim (fprs_lift … HT2 … HLK2 … HTU2 HTU) -K2 -T2 -T #K2 #HU2 #_ -K -d -e
lapply (lfpcs_lfprs_conf K1 … HL12) -HL12 /2 width=3/ #H
lapply (lfpcs_lfprs_strap1 … H K2 ?) -H /2 width=3/ #HK12
lapply (lfpcs_inv_fpcs … HK12 U) -HK12 #HU
/3 width=4 by fpcs_fprs_strap2, fpcs_fprs_div/
qed.
