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

include "basic_2/rt_computation/cprs_cprs.ma".
include "basic_2/rt_computation/lprs_cpms.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Advanced properties ******************************************************)

(* Basic_2A1: was: lprs_pair2 *)
lemma lprs_pair_dx (h) (G): ∀L1,L2. ❪G,L1❫ ⊢ ➡*[h,0] L2 →
                            ∀V1,V2. ❪G,L2❫ ⊢ V1 ➡*[h,0] V2 →
                            ∀I. ❪G,L1.ⓑ[I]V1❫ ⊢ ➡*[h,0] L2.ⓑ[I]V2.
/3 width=3 by lprs_pair, lprs_cpms_trans/ qed.

(* Properties on context-sensitive parallel r-computation for terms *********)

lemma lprs_cprs_conf_dx (h) (G): ∀L0.∀T0,T1:term. ❪G,L0❫ ⊢ T0 ➡*[h,0] T1 →
                                 ∀L1. ❪G,L0❫ ⊢ ➡*[h,0] L1 →
                                 ∃∃T. ❪G,L1❫ ⊢ T1 ➡*[h,0] T & ❪G,L1❫ ⊢ T0 ➡*[h,0] T.
#h #G #L0 #T0 #T1 #HT01 #L1 #H
@(lprs_ind_dx … H) -L1 /2 width=3 by ex2_intro/
#L #L1 #_ #HL1 * #T #HT1 #HT0 -L0
elim (cprs_lpr_conf_dx … HT1 … HL1) -HT1 #T2 #HT2
elim (cprs_lpr_conf_dx … HT0 … HL1) -L #T3 #HT3
elim (cprs_conf … HT2 … HT3) -T
/3 width=5 by cprs_trans, ex2_intro/
qed-.

lemma lprs_cpr_conf_dx (h) (G): ∀L0. ∀T0,T1:term. ❪G,L0❫ ⊢ T0 ➡[h,0] T1 →
                                ∀L1. ❪G,L0❫ ⊢ ➡*[h,0] L1 →
                                ∃∃T. ❪G,L1❫ ⊢ T1 ➡*[h,0] T & ❪G,L1❫ ⊢ T0 ➡*[h,0] T.
/3 width=3 by lprs_cprs_conf_dx, cpm_cpms/ qed-.

(* Note: this can be proved on its own using lprs_ind_sn *)
lemma lprs_cprs_conf_sn (h) (G): ∀L0. ∀T0,T1:term. ❪G,L0❫ ⊢ T0 ➡*[h,0] T1 →
                                 ∀L1. ❪G,L0❫ ⊢ ➡*[h,0] L1 →
                                 ∃∃T. ❪G,L0❫ ⊢ T1 ➡*[h,0] T & ❪G,L1❫ ⊢ T0 ➡*[h,0] T.
#h #G #L0 #T0 #T1 #HT01 #L1 #HL01
elim (lprs_cprs_conf_dx … HT01 … HL01) -HT01
/3 width=3 by lprs_cpms_trans, ex2_intro/
qed-.

lemma lprs_cpr_conf_sn (h) (G): ∀L0. ∀T0,T1:term. ❪G,L0❫ ⊢ T0 ➡[h,0] T1 →
                                ∀L1. ❪G,L0❫ ⊢ ➡*[h,0] L1 →
                                ∃∃T. ❪G,L0❫ ⊢ T1 ➡*[h,0] T & ❪G,L1❫ ⊢ T0 ➡*[h,0] T.
/3 width=3 by lprs_cprs_conf_sn, cpm_cpms/ qed-.
