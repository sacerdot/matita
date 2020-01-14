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

include "basic_2/dynamic/nta_cpcs.ma".
include "basic_2/dynamic/nta_preserve.ma".

(* NATIVE TYPE ASSIGNMENT FOR TERMS ****************************************)

(* Properties based on type equivalence and preservation *******************)

(* Basic_1: uses: ty3_tred *)
lemma nta_cprs_trans (h) (a) (G) (L):
      ∀T,U1. ❪G,L❫ ⊢ T :[h,a] U1 → ∀U2. ❪G,L❫ ⊢ U1 ➡*[h,0] U2 → ❪G,L❫ ⊢ T :[h,a] U2.
#h #a #G #L #T #U1 #H #U2 #HU12
/4 width=4 by nta_conv_cnv, nta_fwd_cnv_dx, cnv_cpms_trans, cpcs_cprs_dx/
qed-.

(* Basic_1: uses: ty3_sred_back *)
lemma cprs_nta_trans (h) (a) (G) (L):
      ∀T1,U0. ❪G,L❫ ⊢ T1 :[h,a] U0 → ∀T2. ❪G,L❫ ⊢ T1 ➡*[h,0] T2 →
      ∀U. ❪G,L❫ ⊢ T2 :[h,a] U →  ❪G,L❫ ⊢ T1 :[h,a] U.
#h #a #G #L #T1 #U0 #HT1 #T2 #HT12 #U #H
lapply (nta_cprs_conf … HT1 … HT12) -HT12 #HT2
/4 width=6 by nta_mono, nta_conv_cnv, nta_fwd_cnv_dx/
qed-.

lemma cprs_nta_trans_cnv (h) (a) (G) (L):
      ∀T1. ❪G,L❫ ⊢ T1 ![h,a] → ∀T2. ❪G,L❫ ⊢ T1 ➡*[h,0] T2 →
      ∀U. ❪G,L❫ ⊢ T2 :[h,a] U → ❪G,L❫ ⊢ T1 :[h,a] U.
#h #a #G #L #T1 #HT1 #T2 #HT12 #U #H
elim (cnv_nta_sn … HT1) -HT1 #U0 #HT1
/2 width=3 by cprs_nta_trans/
qed-.

(* Basic_1: uses: ty3_sconv *)
lemma nta_cpcs_conf (h) (a) (G) (L):
      ∀T1,U. ❪G,L❫ ⊢ T1 :[h,a] U → ∀T2. ❪G,L❫ ⊢ T1 ⬌*[h] T2 →
      ∀U0. ❪G,L❫ ⊢ T2 :[h,a] U0 → ❪G,L❫ ⊢ T2 :[h,a] U.
#h #a #G #L #T1 #U #HT1 #T2 #HT12 #U0 #HT2
elim (cpcs_inv_cprs … HT12) -HT12 #T0 #HT10 #HT02
/3 width=5 by  cprs_nta_trans, nta_cprs_conf/
qed-.

(* Note: type preservation by valid r-equivalence *)
lemma nta_cpcs_conf_cnv (h) (a) (G) (L):
      ∀T1,U. ❪G,L❫ ⊢ T1 :[h,a] U →
      ∀T2. ❪G,L❫ ⊢ T1 ⬌*[h] T2 → ❪G,L❫ ⊢ T2 ![h,a] → ❪G,L❫ ⊢ T2 :[h,a] U.
#h #a #G #L #T1 #U #HT1 #T2 #HT12 #HT2
elim (cnv_nta_sn … HT2) -HT2 #U0 #HT2
/2 width=3 by nta_cpcs_conf/
qed-.
