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

include "basic_2/rt_transition/lpr.ma".
include "basic_2/rt_computation/cpms_cpms.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties with parallel rt-transition for full local environments *******)

lemma lpr_cpm_trans (h) (n) (G):
                    ∀L2,T1,T2. ❪G,L2❫ ⊢ T1 ➡[h,n] T2 →
                    ∀L1. ❪G,L1❫ ⊢ ➡[h,0] L2 → ❪G,L1❫ ⊢ T1 ➡*[h,n] T2.
#h #n #G #L2 #T1 #T2 #H @(cpm_ind … H) -n -G -L2 -T1 -T2
[ /2 width=3 by/
| /3 width=2 by cpm_cpms/
| #n #G #K2 #V2 #V4 #W4 #_ #IH #HVW4 #L1 #H
  elim (lpr_inv_pair_dx … H) -H #K1 #V1 #HK12 #HV12 #H destruct
  /4 width=3 by cpms_delta, cpms_step_sn/
| #n #G #K2 #V2 #V4 #W4 #_ #IH #HVW4 #L1 #H
  elim (lpr_inv_pair_dx … H) -H #K1 #V1 #HK12 #HV12 #H destruct
  /4 width=3 by cpms_ell, cpms_step_sn/
| #n #I2 #G #K2 #T #U #i #_ #IH #HTU #L1 #H
  elim (lpr_inv_bind_dx … H) -H #I1 #K1 #HK12 #HI12 #H destruct
  /4 width=3 by cpms_lref, cpms_step_sn/
| /4 width=1 by cpms_bind, lpr_bind_refl_dx/
| /3 width=1 by cpms_appl/
| /3 width=1 by cpms_cast/
| /4 width=3 by cpms_zeta, lpr_bind_refl_dx/
| /3 width=1 by cpms_eps/
| /3 width=1 by cpms_ee/
| /4 width=1 by lpr_bind_refl_dx, cpms_beta/
| /4 width=3 by lpr_bind_refl_dx, cpms_theta/
]
qed-.

lemma lpr_cpms_trans (h) (n) (G):
                     ∀L1,L2. ❪G,L1❫ ⊢ ➡[h,0] L2 →
                     ∀T1,T2. ❪G,L2❫ ⊢ T1 ➡*[h,n] T2 → ❪G,L1❫ ⊢ T1 ➡*[h,n] T2.
#h #n #G #L1 #L2 #HL12 #T1 #T2 #H @(cpms_ind_sn … H) -n -T1
/3 width=3 by lpr_cpm_trans, cpms_trans/
qed-.

(* Advanced properties ******************************************************)

(* Basic_2A1: includes cpr_bind2 *)
lemma cpm_bind2 (h) (n) (G) (L):
                ∀V1,V2. ❪G,L❫ ⊢ V1 ➡[h,0] V2 →
                ∀I,T1,T2. ❪G,L.ⓑ[I]V2❫ ⊢ T1 ➡[h,n] T2 →
                ∀p. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ➡*[h,n] ⓑ[p,I]V2.T2.
/4 width=5 by lpr_cpm_trans, cpms_bind_dx, lpr_pair/ qed.

(* Basic_2A1: includes cprs_bind2_dx *)
lemma cpms_bind2_dx (h) (n) (G) (L):
                    ∀V1,V2. ❪G,L❫ ⊢ V1 ➡[h,0] V2 →
                    ∀I,T1,T2. ❪G,L.ⓑ[I]V2❫ ⊢ T1 ➡*[h,n] T2 →
                    ∀p. ❪G,L❫ ⊢ ⓑ[p,I]V1.T1 ➡*[h,n] ⓑ[p,I]V2.T2.
/4 width=5 by lpr_cpms_trans, cpms_bind_dx, lpr_pair/ qed.
