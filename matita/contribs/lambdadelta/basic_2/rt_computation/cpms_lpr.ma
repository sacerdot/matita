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

(* Properties concerning sn parallel reduction on local environments ********)

lemma lpr_cpm_trans (n) (h) (G):
                    ∀L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡[n, h] T2 →
                    ∀L1. ⦃G, L1⦄ ⊢ ➡[h] L2 → ⦃G, L1⦄ ⊢ T1 ➡*[n, h] T2.
#n #h #G #L2 #T1 #T2 #H @(cpm_ind … H) -n -G -L2 -T1 -T2
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

(*

(* Basic_1: uses: pr3_pr2_pr2_t *)
(* Basic_1: includes: pr3_pr0_pr2_t *)
(* Basic_2A1: includes: lpr_cpr_trans *)
lemma lpr_cpm_trans (n) (h) (G): s_r_transitive … (λL. cpm h G L n) (λ_. lpr h G).

lemma cpr_bind2: ∀G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡ V2 → ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡ T2 →
                 ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡* ⓑ{a,I}V2.T2.
/4 width=5 by lpr_cpr_trans, cprs_bind_dx, lpr_pair/ qed.

(* Advanced properties ******************************************************)

(* Basic_1: was only: pr3_pr2_pr3_t pr3_wcpr0_t *)
lemma lpr_cprs_trans: ∀G. b_rs_transitive … (cpr G) (λ_. lpr G).
#G @b_c_trans_CTC1 /2 width=3 by lpr_cpr_trans/ (**) (* full auto fails *)
qed-.

lemma cprs_bind2_dx: ∀G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡ V2 →
                     ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡* T2 →
                     ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡* ⓑ{a,I}V2.T2.
/4 width=5 by lpr_cprs_trans, cprs_bind_dx, lpr_pair/ qed.
*)