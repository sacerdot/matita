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

include "ground_2/lib/star.ma".
include "basic_2/rt_transition/lpr.ma".
include "basic_2/rt_computation/cpms.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Properties concerning sn parallel reduction on local environments ********)

(* Basic_1: uses: pr3_pr2_pr2_t *)
(* Basic_1: includes: pr3_pr0_pr2_t *)
(* Basic_2A1: uses: lpr_cpr_trans *) 
lemma lpr_cpm_trans (n) (h) (G): s_r_transitive … (λL. cpm h G L n) (λ_. lpr h G).
#n #h #G #L2 #T1 #T2 #H @(cpm_ind … H) -G -L2 -T1 -T2
[ /2 width=3 by/
| /3 width=2 by cpx_cpxs, cpx_ess/
| #I #G #K2 #V2 #V4 #W4 #_ #IH #HVW4 #L1 #H
  elim (lpx_inv_pair_dx … H) -H #K1 #V1 #HK12 #HV12 #H destruct
  /4 width=3 by cpxs_delta, cpxs_strap2/
| #I2 #G #K2 #T #U #i #_ #IH #HTU #L1 #H
  elim (lpx_inv_bind_dx … H) -H #I1 #K1 #HK12 #HI12 #H destruct
  /4 width=3 by cpxs_lref, cpxs_strap2/
|5,10: /4 width=1 by cpxs_beta, cpxs_bind, lpx_bind_refl_dx/
|6,8,9: /3 width=1 by cpxs_flat, cpxs_ee, cpxs_eps/
| /4 width=3 by cpxs_zeta, lpx_bind_refl_dx/
| /4 width=3 by cpxs_theta, cpxs_strap1, lpx_bind_refl_dx/
]
qed-.







#G #L2 #T1 #T2 #HT12 elim HT12 -G -L2 -T1 -T2
[ /2 width=3 by/
| #G #L2 #K2 #V0 #V2 #W2 #i #HLK2 #_ #HVW2 #IHV02 #L1 #HL12
  elim (lpr_drop_trans_O1 … HL12 … HLK2) -L2 #X #HLK1 #H
  elim (lpr_inv_pair2 … H) -H #K1 #V1 #HK12 #HV10 #H destruct
  /4 width=6 by cprs_strap2, cprs_delta/
|3,7: /4 width=1 by lpr_pair, cprs_bind, cprs_beta/
|4,6: /3 width=1 by cprs_flat, cprs_eps/
|5,8: /4 width=3 by lpr_pair, cprs_zeta, cprs_theta, cprs_strap1/
]
qed-.

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
