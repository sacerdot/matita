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

include "basic_2/rt_transition/lpx.ma".
include "basic_2/rt_computation/cpxs_drops.ma".
include "basic_2/rt_computation/cpxs_cpxs.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS ************)

(* Properties with uncounted parallel rt-transition for local environments **)

lemma lpx_cpx_trans: ∀h,G. s_r_transitive … (cpx h G) (λ_.lpx h G).
#h #G #L2 #T1 #T2 #H @(cpx_ind … H) -G -L2 -T1 -T2
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

lemma lpx_cpxs_trans: ∀h,G. s_rs_transitive … (cpx h G) (λ_.lpx h G).
#h #G @s_r_trans_CTC1 /2 width=3 by lpx_cpx_trans/ (**) (* full auto fails *)
qed-.
