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

include "static_2/static/req_length.ma".
include "static_2/static/req_drops.ma".
include "basic_2/rt_transition/rpx_fsle.ma".

(* EXTENDED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS **************)

(* Properties with syntactic equivalence for lenvs on referred entries ******)

(* Basic_2A1: was: lleq_cpx_trans *)
lemma req_cpx_trans (G): R_transitive_req (cpx G).
#G #L2 #T1 #T2 #H @(cpx_ind … H) -G -L2 -T1 -T2 /2 width=2 by cpx_qu/
[ #I #G #K2 #V1 #V2 #W2 #_ #IH #HVW2 #L1 #H
  elim (req_inv_zero_pair_dx … H) -H #K1 #HK12 #H destruct
  /3 width=3 by cpx_delta/
| #I2 #G #K2 #T #U #i #_ #IH #HTU #L1 #H
  elim (req_inv_lref_bind_dx … H) -H #I1 #K1 #HK12 #H destruct
  /3 width=3 by cpx_lref/
| #p #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #H
  elim (req_inv_bind … H) -H /3 width=1 by cpx_bind/
| #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #H
  elim (req_inv_flat … H) -H /3 width=1 by cpx_flat/
| #G #L2 #V2 #T1 #T #T2 #HT1 #_ #IH #L1 #H
  elim (req_inv_bind … H) -H #HV2 #H
  lapply (req_inv_lifts_bi … H (Ⓣ) … HT1) -H [6:|*: /3 width=2 by drops_refl, drops_drop/ ] #HT
  /3 width=3 by cpx_zeta/
| #G #L2 #W1 #T1 #T2 #_ #IH #L1 #H
  elim (req_inv_flat … H) -H /3 width=1 by cpx_eps/
| #G #L2 #W1 #W2 #T1 #_ #IH #L1 #H
  elim (req_inv_flat … H) -H /3 width=1 by cpx_ee/
| #p #G #L2 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L1 #H
  elim (req_inv_flat … H) -H #HV1 #H
  elim (req_inv_bind … H) -H /3 width=1 by cpx_beta/
| #p #G #L2 #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV1 #IHW12 #IHT12 #HV2 #L1 #H
  elim (req_inv_flat … H) -H #HV1 #H
  elim (req_inv_bind … H) -H /3 width=3 by cpx_theta/
]
qed-.

lemma cpx_req_conf (G): R_confluent1_rex (cpx G) ceq.
/3 width=3 by req_cpx_trans, req_sym/ qed-.

(* Basic_2A1: was: cpx_lleq_conf_sn *)
lemma cpx_req_conf_sn (G): s_r_confluent1 … (cpx G) req.
/2 width=5 by cpx_rex_conf_sn/ qed-.
