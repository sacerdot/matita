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

include "basic_2/static/lfeq.ma".
include "basic_2/rt_transition/lfpx_fsle.ma".

(* UNCOUNTED CONTEXT-SENSITIVE PARALLEL RT-TRANSITION FOR TERMS *************)

(* Properties with syntactic equivalence for lenvs on referred entries ******)

(* Basic_2A1: was: lleq_cpx_trans *)
lemma lfeq_cpx_trans: ∀h,G. lfeq_transitive (cpx h G).
#h #G #L2 #T1 #T2 #H @(cpx_ind … H) -G -L2 -T1 -T2 /2 width=2 by cpx_ess/
[ #I #G #K2 #V1 #V2 #W2 #_ #IH #HVW2 #L1 #H
  elim (lfeq_inv_zero_pair_dx … H) -H #K1 #HK12 #H destruct
  /3 width=3 by cpx_delta/
| #I2 #G #K2 #T #U #i #_ #IH #HTU #L1 #H
  elim (lfeq_inv_lref_bind_dx … H) -H #I1 #K1 #HK12 #H destruct
  /3 width=3 by cpx_lref/
| #p #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #H
  elim (lfeq_inv_bind … H) -H /3 width=1 by cpx_bind/
| #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #H
  elim (lfeq_inv_flat … H) -H /3 width=1 by cpx_flat/
| #G #L2 #V2 #T1 #T #T2 #_ #HT2 #IH #L1 #H
  elim (lfeq_inv_bind … H) -H /3 width=3 by cpx_zeta/
| #G #L2 #W1 #T1 #T2 #_ #IH #L1 #H
  elim (lfeq_inv_flat … H) -H /3 width=1 by cpx_eps/
| #G #L2 #W1 #W2 #T1 #_ #IH #L1 #H
  elim (lfeq_inv_flat … H) -H /3 width=1 by cpx_ee/
| #p #G #L2 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L1 #H
  elim (lfeq_inv_flat … H) -H #HV1 #H
  elim (lfeq_inv_bind … H) -H /3 width=1 by cpx_beta/
| #p #G #L2 #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV1 #IHW12 #IHT12 #HV2 #L1 #H
  elim (lfeq_inv_flat … H) -H #HV1 #H
  elim (lfeq_inv_bind … H) -H /3 width=3 by cpx_theta/
]
qed-.
(*
(* Basic_2A1: was: cpx_lleq_conf *)
lemma cpx_lfeq_conf: ∀h,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ⬈[h] T2 →
                     ∀L1. L2 ≡[T1] L1 → ⦃G, L1⦄ ⊢ T1 ⬈[h] T2.
/3 width=3 by lfeq_cpx_trans, lfeq_sym/ qed-.
*)
(* Basic_2A1: was: cpx_lleq_conf_sn *)
lemma cpx_lfeq_conf_sn: ∀h,G. s_r_confluent1 … (cpx h G) lfeq.
/2 width=5 by cpx_lfxs_conf/ qed-.
(*
(* Basic_2A1: was: cpx_lleq_conf_dx *)
lemma cpx_lfeq_conf_dx: ∀h,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ⬈[h] T2 →
                        ∀L1. L1 ≡[T1] L2 → L1 ≡[T2] L2.
/4 width=6 by cpx_lfeq_conf_sn, lfeq_sym/ qed-.
*)