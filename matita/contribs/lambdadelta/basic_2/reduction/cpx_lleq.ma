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

include "basic_2/multiple/lleq_drop.ma".
include "basic_2/reduction/cpx_llpx_sn.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_cpx_trans: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡[h, g] T2 →
                      ∀L1. L1 ≡[T1, 0] L2 → ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L2 #T1 #T2 #H elim H -G -L2 -T1 -T2 /2 width=2 by cpx_st/
[ #I #G #L2 #K2 #V1 #V2 #W2 #i #HLK2 #_ #HVW2 #IHV12 #L1 #H elim (lleq_fwd_lref_dx … H … HLK2) -L2
  [ #H elim (ylt_yle_false … H) //
  | * /3 width=7 by cpx_delta/
  ]
| #a #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #H elim (lleq_inv_bind_O … H) -H
  /3 width=1 by cpx_bind/
| #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #H elim (lleq_inv_flat … H) -H
  /3 width=1 by cpx_flat/
| #G #L2 #V2 #T1 #T #T2 #_ #HT2 #IHT1 #L1 #H elim (lleq_inv_bind_O … H) -H
  /3 width=3 by cpx_zeta/
| #G #L2 #W1 #T1 #T2 #_ #IHT12 #L1 #H elim (lleq_inv_flat … H) -H
  /3 width=1 by cpx_eps/
| #G #L2 #W1 #W2 #T1 #_ #IHW12 #L1 #H elim (lleq_inv_flat … H) -H
  /3 width=1 by cpx_ct/
| #a #G #L1 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L1 #H elim (lleq_inv_flat … H) -H
  #HV1 #H elim (lleq_inv_bind_O … H) -H /3 width=1 by cpx_beta/
| #a #G #L1 #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #L1 #H elim (lleq_inv_flat … H) -H
  #HV1 #H elim (lleq_inv_bind_O … H) -H /3 width=3 by cpx_theta/
]
qed-.

lemma cpx_lleq_conf: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡[h, g] T2 →
                     ∀L1. L2 ≡[T1, 0] L1 → ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2.
/3 width=3 by lleq_cpx_trans, lleq_sym/ qed-.

lemma cpx_lleq_conf_sn: ∀h,g,G. s_r_confluent1 … (cpx h g G) (lleq 0).
/3 width=6 by cpx_llpx_sn_conf, lift_mono, ex2_intro/ qed-.

lemma cpx_lleq_conf_dx: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡[h, g] T2 →
                        ∀L1. L1 ≡[T1, 0] L2 → L1 ≡[T2, 0] L2.
/4 width=6 by cpx_lleq_conf_sn, lleq_sym/ qed-.
