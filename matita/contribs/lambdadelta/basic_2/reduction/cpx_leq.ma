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

include "basic_2/relocation/ldrop_leq.ma".
include "basic_2/relocation/lleq_lleq.ma".
include "basic_2/reduction/cpx.ma".

(* CONTEXT-SENSITIVE EXTENDED PARALLEL REDUCTION FOR TERMS ******************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_cpx_trans_leq: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡[h, g] T2 →
                          ∀L1,d. L1 ⋕[d, T1] L2 → L1 ≃[d, ∞] L2 → ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2.
#h #g #G #L2 #T1 #T2 #H elim H -G -L2 -T1 -T2 /2 width=2 by cpx_sort/
[ #I #G #L2 #K2 #V1 #V2 #W2 #i #HLK2 #_ #HVW2 #IHV12 #L1 #d #H #HL12 elim (lleq_inv_lref_dx … H … HLK2) -H *
  [ #K1 #HLK1 #HV1 #Hdi elim (ldrop_leq_conf_be … HL12 … HLK1) -HL12 /2 width=1 by yle_inj/
    >yminus_Y_inj #J #Y #X #HK12 #H lapply (ldrop_mono … H … HLK2) -L2
    #H destruct /3 width=7 by cpx_delta/
  | #J #K1 #V #HLK1 #_ #HV1 #Hid elim (ldrop_leq_conf_lt … HL12 … HLK1) -HL12 /2 width=1 by ylt_inj/
    #Y #HK12 #H lapply (ldrop_mono … H … HLK2) -L2
    #H destruct /3 width=7 by cpx_delta/
  ]
| #a #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #d #H elim (lleq_inv_bind … H) -H
  /4 width=3 by cpx_bind, leq_succ/
| #I #G #L2 #V1 #V2 #T1 #T2 #_ #_ #IHV12 #IHT12 #L1 #d #H elim (lleq_inv_flat … H) -H
  /3 width=3 by cpx_flat/
| #G #L2 #V2 #T1 #T #T2 #_ #HT2 #IHT1 #L1 #d #H elim (lleq_inv_bind … H) -H
  /4 width=3 by cpx_zeta, leq_succ/
| #G #L2 #W1 #T1 #T2 #_ #IHT12 #L1 #d #H elim (lleq_inv_flat … H) -H
  /3 width=3 by cpx_tau/
| #G #L2 #W1 #W2 #T1 #_ #IHW12 #L1 #d #H elim (lleq_inv_flat … H) -H
  /3 width=3 by cpx_ti/
| #a #G #L1 #V1 #V2 #W1 #W2 #T1 #T2 #_ #_ #_ #IHV12 #IHW12 #IHT12 #L1 #d #H elim (lleq_inv_flat … H) -H
  #HV1 #H elim (lleq_inv_bind … H) -H /4 width=3 by cpx_beta, leq_succ/
| #a #G #L1 #V1 #V #V2 #W1 #W2 #T1 #T2 #_ #HV2 #_ #_ #IHV1 #IHW12 #IHT12 #L1 #d #H elim (lleq_inv_flat … H) -H
  #HV1 #H elim (lleq_inv_bind … H) -H /4 width=3 by cpx_theta, leq_succ/
]
qed-.

(* Note: this can be proved directly *)
lemma lleq_cpx_trans: ∀h,g,G,L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡[h, g] T2 →
                      ∀L1. L1 ⋕[0, T1] L2 → ⦃G, L1⦄ ⊢ T1 ➡[h, g] T2.
/4 width=6 by lleq_cpx_trans_leq, lleq_fwd_length, leq_O_Y/ qed-. 