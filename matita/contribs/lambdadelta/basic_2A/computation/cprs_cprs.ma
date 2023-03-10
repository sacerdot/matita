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

include "ground/xoa/ex_4_5.ma".
include "basic_2A/reduction/lpr_lpr.ma".
include "basic_2A/computation/cprs_lift.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION ON TERMS **************************)

(* Main properties **********************************************************)

(* Basic_1: was: pr3_t *)
(* Basic_1: includes: pr1_t *)
theorem cprs_trans: ∀G,L. Transitive … (cprs G L).
normalize /2 width=3 by trans_TC/ qed-.

(* Basic_1: was: pr3_confluence *)
(* Basic_1: includes: pr1_confluence *)
theorem cprs_conf: ∀G,L. confluent2 … (cprs G L) (cprs G L).
normalize /3 width=3 by cpr_conf, TC_confluent2/ qed-.

theorem cprs_bind: ∀a,I,G,L,V1,V2,T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡* T2 → ⦃G, L⦄ ⊢ V1 ➡* V2 →
                   ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡* ⓑ{a,I}V2.T2.
#a #I #G #L #V1 #V2 #T1 #T2 #HT12 #H @(cprs_ind … H) -V2
/3 width=5 by cprs_trans, cprs_bind_dx/
qed.

(* Basic_1: was: pr3_flat *)
theorem cprs_flat: ∀I,G,L,V1,V2,T1,T2. ⦃G, L⦄ ⊢ T1 ➡* T2 → ⦃G, L⦄ ⊢ V1 ➡* V2 →
                   ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ➡* ⓕ{I}V2.T2.
#I #G #L #V1 #V2 #T1 #T2 #HT12 #H @(cprs_ind … H) -V2
/3 width=3 by cprs_flat_dx, cprs_strap1, cpr_pair_sn/
qed.

theorem cprs_beta_rc: ∀a,G,L,V1,V2,W1,W2,T1,T2.
                      ⦃G, L⦄ ⊢ V1 ➡ V2 → ⦃G, L.ⓛW1⦄ ⊢ T1 ➡* T2 → ⦃G, L⦄ ⊢ W1 ➡* W2 →
                      ⦃G, L⦄ ⊢ ⓐV1.ⓛ{a}W1.T1 ➡* ⓓ{a}ⓝW2.V2.T2.
#a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HV12 #HT12 #H @(cprs_ind … H) -W2 /2 width=1 by cprs_beta_dx/
#W #W2 #_ #HW2 #IHW1 (**) (* fulla uto too slow 14s *)
@(cprs_trans … IHW1) -IHW1 /3 width=1 by cprs_flat_dx, cprs_bind/
qed.

theorem cprs_beta: ∀a,G,L,V1,V2,W1,W2,T1,T2.
                   ⦃G, L.ⓛW1⦄ ⊢ T1 ➡* T2 → ⦃G, L⦄ ⊢ W1 ➡* W2 → ⦃G, L⦄ ⊢ V1 ➡* V2 →
                   ⦃G, L⦄ ⊢ ⓐV1.ⓛ{a}W1.T1 ➡* ⓓ{a}ⓝW2.V2.T2.
#a #G #L #V1 #V2 #W1 #W2 #T1 #T2 #HT12 #HW12 #H @(cprs_ind … H) -V2 /2 width=1 by cprs_beta_rc/
#V #V2 #_ #HV2 #IHV1
@(cprs_trans … IHV1) -IHV1 /3 width=1 by cprs_flat_sn, cprs_bind/
qed.

theorem cprs_theta_rc: ∀a,G,L,V1,V,V2,W1,W2,T1,T2.
                       ⦃G, L⦄ ⊢ V1 ➡ V → ⬆[0, 1] V ≡ V2 → ⦃G, L.ⓓW1⦄ ⊢ T1 ➡* T2 →
                       ⦃G, L⦄ ⊢ W1 ➡* W2 → ⦃G, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡* ⓓ{a}W2.ⓐV2.T2.
#a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV1 #HV2 #HT12 #H @(cprs_ind … H) -W2
/3 width=5 by cprs_trans, cprs_theta_dx, cprs_bind_dx/
qed.

theorem cprs_theta: ∀a,G,L,V1,V,V2,W1,W2,T1,T2.
                    ⬆[0, 1] V ≡ V2 → ⦃G, L⦄ ⊢ W1 ➡* W2 → ⦃G, L.ⓓW1⦄ ⊢ T1 ➡* T2 →
                    ⦃G, L⦄ ⊢ V1 ➡* V → ⦃G, L⦄ ⊢ ⓐV1.ⓓ{a}W1.T1 ➡* ⓓ{a}W2.ⓐV2.T2.
#a #G #L #V1 #V #V2 #W1 #W2 #T1 #T2 #HV2 #HW12 #HT12 #H @(cprs_ind_dx … H) -V1
/3 width=3 by cprs_trans, cprs_theta_rc, cprs_flat_dx/
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was pr3_gen_appl *)
lemma cprs_inv_appl1: ∀G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓐV1.T1 ➡* U2 →
                      ∨∨ ∃∃V2,T2.       ⦃G, L⦄ ⊢ V1 ➡* V2 & ⦃G, L⦄ ⊢ T1 ➡* T2 &
                                        U2 = ⓐV2. T2
                       | ∃∃a,W,T.       ⦃G, L⦄ ⊢ T1 ➡* ⓛ{a}W.T &
                                        ⦃G, L⦄ ⊢ ⓓ{a}ⓝW.V1.T ➡* U2
                       | ∃∃a,V0,V2,V,T. ⦃G, L⦄ ⊢ V1 ➡* V0 & ⬆[0,1] V0 ≡ V2 &
                                        ⦃G, L⦄ ⊢ T1 ➡* ⓓ{a}V.T &
                                        ⦃G, L⦄ ⊢ ⓓ{a}V.ⓐV2.T ➡* U2.
#G #L #V1 #T1 #U2 #H @(cprs_ind … H) -U2 /3 width=5 by or3_intro0, ex3_2_intro/
#U #U2 #_ #HU2 * *
[ #V0 #T0 #HV10 #HT10 #H destruct
  elim (cpr_inv_appl1 … HU2) -HU2 *
  [ #V2 #T2 #HV02 #HT02 #H destruct /4 width=5 by cprs_strap1, or3_intro0, ex3_2_intro/
  | #a #V2 #W #W2 #T #T2 #HV02 #HW2 #HT2 #H1 #H2 destruct
    lapply (cprs_strap1 … HV10 … HV02) -V0 #HV12
    lapply (lsubr_cpr_trans … HT2 (L.ⓓⓝW.V1) ?) -HT2
    /5 width=5 by cprs_bind, cprs_flat_dx, cpr_cprs, lsubr_beta, ex2_3_intro, or3_intro1/
  | #a #V #V2 #W0 #W2 #T #T2 #HV0 #HV2 #HW02 #HT2 #H1 #H2 destruct
    /5 width=10 by cprs_flat_sn, cprs_bind_dx, cprs_strap1, ex4_5_intro, or3_intro2/
  ]
| /4 width=9 by cprs_strap1, or3_intro1, ex2_3_intro/
| /4 width=11 by cprs_strap1, or3_intro2, ex4_5_intro/
]
qed-.

(* Properties concerning sn parallel reduction on local environments ********)

(* Basic_1: was just: pr3_pr2_pr2_t *)
(* Basic_1: includes: pr3_pr0_pr2_t *)
lemma lpr_cpr_trans: ∀G. s_r_transitive … (cpr G) (λ_. lpr G).
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
lemma lpr_cprs_trans: ∀G. s_rs_transitive … (cpr G) (λ_. lpr G).
#G @s_r_trans_CTC1 /2 width=3 by lpr_cpr_trans/ (**) (* full auto fails *)
qed-.

(* Basic_1: was: pr3_strip *)
(* Basic_1: includes: pr1_strip *)
lemma cprs_strip: ∀G,L. confluent2 … (cprs G L) (cpr G L).
normalize /4 width=3 by cpr_conf, TC_strip1/ qed-.

lemma cprs_lpr_conf_dx: ∀G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡* T1 → ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 →
                        ∃∃T. ⦃G, L1⦄ ⊢ T1 ➡* T & ⦃G, L1⦄ ⊢ T0 ➡* T.
#G #L0 #T0 #T1 #H @(cprs_ind … H) -T1 /2 width=3 by ex2_intro/
#T #T1 #_ #HT1 #IHT0 #L1 #HL01 elim (IHT0 … HL01)
#T2 #HT2 #HT02 elim (lpr_cpr_conf_dx … HT1 … HL01) -L0
#T3 #HT3 #HT13 elim (cprs_strip … HT2 … HT3) -T
/4 width=5 by cprs_strap2, cprs_strap1, ex2_intro/
qed-.

lemma cprs_lpr_conf_sn: ∀G,L0,T0,T1. ⦃G, L0⦄ ⊢ T0 ➡* T1 →
                        ∀L1. ⦃G, L0⦄ ⊢ ➡ L1 →
                        ∃∃T. ⦃G, L0⦄ ⊢ T1 ➡* T & ⦃G, L1⦄ ⊢ T0 ➡* T.
#G #L0 #T0 #T1 #HT01 #L1 #HL01 elim (cprs_lpr_conf_dx … HT01 … HL01) -HT01
/3 width=3 by lpr_cprs_trans, ex2_intro/
qed-.

lemma cprs_bind2_dx: ∀G,L,V1,V2. ⦃G, L⦄ ⊢ V1 ➡ V2 →
                     ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡* T2 →
                     ∀a. ⦃G, L⦄ ⊢ ⓑ{a,I}V1.T1 ➡* ⓑ{a,I}V2.T2.
/4 width=5 by lpr_cprs_trans, cprs_bind_dx, lpr_pair/ qed.
