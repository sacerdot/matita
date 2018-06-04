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

include "basic_2/rt_transition/lpr_lpr.ma".
include "basic_2/rt_computation/cpms_cpms.ma".

(* CONTEXT-SENSITIVE PARALLEL COMPUTATION FOR TERMS *************************)

(* Main properties **********************************************************)

(* Basic_1: was: pr3_t *)
(* Basic_1: includes: pr1_t *)
theorem cprs_trans: ∀G,L. Transitive … (cprs G L).
normalize /2 width=3 by trans_TC/ qed-.

(* Basic_1: was: pr3_confluence *)
(* Basic_1: includes: pr1_confluence *)
theorem cprs_conf: ∀G,L. confluent2 … (cprs G L) (cprs G L).
normalize /3 width=3 by cpr_conf, TC_confluent2/ qed-.

(* Basic_1: was: pr3_flat *)
theorem cprs_flat (h) (G) (L):
                  ∀T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[h] T2 →
                  ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h] V2 →
                  ∀I. ⦃G, L⦄ ⊢ ⓕ{I}V1.T1 ➡*[h] ⓕ{I}V2.T2.
#h #G #L #T1 #T2 #HT12 #V1 #V2 #H @(cprs_ind_dx … H) -V2
[ /2 width=3 by cprs_flat_dx/
| /3 width=3 by cpr_pair_sn, cprs_step_dx/
]
qed.

(* Advanced inversion lemmas ************************************************)

(* Basic_1: was pr3_gen_appl *)
lemma cprs_inv_appl1: ∀G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓐV1.T1 ➡* U2 →
                      ∨∨ ∃∃V2,T2.       ⦃G, L⦄ ⊢ V1 ➡* V2 & ⦃G, L⦄ ⊢ T1 ➡* T2 &
                                        U2 = ⓐV2. T2
                       | ∃∃a,W,T.       ⦃G, L⦄ ⊢ T1 ➡* ⓛ{a}W.T &
                                        ⦃G, L⦄ ⊢ ⓓ{a}ⓝW.V1.T ➡* U2
                       | ∃∃a,V0,V2,V,T. ⦃G, L⦄ ⊢ V1 ➡* V0 & ⬆[0,1] V0 ≘ V2 &
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
