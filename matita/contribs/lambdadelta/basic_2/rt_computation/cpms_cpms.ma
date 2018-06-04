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

include "basic_2/rt_computation/cpms_drops.ma".
include "basic_2/rt_computation/cprs.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Main properties **********************************************************)

(* Basic_2A1: uses: lstas_scpds_trans scpds_strap2 *)
theorem cpms_trans (h) (G) (L):
                   ∀n1,T1,T. ⦃G, L⦄ ⊢ T1 ➡*[n1, h] T →
                   ∀n2,T2. ⦃G, L⦄ ⊢ T ➡*[n2, h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[n1+n2, h] T2.
/2 width=3 by ltc_trans/ qed-.

(* Basic_2A1: uses: scpds_cprs_trans *)
theorem cpms_cprs_trans (n) (h) (G) (L):
                        ∀T1,T. ⦃G, L⦄ ⊢ T1 ➡*[n, h] T →
                        ∀T2. ⦃G, L⦄ ⊢ T ➡*[h] T2 → ⦃G, L⦄ ⊢ T1 ➡*[n, h] T2.
#n #h #G #L #T1 #T #HT1 #T2 #HT2 >(plus_n_O … n)
/2 width=3 by cpms_trans/ qed-.

(* Basic_2A1: includes: cprs_bind *)
theorem cpms_bind (n) (h) (G) (L):
                  ∀I,V1,T1,T2. ⦃G, L.ⓑ{I}V1⦄ ⊢ T1 ➡*[n, h] T2 →
                  ∀V2. ⦃G, L⦄ ⊢ V1 ➡*[h] V2 →
                  ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ➡*[n, h] ⓑ{p,I}V2.T2.
#n #h #G #L #I #V1 #T1 #T2 #HT12 #V2 #H @(cprs_ind_dx … H) -V2
[ /2 width=1 by cpms_bind_dx/
| #V #V2 #_ #HV2 #IH #p >(plus_n_O … n) -HT12
  /3 width=3 by cpr_pair_sn, cpms_step_dx/
]
qed.

theorem cpms_appl (n) (h) (G) (L):
                  ∀T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[n, h] T2 →
                  ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h] V2 →
                  ⦃G, L⦄ ⊢ ⓐV1.T1 ➡*[n, h] ⓐV2.T2.
#n #h #G #L #T1 #T2 #HT12 #V1 #V2 #H @(cprs_ind_dx … H) -V2
[ /2 width=1 by cpms_appl_dx/
| #V #V2 #_ #HV2 #IH >(plus_n_O … n) -HT12
  /3 width=3 by cpr_pair_sn, cpms_step_dx/
]
qed.

lemma cpms_inv_plus (h) (G) (L): ∀n1,n2,T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[n1+n2, h] T2 →
                                 ∃∃T. ⦃G, L⦄ ⊢ T1 ➡*[n1, h] T & ⦃G, L⦄ ⊢ T ➡*[n2, h] T2.
#h #G #L #n1 elim n1 -n1 /2 width=3 by ex2_intro/
#n1 #IH #n2 #T1 #T2 <plus_S1 #H
elim (cpms_inv_succ_sn … H) -H #T0 #HT10 #HT02
elim (IH … HT02) -IH -HT02 #T #HT0 #HT2
lapply (cpms_trans … HT10 … HT0) -T0 #HT1
/2 width=3 by ex2_intro/
qed-.

lemma cpms_cast (n) (h) (G) (L):
                ∀T1,T2. ⦃G, L⦄ ⊢ T1 ➡*[n, h] T2 →
                ∀U1,U2. ⦃G, L⦄ ⊢ U1 ➡*[n, h] U2 →
                ⦃G, L⦄ ⊢ ⓝU1.T1 ➡*[n, h] ⓝU2.T2.
#n #h #G #L #T1 #T2 #H @(cpms_ind_sn … H) -T1 -n
[ /3 width=3 by cpms_cast_sn/
| #n1 #n2 #T1 #T #HT1 #_ #IH #U1 #U2 #H
  elim (cpms_inv_plus … H) -H #U #HU1 #HU2
  /3 width=3 by cpms_trans, cpms_cast_sn/
]
qed.

(* Basic_2A1: includes: cprs_beta_rc *)
theorem cpms_beta_rc (n) (h) (G) (L):
                     ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡[h] V2 →
                     ∀W1,T1,T2. ⦃G, L.ⓛW1⦄ ⊢ T1 ➡*[n, h] T2 →
                     ∀W2. ⦃G, L⦄ ⊢ W1 ➡*[h] W2 →
                     ∀p. ⦃G, L⦄ ⊢ ⓐV1.ⓛ{p}W1.T1 ➡*[n, h] ⓓ{p}ⓝW2.V2.T2.
#n #h #G #L #V1 #V2 #HV12 #W1 #T1 #T2 #HT12 #W2 #H @(cprs_ind_dx … H) -W2
[ /2 width=1 by cpms_beta_dx/
| #W #W2 #_ #HW2 #IH #p >(plus_n_O … n) -HT12
  /4 width=3 by cpr_pair_sn, cpms_step_dx/
]
qed.

(* Basic_2A1: includes: cprs_beta *)
theorem cpms_beta (n) (h) (G) (L):
                  ∀W1,T1,T2. ⦃G, L.ⓛW1⦄ ⊢ T1 ➡*[n, h] T2 →
                  ∀W2. ⦃G, L⦄ ⊢ W1 ➡*[h] W2 →
                  ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h] V2 →
                  ∀p. ⦃G, L⦄ ⊢ ⓐV1.ⓛ{p}W1.T1 ➡*[n, h] ⓓ{p}ⓝW2.V2.T2.
#n #h #G #L #W1 #T1 #T2 #HT12 #W2 #HW12 #V1 #V2 #H @(cprs_ind_dx … H) -V2
[ /2 width=1 by cpms_beta_rc/
| #V #V2 #_ #HV2 #IH #p >(plus_n_O … n) -HT12
  /4 width=5 by cpms_step_dx, cpr_pair_sn, cpm_cast/
]
qed.

(* Basic_2A1: includes: cprs_theta_rc *)
theorem cpms_theta_rc (n) (h) (G) (L):
                      ∀V1,V. ⦃G, L⦄ ⊢ V1 ➡[h] V → ∀V2. ⬆*[1] V ≘ V2 →
                      ∀W1,T1,T2. ⦃G, L.ⓓW1⦄ ⊢ T1 ➡*[n, h] T2 →
                      ∀W2. ⦃G, L⦄ ⊢ W1 ➡*[h] W2 →
                      ∀p. ⦃G, L⦄ ⊢ ⓐV1.ⓓ{p}W1.T1 ➡*[n, h] ⓓ{p}W2.ⓐV2.T2.
#n #h #G #L #V1 #V #HV1 #V2 #HV2 #W1 #T1 #T2 #HT12 #W2 #H @(cprs_ind_dx … H) -W2
[ /2 width=3 by cpms_theta_dx/
| #W #W2 #_ #HW2 #IH #p >(plus_n_O … n) -HT12
  /3 width=3 by cpr_pair_sn, cpms_step_dx/
]
qed.

(* Basic_2A1: includes: cprs_theta *)
theorem cpms_theta (n) (h) (G) (L):
                   ∀V,V2. ⬆*[1] V ≘ V2 → ∀W1,W2. ⦃G, L⦄ ⊢ W1 ➡*[h] W2 →
                   ∀T1,T2. ⦃G, L.ⓓW1⦄ ⊢ T1 ➡*[n, h] T2 →
                   ∀V1. ⦃G, L⦄ ⊢ V1 ➡*[h] V → 
                   ∀p. ⦃G, L⦄ ⊢ ⓐV1.ⓓ{p}W1.T1 ➡*[n, h] ⓓ{p}W2.ⓐV2.T2.
#n #h #G #L #V #V2 #HV2 #W1 #W2 #HW12 #T1 #T2 #HT12 #V1 #H @(cprs_ind_sn … H) -V1
[ /2 width=3 by cpms_theta_rc/
| #V1 #V0 #HV10 #_ #IH #p >(plus_O_n … n) -HT12
  /3 width=3 by cpr_pair_sn, cpms_step_sn/
]
qed.
(*
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

(* Advanced inversion lemmas ************************************************)

lemma scpds_inv_abst1: ∀h,o,a,G,L,V1,T1,U2,d. ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 •*➡*[h, o, d] U2 →
                       ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡* V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 •*➡*[h, o, d] T2 &
                                U2 = ⓛ{a}V2.T2.
#h #o #a #G #L #V1 #T1 #U2 #d2 * #X #d1 #Hd21 #Hd1 #H1 #H2
lapply (da_inv_bind … Hd1) -Hd1 #Hd1
elim (lstas_inv_bind1 … H1) -H1 #U #HTU1 #H destruct
elim (cprs_inv_abst1 … H2) -H2 #V2 #T2 #HV12 #HUT2 #H destruct
/3 width=6 by ex4_2_intro, ex3_2_intro/
qed-.

lemma scpds_inv_abbr_abst: ∀h,o,a1,a2,G,L,V1,W2,T1,T2,d. ⦃G, L⦄ ⊢ ⓓ{a1}V1.T1 •*➡*[h, o, d] ⓛ{a2}W2.T2 →
                           ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 •*➡*[h, o, d] T & ⬆[0, 1] ⓛ{a2}W2.T2 ≘ T & a1 = true.
#h #o #a1 #a2 #G #L #V1 #W2 #T1 #T2 #d2 * #X #d1 #Hd21 #Hd1 #H1 #H2
lapply (da_inv_bind … Hd1) -Hd1 #Hd1
elim (lstas_inv_bind1 … H1) -H1 #U1 #HTU1 #H destruct
elim (cprs_inv_abbr1 … H2) -H2 *
[ #V2 #U2 #HV12 #HU12 #H destruct
| /3 width=6 by ex4_2_intro, ex3_intro/
]
qed-.

lemma scpds_inv_lstas_eq: ∀h,o,G,L,T1,T2,d. ⦃G, L⦄ ⊢ T1 •*➡*[h, o, d] T2 →
                          ∀T. ⦃G, L⦄ ⊢ T1 •*[h, d] T → ⦃G, L⦄ ⊢ T ➡* T2.
#h #o #G #L #T1 #T2 #d2 *
#T0 #d1 #_ #_ #HT10 #HT02 #T #HT1
lapply (lstas_mono … HT10 … HT1) #H destruct //
qed-.

(* Main properties **********************************************************)

theorem scpds_conf_eq: ∀h,o,G,L,T0,T1,d. ⦃G, L⦄ ⊢ T0 •*➡*[h, o, d] T1 →
                       ∀T2. ⦃G, L⦄ ⊢ T0 •*➡*[h, o, d] T2 →
                       ∃∃T. ⦃G, L⦄ ⊢ T1 ➡* T & ⦃G, L⦄ ⊢ T2 ➡* T.
#h #o #G #L #T0 #T1 #d0 * #U1 #d1 #_ #_ #H1 #HUT1 #T2 * #U2 #d2 #_ #_ #H2 #HUT2 -d1 -d2
lapply (lstas_mono … H1 … H2) #H destruct -h -d0 /2 width=3 by cprs_conf/
qed-.
*)
