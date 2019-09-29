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

include "ground_2/lib/ltc.ma".
include "basic_2/notation/relations/predstar_6.ma".
include "basic_2/notation/relations/predstar_5.ma".
include "basic_2/rt_transition/cpm.ma".

(* T-BOUND CONTEXT-SENSITIVE PARALLEL RT-COMPUTATION FOR TERMS **************)

(* Basic_2A1: uses: scpds *)
definition cpms (h) (G) (L): relation3 nat term term ≝
                             ltc … plus … (cpm h G L).

interpretation
   "t-bound context-sensitive parallel rt-computarion (term)"
   'PRedStar n h G L T1 T2 = (cpms h G L n T1 T2).

interpretation
   "context-sensitive parallel r-computation (term)"
   'PRedStar h G L T1 T2 = (cpms h G L O T1 T2).

(* Basic eliminators ********************************************************)

lemma cpms_ind_sn (h) (G) (L) (T2) (Q:relation2 …):
                  Q 0 T2 →
                  (∀n1,n2,T1,T. ⦃G,L⦄ ⊢ T1 ➡[n1,h] T → ⦃G,L⦄ ⊢ T ➡*[n2,h] T2 → Q n2 T → Q (n1+n2) T1) →
                  ∀n,T1. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 → Q n T1.
#h #G #L #T2 #Q @ltc_ind_sn_refl //
qed-.

lemma cpms_ind_dx (h) (G) (L) (T1) (Q:relation2 …):
                  Q 0 T1 →
                  (∀n1,n2,T,T2. ⦃G,L⦄ ⊢ T1 ➡*[n1,h] T → Q n1 T → ⦃G,L⦄ ⊢ T ➡[n2,h] T2 → Q (n1+n2) T2) →
                  ∀n,T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 → Q n T2.
#h #G #L #T1 #Q @ltc_ind_dx_refl //
qed-.

(* Basic properties *********************************************************)

(* Basic_1: includes: pr1_pr0 *)
(* Basic_1: uses: pr3_pr2 *)
(* Basic_2A1: includes: cpr_cprs *)
lemma cpm_cpms (h) (G) (L): ∀n,T1,T2. ⦃G,L⦄ ⊢ T1 ➡[n,h] T2 → ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2.
/2 width=1 by ltc_rc/ qed.

lemma cpms_step_sn (h) (G) (L): ∀n1,T1,T. ⦃G,L⦄ ⊢ T1 ➡[n1,h] T →
                                ∀n2,T2. ⦃G,L⦄ ⊢ T ➡*[n2,h] T2 → ⦃G,L⦄ ⊢ T1 ➡*[n1+n2,h] T2.
/2 width=3 by ltc_sn/ qed-.

lemma cpms_step_dx (h) (G) (L): ∀n1,T1,T. ⦃G,L⦄ ⊢ T1 ➡*[n1,h] T →
                                ∀n2,T2. ⦃G,L⦄ ⊢ T ➡[n2,h] T2 → ⦃G,L⦄ ⊢ T1 ➡*[n1+n2,h] T2.
/2 width=3 by ltc_dx/ qed-.

(* Basic_2A1: uses: cprs_bind_dx *)
lemma cpms_bind_dx (n) (h) (G) (L):
                   ∀V1,V2. ⦃G,L⦄ ⊢ V1 ➡[h] V2 →
                   ∀I,T1,T2. ⦃G,L.ⓑ{I}V1⦄ ⊢ T1 ➡*[n,h] T2 →
                   ∀p. ⦃G,L⦄ ⊢ ⓑ{p,I}V1.T1 ➡*[n,h] ⓑ{p,I}V2.T2.
#n #h #G #L #V1 #V2 #HV12 #I #T1 #T2 #H #a @(cpms_ind_sn … H) -T1
/3 width=3 by cpms_step_sn, cpm_cpms, cpm_bind/ qed.

lemma cpms_appl_dx (n) (h) (G) (L):
                   ∀V1,V2. ⦃G,L⦄ ⊢ V1 ➡[h] V2 →
                   ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 →
                   ⦃G,L⦄ ⊢ ⓐV1.T1 ➡*[n,h] ⓐV2.T2.
#n #h #G #L #V1 #V2 #HV12 #T1 #T2 #H @(cpms_ind_sn … H) -T1
/3 width=3 by cpms_step_sn, cpm_cpms, cpm_appl/
qed.

lemma cpms_zeta (n) (h) (G) (L):
                ∀T1,T. ⬆*[1] T ≘ T1 →
                ∀V,T2. ⦃G,L⦄ ⊢ T ➡*[n,h] T2 → ⦃G,L⦄ ⊢ +ⓓV.T1 ➡*[n,h] T2.
#n #h #G #L #T1 #T #HT1 #V #T2 #H @(cpms_ind_dx … H) -T2
/3 width=3 by cpms_step_dx, cpm_cpms, cpm_zeta/
qed.

(* Basic_2A1: uses: cprs_zeta *)
lemma cpms_zeta_dx (n) (h) (G) (L):
                   ∀T2,T. ⬆*[1] T2 ≘ T →
                   ∀V,T1. ⦃G,L.ⓓV⦄ ⊢ T1 ➡*[n,h] T → ⦃G,L⦄ ⊢ +ⓓV.T1 ➡*[n,h] T2.
#n #h #G #L #T2 #T #HT2 #V #T1 #H @(cpms_ind_sn … H) -T1
/3 width=3 by cpms_step_sn, cpm_cpms, cpm_bind, cpm_zeta/
qed.

(* Basic_2A1: uses: cprs_eps *)
lemma cpms_eps (n) (h) (G) (L):
               ∀T1,T2. ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 →
               ∀V. ⦃G,L⦄ ⊢ ⓝV.T1 ➡*[n,h] T2.
#n #h #G #L #T1 #T2 #H @(cpms_ind_sn … H) -T1
/3 width=3 by cpms_step_sn, cpm_cpms, cpm_eps/
qed.

lemma cpms_ee (n) (h) (G) (L):
              ∀U1,U2. ⦃G,L⦄ ⊢ U1 ➡*[n,h] U2 →
              ∀T. ⦃G,L⦄ ⊢ ⓝU1.T ➡*[↑n,h] U2.
#n #h #G #L #U1 #U2 #H @(cpms_ind_sn … H) -U1 -n
[ /3 width=1 by cpm_cpms, cpm_ee/
| #n1 #n2 #U1 #U #HU1 #HU2 #_ #T >plus_S1
  /3 width=3 by cpms_step_sn, cpm_ee/
]
qed.

(* Basic_2A1: uses: cprs_beta_dx *)
lemma cpms_beta_dx (n) (h) (G) (L):
                   ∀V1,V2. ⦃G,L⦄ ⊢ V1 ➡[h] V2 →
                   ∀W1,W2. ⦃G,L⦄ ⊢ W1 ➡[h] W2 →
                   ∀T1,T2. ⦃G,L.ⓛW1⦄ ⊢ T1 ➡*[n,h] T2 →
                   ∀p. ⦃G,L⦄ ⊢ ⓐV1.ⓛ{p}W1.T1 ➡*[n,h] ⓓ{p}ⓝW2.V2.T2.
#n #h #G #L #V1 #V2 #HV12 #W1 #W2 #HW12 #T1 #T2 #H @(cpms_ind_dx … H) -T2
/4 width=7 by cpms_step_dx, cpm_cpms, cpms_bind_dx, cpms_appl_dx, cpm_beta/
qed.

(* Basic_2A1: uses: cprs_theta_dx *)
lemma cpms_theta_dx (n) (h) (G) (L):
                    ∀V1,V. ⦃G,L⦄ ⊢ V1 ➡[h] V →
                    ∀V2. ⬆*[1] V ≘ V2 →
                    ∀W1,W2. ⦃G,L⦄ ⊢ W1 ➡[h] W2 →
                    ∀T1,T2. ⦃G,L.ⓓW1⦄ ⊢ T1 ➡*[n,h] T2 →
                    ∀p. ⦃G,L⦄ ⊢ ⓐV1.ⓓ{p}W1.T1 ➡*[n,h] ⓓ{p}W2.ⓐV2.T2.
#n #h #G #L #V1 #V #HV1 #V2 #HV2 #W1 #W2 #HW12 #T1 #T2 #H @(cpms_ind_dx … H) -T2
/4 width=9 by cpms_step_dx, cpm_cpms, cpms_bind_dx, cpms_appl_dx, cpm_theta/
qed.

(* Basic properties with r-transition ***************************************)

(* Basic_1: was: pr3_refl *)
lemma cprs_refl: ∀h,G,L. reflexive … (cpms h G L 0).
/2 width=1 by cpm_cpms/ qed.

(* Advanced properties ******************************************************)

lemma cpms_sort (h) (G) (L) (n):
                ∀s. ⦃G,L⦄ ⊢ ⋆s ➡*[n,h] ⋆((next h)^n s).
#h #G #L #n elim n -n [ // ]
#n #IH #s <plus_SO
/3 width=3 by cpms_step_dx, cpm_sort/
qed.

(* Basic inversion lemmas ***************************************************)

lemma cpms_inv_sort1 (n) (h) (G) (L): ∀X2,s. ⦃G,L⦄ ⊢ ⋆s ➡*[n,h] X2 → X2 = ⋆(((next h)^n) s).
#n #h #G #L #X2 #s #H @(cpms_ind_dx … H) -X2 //
#n1 #n2 #X #X2 #_ #IH #HX2 destruct
elim (cpm_inv_sort1 … HX2) -HX2 #H #_ destruct //
qed-.

lemma cpms_inv_lref1_ctop (n) (h) (G):
      ∀X2,i. ⦃G,⋆⦄ ⊢ #i ➡*[n,h] X2 → ∧∧ X2 = #i & n = 0.
#n #h #G #X2 #i #H @(cpms_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpm_inv_lref1_ctop … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpms_inv_zero1_unit (n) (h) (I) (K) (G):
      ∀X2. ⦃G,K.ⓤ{I}⦄ ⊢ #0 ➡*[n,h] X2 → ∧∧ X2 = #0 & n = 0.
#n #h #I #G #K #X2 #H @(cpms_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpm_inv_zero1_unit … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpms_inv_gref1 (n) (h) (G) (L):
      ∀X2,l. ⦃G,L⦄ ⊢ §l ➡*[n,h] X2 → ∧∧ X2 = §l & n = 0.
#n #h #G #L #X2 #l #H @(cpms_ind_dx … H) -X2
[ /2 width=1 by conj/
| #n1 #n2 #X #X2 #_ * #HX #Hn1 #HX2 destruct
  elim (cpm_inv_gref1 … HX2) -HX2 #H1 #H2 destruct
  /2 width=1 by conj/
]
qed-.

lemma cpms_inv_cast1 (h) (n) (G) (L):
      ∀W1,T1,X2. ⦃G,L⦄ ⊢ ⓝW1.T1 ➡*[n,h] X2 →
      ∨∨ ∃∃W2,T2. ⦃G,L⦄ ⊢ W1 ➡*[n,h] W2 & ⦃G,L⦄ ⊢ T1 ➡*[n,h] T2 & X2 = ⓝW2.T2
       | ⦃G,L⦄ ⊢ T1 ➡*[n,h] X2
       | ∃∃m. ⦃G,L⦄ ⊢ W1 ➡*[m,h] X2 & n = ↑m.
#h #n #G #L #W1 #T1 #X2 #H @(cpms_ind_dx … H) -n -X2
[ /3 width=5 by or3_intro0, ex3_2_intro/
| #n1 #n2 #X #X2 #_ * [ * || * ]
  [ #W #T #HW1 #HT1 #H #HX2 destruct
    elim (cpm_inv_cast1 … HX2) -HX2 [ * || * ]
    [ #W2 #T2 #HW2 #HT2 #H destruct
      /4 width=5 by cpms_step_dx, ex3_2_intro, or3_intro0/
    | #HX2 /3 width=3 by cpms_step_dx, or3_intro1/
    | #m #HX2 #H destruct <plus_n_Sm
      /4 width=3 by cpms_step_dx, ex2_intro, or3_intro2/
    ]
  | #HX #HX2 /3 width=3 by cpms_step_dx, or3_intro1/
  | #m #HX #H #HX2 destruct
    /4 width=3 by cpms_step_dx, ex2_intro, or3_intro2/
  ]
]
qed-.

(* Basic_2A1: removed theorems 5:
              sta_cprs_scpds lstas_scpds scpds_strap1 scpds_fwd_cprs
              scpds_inv_lstas_eq
*)
