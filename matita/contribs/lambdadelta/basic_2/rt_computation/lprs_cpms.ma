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

include "basic_2/rt_computation/lprs_lpr.ma".

(* PARALLEL R-COMPUTATION FOR FULL LOCAL ENVIRONMENTS ***********************)

(* Properties with t-bound context-sensitive rt-computarion for terms *******)

lemma lprs_cpms_trans (n) (h) (G):
                      ∀L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡*[n, h] T2 →
                      ∀L1. ⦃G, L1⦄ ⊢ ➡*[h] L2 → ⦃G, L1⦄ ⊢ T1 ➡*[n, h] T2.
#n #h #G #L2 #T1 #T2 #HT12 #L1 #H
@(lprs_ind_sn … H) -L1 /2 width=3 by lpr_cpms_trans/
qed-.

lemma lprs_cpm_trans (n) (h) (G):
                     ∀L2,T1,T2. ⦃G, L2⦄ ⊢ T1 ➡[n, h] T2 →
                     ∀L1. ⦃G, L1⦄ ⊢ ➡*[h] L2 → ⦃G, L1⦄ ⊢ T1 ➡*[n, h] T2.
/3 width=3 by lprs_cpms_trans, cpm_cpms/ qed-.

(* Basic_2A1: includes cprs_bind2 *)
lemma cpms_bind_dx (n) (h) (G) (L):
                   ∀V1,V2. ⦃G, L⦄ ⊢ V1 ➡*[h] V2 →
                   ∀I,T1,T2. ⦃G, L.ⓑ{I}V2⦄ ⊢ T1 ➡*[n, h] T2 →
                   ∀p. ⦃G, L⦄ ⊢ ⓑ{p,I}V1.T1 ➡*[n, h] ⓑ{p,I}V2.T2.
/4 width=5 by lprs_cpms_trans, lprs_pair, cpms_bind/ qed.

(* Inversion lemmas with t-bound context-sensitive rt-computarion for terms *)

(* Basic_1: was: pr3_gen_abst *)
(* Basic_2A1: includes: cprs_inv_abst1 *)
(* Basic_2A1: uses: scpds_inv_abst1 *)
lemma cpms_inv_abst_sn (n) (h) (G) (L):
                       ∀p,V1,T1,X2. ⦃G, L⦄ ⊢ ⓛ{p}V1.T1 ➡*[n, h] X2 →
                       ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡*[h] V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 ➡*[n, h] T2 &
                                X2 = ⓛ{p}V2.T2.
#n #h #G #L #p #V1 #T1 #X2 #H
@(cpms_ind_dx … H) -X2 /2 width=5 by ex3_2_intro/
#n1 #n2 #X #X2 #_ * #V #T #HV1 #HT1 #H1 #H2 destruct
elim (cpm_inv_abst1 … H2) -H2 #V2 #T2 #HV2 #HT2 #H2 destruct
/5 width=7 by lprs_cpm_trans, lprs_pair, cprs_step_dx, cpms_trans, ex3_2_intro/
qed-.

lemma cpms_inv_abst_sn_cprs (h) (n) (p) (G) (L) (W):
                            ∀T,X. ⦃G,L⦄ ⊢ ⓛ{p}W.T ➡*[n,h] X →
                            ∃∃U. ⦃G,L.ⓛW⦄⊢ T ➡*[n,h] U & ⦃G,L⦄ ⊢ ⓛ{p}W.U ➡*[h] X.
#h #n #p #G #L #W #T #X #H
elim (cpms_inv_abst_sn … H) -H #W0 #U #HW0 #HTU #H destruct
@(ex2_intro … HTU) /2 width=1 by cpms_bind/
qed-.

(* Basic_2A1: includes: cprs_inv_abst *)
lemma cpms_inv_abst_bi (n) (h) (G) (L):
                       ∀p,W1,W2,T1,T2. ⦃G, L⦄ ⊢ ⓛ{p}W1.T1 ➡*[n, h] ⓛ{p}W2.T2 →
                       ∧∧ ⦃G, L⦄ ⊢ W1 ➡*[h] W2 & ⦃G, L.ⓛW1⦄ ⊢ T1 ➡*[n, h] T2.
#n #h #G #L #p #W1 #W2 #T1 #T2 #H
elim (cpms_inv_abst_sn … H) -H #W #T #HW1 #HT1 #H destruct
/2 width=1 by conj/
qed-.

(* Basic_1: was pr3_gen_abbr *)
(* Basic_2A1: includes: cprs_inv_abbr1 *)
lemma cpms_inv_abbr_sn_dx (n) (h) (G) (L):
                          ∀p,V1,T1,X2. ⦃G, L⦄ ⊢ ⓓ{p}V1.T1 ➡*[n, h] X2 →
                          ∨∨ ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡*[h] V2 & ⦃G, L.ⓓV1⦄ ⊢ T1 ➡*[n, h] T2 & X2 = ⓓ{p}V2.T2
                           | ∃∃T2. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡*[n ,h] T2 & ⬆*[1] X2 ≘ T2 & p = Ⓣ.
#n #h #G #L #p #V1 #T1 #X2 #H
@(cpms_ind_dx … H) -X2 -n /3 width=5 by ex3_2_intro, or_introl/
#n1 #n2 #X #X2 #_ * *
[ #V #T #HV1 #HT1 #H #HX2 destruct
  elim (cpm_inv_abbr1 … HX2) -HX2 *
  [ #V2 #T2 #HV2 #HT2 #H destruct
    /6 width=7 by lprs_cpm_trans, lprs_pair, cprs_step_dx, cpms_trans, ex3_2_intro, or_introl/
  | #T2 #HT2 #HTX2 #Hp -V
    elim (cpm_lifts_sn … HTX2 (Ⓣ) … (L.ⓓV1) … HT2) -T2 [| /3 width=3 by drops_refl, drops_drop/ ] #X #HX2 #HTX
    /4 width=3 by cpms_step_dx, ex3_intro, or_intror/
  ]
| #T #HT1 #HXT #Hp #HX2
  elim (cpm_lifts_sn … HX2 (Ⓣ) … (L.ⓓV1) … HXT) -X
  /4 width=3 by cpms_step_dx, drops_refl, drops_drop, ex3_intro, or_intror/
]
qed-.

(* Basic_2A1: uses: scpds_inv_abbr_abst *)
lemma cpms_inv_abbr_abst (n) (h) (G) (L):
                         ∀p1,p2,V1,W2,T1,T2. ⦃G, L⦄ ⊢ ⓓ{p1}V1.T1 ➡*[n, h] ⓛ{p2}W2.T2 →
                         ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 ➡*[n, h] T & ⬆*[1] ⓛ{p2}W2.T2 ≘ T & p1 = Ⓣ.
#n #h #G #L #p1 #p2 #V1 #W2 #T1 #T2 #H
elim (cpms_inv_abbr_sn_dx … H) -H *
[ #V #T #_ #_ #H destruct
| /2 width=3 by ex3_intro/
]
qed-.
