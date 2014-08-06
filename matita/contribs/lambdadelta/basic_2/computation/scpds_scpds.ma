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

include "basic_2/unfold/lstas_lstas.ma".
include "basic_2/computation/lprs_cprs.ma".
include "basic_2/computation/cpxs_cpxs.ma".
include "basic_2/computation/scpds.ma".

(* STRATIFIED DECOMPOSED PARALLEL COMPUTATION ON TERMS **********************)

(* Advanced properties ******************************************************)

lemma scpds_strap2: ∀h,g,G,L,T1,T,T2,l1,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l1+1 →
                    ⦃G, L⦄ ⊢ T1 •[h] T → ⦃G, L⦄ ⊢ T •*➡*[h, g, l] T2 →
                    ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l+1] T2.
#h #g #G #L #T1 #T #T2 #l1 #l #Hl1 #HT1 *
#T0 #l0 #Hl0 #HTl0 #HT0 #HT02
lapply (da_sta_conf … HT1 … Hl1) <minus_plus_m_m #HTl1
lapply (da_mono … HTl0 … HTl1) -HTl0 -HTl1 #H destruct
/3 width=6 by lstas_step_sn, le_S_S, ex4_2_intro/
qed.

lemma scpds_cprs_trans: ∀h,g,G,L,T1,T,T2,l.
                        ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l] T → ⦃G, L⦄ ⊢ T ➡* T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l] T2.
#h #g #G #L #T1 #T #T2 #l * /3 width=8 by cprs_trans, ex4_2_intro/
qed-.

lemma lstas_scpds_trans: ∀h,g,G,L,T1,T,T2,l1,l2,l.
                         l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 →
                         ⦃G, L⦄ ⊢ T1 •*[h, l2] T → ⦃G, L⦄ ⊢ T •*➡*[h, g, l] T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l2+l] T2.
#h #g #G #L #T1 #T #T2 #l1 #l2 #l #Hl21 #HTl1 #HT1 * #T0 #l0 #Hl0 #HTl0 #HT0 #HT02
lapply (lstas_da_conf … HT1 … HTl1) #HTl12
lapply (da_mono … HTl12 … HTl0) -HTl12 -HTl0 #H destruct
lapply (le_minus_to_plus_r … Hl21 Hl0) -Hl21 -Hl0
/3 width=7 by lstas_trans, ex4_2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma scpds_inv_abst1: ∀h,g,a,G,L,V1,T1,U2,l. ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 •*➡*[h, g, l] U2 →
                       ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡* V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 •*➡*[h, g, l] T2 &
                                U2 = ⓛ{a}V2.T2.
#h #g #a #G #L #V1 #T1 #U2 #l2 * #X #l1 #Hl21 #Hl1 #H1 #H2
lapply (da_inv_bind … Hl1) -Hl1 #Hl1
elim (lstas_inv_bind1 … H1) -H1 #U #HTU1 #H destruct
elim (cprs_inv_abst1 … H2) -H2 #V2 #T2 #HV12 #HUT2 #H destruct
/3 width=6 by ex4_2_intro, ex3_2_intro/
qed-.

lemma scpds_inv_abbr_abst: ∀h,g,a1,a2,G,L,V1,W2,T1,T2,l. ⦃G, L⦄ ⊢ ⓓ{a1}V1.T1 •*➡*[h, g, l] ⓛ{a2}W2.T2 →
                           ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 •*➡*[h, g, l] T & ⇧[0, 1] ⓛ{a2}W2.T2 ≡ T & a1 = true.
#h #g #a1 #a2 #G #L #V1 #W2 #T1 #T2 #l2 * #X #l1 #Hl21 #Hl1 #H1 #H2
lapply (da_inv_bind … Hl1) -Hl1 #Hl1
elim (lstas_inv_bind1 … H1) -H1 #U1 #HTU1 #H destruct
elim (cprs_inv_abbr1 … H2) -H2 *
[ #V2 #U2 #HV12 #HU12 #H destruct
| /3 width=6 by ex4_2_intro, ex3_intro/
]
qed-.

lemma scpds_inv_lstas_eq: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l] T2 →
                          ∀T. ⦃G, L⦄ ⊢ T1 •*[h, l] T → ⦃G, L⦄ ⊢ T ➡* T2.
#h #g #G #L #T1 #T2 #l2 *
#T0 #l1 #_ #_ #HT10 #HT02 #T #HT1
lapply (lstas_mono … HT10 … HT1) #H destruct //
qed-.

(* Advanced forward lemmas **************************************************)

lemma scpds_fwd_cpxs: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
#h #g #G #L #T1 #T2 #l * /3 width=5 by cpxs_trans, lstas_cpxs, cprs_cpxs/
qed-.

(* Main properties **********************************************************)

theorem scpds_conf_eq: ∀h,g,G,L,T0,T1,l. ⦃G, L⦄ ⊢ T0 •*➡*[h, g, l] T1 →
                       ∀T2. ⦃G, L⦄ ⊢ T0 •*➡*[h, g, l] T2 →
                       ∃∃T. ⦃G, L⦄ ⊢ T1 ➡* T & ⦃G, L⦄ ⊢ T2 ➡* T.
#h #g #G #L #T0 #T1 #l0 * #U1 #l1 #_ #_ #H1 #HUT1 #T2 * #U2 #l2 #_ #_ #H2 #HUT2 -l1 -l2
lapply (lstas_mono … H1 … H2) #H destruct -h -l0 /2 width=3 by cprs_conf/
qed-.
