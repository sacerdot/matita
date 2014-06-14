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
include "basic_2/computation/cpds.ma".

(* DECOMPOSED EXTENDED PARALLEL COMPUTATION ON TERMS ************************)

(* Advanced properties ******************************************************)

lemma cpds_strap2: ∀h,g,G,L,T1,T,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 →
                   ⦃G, L⦄ ⊢ T1 •[h] T → ⦃G, L⦄ ⊢ T •*➡*[h, g] T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2.
#h #g #G #L #T1 #T #T2 #l #Hl #HT1 *
#T0 #l0 #l1 #Hl10 #HT #HT0 #HT02
lapply (da_sta_conf … HT1 … Hl) <minus_plus_m_m #H0T
lapply (da_mono … H0T … HT) -HT -H0T #H destruct
/3 width=7 by lstas_step_sn, le_S_S, ex4_3_intro/
qed.

lemma cpds_cprs_trans: ∀h,g,G,L,T1,T,T2.
                       ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T → ⦃G, L⦄ ⊢ T ➡* T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2.
#h #g #G #L #T1 #T #T2 * /3 width=9 by cprs_trans, ex4_3_intro/
qed-.

lemma lstas_cpds_trans: ∀h,g,G,L,T1,T,T2,l1,l2.
                        l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 →
                        ⦃G, L⦄ ⊢ T1 •*[h, l2] T → ⦃G, L⦄ ⊢ T •*➡*[h, g] T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2.
#h #g #G #L #T1 #T #T2 #l1 #l2 #Hl21 #Hl1 #HT1 * #T0 #l3 #l4 #Hl43 #Hl3 #HT0 #HT02
lapply (lstas_da_conf … HT1 … Hl1) #H0T
lapply (da_mono … H0T … Hl3) -H0T -Hl3 #H destruct
lapply (le_minus_to_plus_r … Hl21 Hl43) -Hl21 -Hl43
/3 width=8 by lstas_trans, ex4_3_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma cpds_inv_abst1: ∀h,g,a,G,L,V1,T1,U2. ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 •*➡*[h, g] U2 →
                      ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡* V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 •*➡*[h, g] T2 &
                               U2 = ⓛ{a}V2.T2.
#h #g #a #G #L #V1 #T1 #U2 * #X #l1 #l2 #Hl21 #Hl1 #H1 #H2
lapply (da_inv_bind … Hl1) -Hl1 #Hl1
elim (lstas_inv_bind1 … H1) -H1 #U #HTU1 #H destruct
elim (cprs_inv_abst1 … H2) -H2 #V2 #T2 #HV12 #HUT2 #H destruct
/3 width=7 by ex4_3_intro, ex3_2_intro/
qed-.

lemma cpds_inv_abbr_abst: ∀h,g,a1,a2,G,L,V1,W2,T1,T2. ⦃G, L⦄ ⊢ ⓓ{a1}V1.T1 •*➡*[h, g] ⓛ{a2}W2.T2 →
                          ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 •*➡*[h, g] T & ⇧[0, 1] ⓛ{a2}W2.T2 ≡ T & a1 = true.
#h #g #a1 #a2 #G #L #V1 #W2 #T1 #T2 * #X #l1 #l2 #Hl21 #Hl1 #H1 #H2
lapply (da_inv_bind … Hl1) -Hl1 #Hl1
elim (lstas_inv_bind1 … H1) -H1 #U1 #HTU1 #H destruct
elim (cprs_inv_abbr1 … H2) -H2 *
[ #V2 #U2 #HV12 #HU12 #H destruct
| /3 width=7 by ex4_3_intro, ex3_intro/
]
qed-.

(* Advanced forward lemmas **************************************************)

lemma cpds_fwd_cpxs: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
#h #g #G #L #T1 #T2 * /3 width=5 by cpxs_trans, lstas_cpxs, cprs_cpxs/
qed-.
