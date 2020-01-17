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

include "basic_2A/unfold/lstas_da.ma".
include "basic_2A/computation/lprs_cprs.ma".
include "basic_2A/computation/cpxs_cpxs.ma".
include "basic_2A/computation/scpds.ma".

(* STRATIFIED DECOMPOSED PARALLEL COMPUTATION ON TERMS **********************)

(* Advanced properties ******************************************************)

lemma scpds_strap2: ∀h,g,G,L,T1,T,T2,d1,d. ⦃G, L⦄ ⊢ T1 ▪[h, g] d1+1 →
                    ⦃G, L⦄ ⊢ T1 •*[h, 1] T → ⦃G, L⦄ ⊢ T •*➡*[h, g, d] T2 →
                    ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d+1] T2.
#h #g #G #L #T1 #T #T2 #d1 #d #Hd1 #HT1 *
#T0 #d0 #Hd0 #HTd0 #HT0 #HT02
lapply (lstas_da_conf … HT1 … Hd1) <minus_plus_m_m #HTd1
lapply (da_mono … HTd0 … HTd1) -HTd0 -HTd1 #H destruct
lapply (lstas_trans … HT1 … HT0) -T >commutative_plus
/3 width=6 by le_S_S, ex4_2_intro/
qed.

lemma scpds_cprs_trans: ∀h,g,G,L,T1,T,T2,d.
                        ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d] T → ⦃G, L⦄ ⊢ T ➡* T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d] T2.
#h #g #G #L #T1 #T #T2 #d * /3 width=8 by cprs_trans, ex4_2_intro/
qed-.

lemma lstas_scpds_trans: ∀h,g,G,L,T1,T,T2,d1,d2,d.
                         d2 ≤ d1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] d1 →
                         ⦃G, L⦄ ⊢ T1 •*[h, d2] T → ⦃G, L⦄ ⊢ T •*➡*[h, g, d] T2 → ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d2+d] T2.
#h #g #G #L #T1 #T #T2 #d1 #d2 #d #Hd21 #HTd1 #HT1 * #T0 #d0 #Hd0 #HTd0 #HT0 #HT02
lapply (lstas_da_conf … HT1 … HTd1) #HTd12
lapply (da_mono … HTd12 … HTd0) -HTd12 -HTd0 #H destruct
lapply (le_minus_to_plus_r … Hd21 Hd0) -Hd21 -Hd0
/3 width=7 by lstas_trans, ex4_2_intro/
qed-.

(* Advanced inversion lemmas ************************************************)

lemma scpds_inv_abst1: ∀h,g,a,G,L,V1,T1,U2,d. ⦃G, L⦄ ⊢ ⓛ{a}V1.T1 •*➡*[h, g, d] U2 →
                       ∃∃V2,T2. ⦃G, L⦄ ⊢ V1 ➡* V2 & ⦃G, L.ⓛV1⦄ ⊢ T1 •*➡*[h, g, d] T2 &
                                U2 = ⓛ{a}V2.T2.
#h #g #a #G #L #V1 #T1 #U2 #d2 * #X #d1 #Hd21 #Hd1 #H1 #H2
lapply (da_inv_bind … Hd1) -Hd1 #Hd1
elim (lstas_inv_bind1 … H1) -H1 #U #HTU1 #H destruct
elim (cprs_inv_abst1 … H2) -H2 #V2 #T2 #HV12 #HUT2 #H destruct
/3 width=6 by ex4_2_intro, ex3_2_intro/
qed-.

lemma scpds_inv_abbr_abst: ∀h,g,a1,a2,G,L,V1,W2,T1,T2,d. ⦃G, L⦄ ⊢ ⓓ{a1}V1.T1 •*➡*[h, g, d] ⓛ{a2}W2.T2 →
                           ∃∃T. ⦃G, L.ⓓV1⦄ ⊢ T1 •*➡*[h, g, d] T & ⬆[0, 1] ⓛ{a2}W2.T2 ≡ T & a1 = true.
#h #g #a1 #a2 #G #L #V1 #W2 #T1 #T2 #d2 * #X #d1 #Hd21 #Hd1 #H1 #H2
lapply (da_inv_bind … Hd1) -Hd1 #Hd1
elim (lstas_inv_bind1 … H1) -H1 #U1 #HTU1 #H destruct
elim (cprs_inv_abbr1 … H2) -H2 *
[ #V2 #U2 #HV12 #HU12 #H destruct
| /3 width=6 by ex4_2_intro, ex3_intro/
]
qed-.

lemma scpds_inv_lstas_eq: ∀h,g,G,L,T1,T2,d. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d] T2 →
                          ∀T. ⦃G, L⦄ ⊢ T1 •*[h, d] T → ⦃G, L⦄ ⊢ T ➡* T2.
#h #g #G #L #T1 #T2 #d2 *
#T0 #d1 #_ #_ #HT10 #HT02 #T #HT1
lapply (lstas_mono … HT10 … HT1) #H destruct //
qed-.

(* Advanced forward lemmas **************************************************)

lemma scpds_fwd_cpxs: ∀h,g,G,L,T1,T2,d. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d] T2 → ⦃G, L⦄ ⊢ T1 ➡*[h, g] T2.
#h #g #G #L #T1 #T2 #d * /3 width=5 by cpxs_trans, lstas_cpxs, cprs_cpxs/
qed-.

(* Main properties **********************************************************)

theorem scpds_conf_eq: ∀h,g,G,L,T0,T1,d. ⦃G, L⦄ ⊢ T0 •*➡*[h, g, d] T1 →
                       ∀T2. ⦃G, L⦄ ⊢ T0 •*➡*[h, g, d] T2 →
                       ∃∃T. ⦃G, L⦄ ⊢ T1 ➡* T & ⦃G, L⦄ ⊢ T2 ➡* T.
#h #g #G #L #T0 #T1 #d0 * #U1 #d1 #_ #_ #H1 #HUT1 #T2 * #U2 #d2 #_ #_ #H2 #HUT2 -d1 -d2
lapply (lstas_mono … H1 … H2) #H destruct -h -d0 /2 width=3 by cprs_conf/
qed-.
