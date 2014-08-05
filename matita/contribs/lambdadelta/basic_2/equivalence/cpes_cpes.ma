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

include "basic_2/computation/cpds_cpds.ma".
include "basic_2/equivalence/cpes.ma".

(* DECOMPOSED EXTENDED PARALLEL EQUIVALENCE FOR TERMS ***********************)

(* Advanced inversion lemmas ************************************************)

lemma cpes_inv_abst2: ∀h,g,a,G,L,T1,T2,W2,l1,l2. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] ⓛ{a}W2.T2 →
                      ∃∃W,T. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l1] ⓛ{a}W.T & ⦃G, L⦄ ⊢ W2 ➡* W & 
                             ⦃G, L.ⓛW2⦄ ⊢ T2 •*➡*[h, g, l2] T.
#h #g #a #G #L #T1 #T2 #W2 #l1 #l2 * #T0 #HT10 #H
elim (cpds_inv_abst1 … H) -H #W #T #HW2 #HT2 #H destruct /2 width=5 by ex3_2_intro/
qed-.

(* Advanced properties ******************************************************)

lemma cpes_refl: ∀h,g,G,L,T,l1,l2. l2 ≤ l1 → ⦃G, L⦄ ⊢ T ▪[h, g] l1 →
                 ⦃G, L⦄ ⊢ T •*⬌*[h, g, l2, l2] T.
#h #g #G #L #T #l1 #l2 #Hl21 #Hl1
elim (da_inv_sta … Hl1) #U #HTU
elim (lstas_total … HTU l2) -U /3 width=3 by cpds_div, lstas_cpds/
qed.

lemma lstas_cpes_trans: ∀h,g,G,L,T1,l0,l1. ⦃G, L⦄ ⊢ T1 ▪[h, g] l0 → l1 ≤ l0 →
                        ∀T. ⦃G, L⦄ ⊢ T1 •*[h, l1] T →
                        ∀T2,l,l2. ⦃G, L⦄ ⊢ T •*⬌*[h,g,l,l2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h,g,l1+l,l2] T2.
#h #g #G #L #T1 #l0 #l1 #Hl0 #Hl10 #T #HT1 #T2 #l #l2 *
/3 width=3 by cpds_div, lstas_cpds_trans/ qed-.

(* Main properties **********************************************************)

theorem cpes_trans: ∀h,g,G,L,T1,T,l1,l. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l] T →
                    ∀T2,l2. ⦃G, L⦄ ⊢ T •*⬌*[h, g, l, l2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2.
#h #g #G #L #T1 #T #l1 #l * #X1 #HT1X1 #HTX1 #T2 #l2 * #X2 #HTX2 #HT2X2
elim (cpds_conf_eq … HTX1 … HTX2) -T -l /3 width=5 by cpds_cprs_trans, cpds_div/
qed-.

theorem cpes_canc_sn: ∀h,g,G,L,T,T1,l,l1. ⦃G, L⦄ ⊢ T •*⬌*[h, g, l, l1] T1 →
                      ∀T2,l2. ⦃G, L⦄ ⊢ T •*⬌*[h, g, l, l2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2.
#h #g #G #L #T #T1 #l #l1 #HT1
@cpes_trans /2 width=1 by cpes_sym/ (**) (* full auto raises NTypeChecker failure *)
qed-.

theorem cpes_canc_dx: ∀h,g,G,L,T1,T,l1,l. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l] T →
                      ∀T2,l2. ⦃G, L⦄ ⊢ T2 •*⬌*[h, g, l2, l] T → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2.
#h #g #G #L #T1 #T #l1 #l #HT1 #T2 #l2 #HT2
@(cpes_trans … HT1) -T1 -l1 /2 width=1 by cpes_sym/ (**) (* full auto raises NTypeChecker failure *)
qed-.
