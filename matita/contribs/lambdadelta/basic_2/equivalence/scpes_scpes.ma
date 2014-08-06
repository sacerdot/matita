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

include "basic_2/computation/scpds_scpds.ma".
include "basic_2/equivalence/scpes.ma".

(* STRATIFIED DECOMPOSED PARALLEL EQUIVALENCE FOR TERMS *********************)

(* Advanced inversion lemmas ************************************************)

lemma scpes_inv_abst2: ∀h,g,a,G,L,T1,T2,W2,l1,l2. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] ⓛ{a}W2.T2 →
                       ∃∃W,T. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, l1] ⓛ{a}W.T & ⦃G, L⦄ ⊢ W2 ➡* W & 
                              ⦃G, L.ⓛW2⦄ ⊢ T2 •*➡*[h, g, l2] T.
#h #g #a #G #L #T1 #T2 #W2 #l1 #l2 * #T0 #HT10 #H
elim (scpds_inv_abst1 … H) -H #W #T #HW2 #HT2 #H destruct /2 width=5 by ex3_2_intro/
qed-.

(* Advanced properties ******************************************************)

lemma scpes_refl: ∀h,g,G,L,T,l1,l2. l2 ≤ l1 → ⦃G, L⦄ ⊢ T ▪[h, g] l1 →
                  ⦃G, L⦄ ⊢ T •*⬌*[h, g, l2, l2] T.
#h #g #G #L #T #l1 #l2 #Hl21 #Hl1
elim (da_inv_sta … Hl1) #U #HTU
elim (lstas_total … HTU l2) -U /3 width=3 by scpds_div, lstas_scpds/
qed.

lemma lstas_scpes_trans: ∀h,g,G,L,T1,l0,l1. ⦃G, L⦄ ⊢ T1 ▪[h, g] l0 → l1 ≤ l0 →
                         ∀T. ⦃G, L⦄ ⊢ T1 •*[h, l1] T →
                         ∀T2,l,l2. ⦃G, L⦄ ⊢ T •*⬌*[h,g,l,l2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h,g,l1+l,l2] T2.
#h #g #G #L #T1 #l0 #l1 #Hl0 #Hl10 #T #HT1 #T2 #l #l2 *
/3 width=3 by scpds_div, lstas_scpds_trans/ qed-.

(* Main properties **********************************************************)

theorem scpes_trans: ∀h,g,G,L,T1,T,l1,l. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l] T →
                     ∀T2,l2. ⦃G, L⦄ ⊢ T •*⬌*[h, g, l, l2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2.
#h #g #G #L #T1 #T #l1 #l * #X1 #HT1X1 #HTX1 #T2 #l2 * #X2 #HTX2 #HT2X2
elim (scpds_conf_eq … HTX1 … HTX2) -T -l /3 width=5 by scpds_cprs_trans, scpds_div/
qed-.

theorem scpes_canc_sn: ∀h,g,G,L,T,T1,l,l1. ⦃G, L⦄ ⊢ T •*⬌*[h, g, l, l1] T1 →
                       ∀T2,l2. ⦃G, L⦄ ⊢ T •*⬌*[h, g, l, l2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2.
#h #g #G #L #T #T1 #l #l1 #HT1
@scpes_trans /2 width=1 by scpes_sym/ (**) (* full auto raises NTypeChecker failure *)
qed-.

theorem scpes_canc_dx: ∀h,g,G,L,T1,T,l1,l. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l] T →
                       ∀T2,l2. ⦃G, L⦄ ⊢ T2 •*⬌*[h, g, l2, l] T → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2.
#h #g #G #L #T1 #T #l1 #l #HT1 #T2 #l2 #HT2
@(scpes_trans … HT1) -T1 -l1 /2 width=1 by scpes_sym/ (**) (* full auto raises NTypeChecker failure *)
qed-.
