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

include "basic_2A/computation/scpds_scpds.ma".
include "basic_2A/equivalence/scpes.ma".

(* STRATIFIED DECOMPOSED PARALLEL EQUIVALENCE FOR TERMS *********************)

(* Advanced inversion lemmas ************************************************)

lemma scpes_inv_abst2: ∀h,g,a,G,L,T1,T2,W2,d1,d2. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d2] ⓛ{a}W2.T2 →
                       ∃∃W,T. ⦃G, L⦄ ⊢ T1 •*➡*[h, g, d1] ⓛ{a}W.T & ⦃G, L⦄ ⊢ W2 ➡* W & 
                              ⦃G, L.ⓛW2⦄ ⊢ T2 •*➡*[h, g, d2] T.
#h #g #a #G #L #T1 #T2 #W2 #d1 #d2 * #T0 #HT10 #H
elim (scpds_inv_abst1 … H) -H #W #T #HW2 #HT2 #H destruct /2 width=5 by ex3_2_intro/
qed-.

(* Advanced properties ******************************************************)

lemma scpes_refl: ∀h,g,G,L,T,d1,d2. d2 ≤ d1 → ⦃G, L⦄ ⊢ T ▪[h, g] d1 →
                  ⦃G, L⦄ ⊢ T •*⬌*[h, g, d2, d2] T.
#h #g #G #L #T #d1 #d2 #Hd21 #Hd1
elim (da_lstas … Hd1 … d2) #U #HTU #_
/3 width=3 by scpds_div, lstas_scpds/
qed.

lemma lstas_scpes_trans: ∀h,g,G,L,T1,d0,d1. ⦃G, L⦄ ⊢ T1 ▪[h, g] d0 → d1 ≤ d0 →
                         ∀T. ⦃G, L⦄ ⊢ T1 •*[h, d1] T →
                         ∀T2,d,d2. ⦃G, L⦄ ⊢ T •*⬌*[h,g,d,d2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h,g,d1+d,d2] T2.
#h #g #G #L #T1 #d0 #d1 #Hd0 #Hd10 #T #HT1 #T2 #d #d2 *
/3 width=3 by scpds_div, lstas_scpds_trans/ qed-.

(* Properties on parallel computation for terms *****************************)

lemma cprs_scpds_div: ∀h,g,G,L,T1,T. ⦃G, L⦄ ⊢ T1 ➡* T →
                      ∀d. ⦃G, L⦄ ⊢ T1 ▪[h, g] d →
                      ∀T2,d2. ⦃G, L⦄ ⊢ T2 •*➡*[h, g, d2] T →
                      ⦃G, L⦄⊢ T1 •*⬌*[h, g, 0, d2] T2.
#h #g #G #L #T1 #T #HT1 #d #Hd elim (da_lstas … Hd 0)
#X1 #HTX1 #_ elim (cprs_strip … HT1 X1) -HT1
/3 width=5 by scpds_strap1, scpds_div, lstas_cpr, ex4_2_intro/
qed.

(* Main properties **********************************************************)

theorem scpes_trans: ∀h,g,G,L,T1,T,d1,d. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d] T →
                     ∀T2,d2. ⦃G, L⦄ ⊢ T •*⬌*[h, g, d, d2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d2] T2.
#h #g #G #L #T1 #T #d1 #d * #X1 #HT1X1 #HTX1 #T2 #d2 * #X2 #HTX2 #HT2X2
elim (scpds_conf_eq … HTX1 … HTX2) -T -d /3 width=5 by scpds_cprs_trans, scpds_div/
qed-.

theorem scpes_canc_sn: ∀h,g,G,L,T,T1,d,d1. ⦃G, L⦄ ⊢ T •*⬌*[h, g, d, d1] T1 →
                       ∀T2,d2. ⦃G, L⦄ ⊢ T •*⬌*[h, g, d, d2] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d2] T2.
/3 width=4 by scpes_trans, scpes_sym/ qed-.

theorem scpes_canc_dx: ∀h,g,G,L,T1,T,d1,d. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d] T →
                       ∀T2,d2. ⦃G, L⦄ ⊢ T2 •*⬌*[h, g, d2, d] T → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d2] T2.
/3 width=4 by scpes_trans, scpes_sym/ qed-.
