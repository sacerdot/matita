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
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/equivalence/scpes.ma".

(* STRATIFIED DECOMPOSED PARALLEL EQUIVALENCE FOR TERMS *********************)

(* Inversion lemmas on parallel equivalence for terms ***********************)

lemma scpes_inv_lstas_eq: ∀h,g,G,L,T1,T2,l1,l2. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l1, l2] T2 →
                         ∀U1. ⦃G, L⦄ ⊢ T1 •*[h, l1] U1 →
                         ∀U2. ⦃G, L⦄ ⊢ T2 •*[h, l2] U2 → ⦃G, L⦄ ⊢ U1 ⬌* U2.
#h #g #G #L #T1 #T2 #l1 #l2 * #T #HT1 #HT2 #U1 #HTU1 #U2 #HTU2
/3 width=8 by scpds_inv_lstas_eq, cprs_div/
qed-.

(* Properties on parallel equivalence for terms ***********************)

lemma cpcs_scpes: ∀h,g,G,L,T1,l11. ⦃G, L⦄ ⊢ T1 ▪[h, g] l11 →
                  ∀U1,l12. l12 ≤ l11 → ⦃G, L⦄ ⊢ T1 •*[h, l12] U1 →
                  ∀T2,l21. ⦃G, L⦄ ⊢ T2 ▪[h, g] l21 →
                  ∀U2,l22. l22 ≤ l21 → ⦃G, L⦄ ⊢ T2 •*[h, l22] U2 →
                  ⦃G, L⦄ ⊢ U1 ⬌* U2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, l12, l22] T2.
#h #g #G #L #T1 #l11 #HT1 #U1 #l12 #Hl121 #HTU1 #T2 #l21 #HT2 #U2 #l22 #Hl221 #HTU2 #HU12
elim (cpcs_inv_cprs … HU12) -HU12 /3 width=6 by scpds_div, ex4_2_intro/
qed.
