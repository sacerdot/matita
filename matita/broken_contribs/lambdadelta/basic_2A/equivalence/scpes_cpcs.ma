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
include "basic_2A/equivalence/cpcs_cpcs.ma".
include "basic_2A/equivalence/scpes.ma".

(* STRATIFIED DECOMPOSED PARALLEL EQUIVALENCE FOR TERMS *********************)

(* Inversion lemmas on parallel equivalence for terms ***********************)

lemma scpes_inv_lstas_eq: ∀h,g,G,L,T1,T2,d1,d2. ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d1, d2] T2 →
                          ∀U1. ⦃G, L⦄ ⊢ T1 •*[h, d1] U1 →
                          ∀U2. ⦃G, L⦄ ⊢ T2 •*[h, d2] U2 → ⦃G, L⦄ ⊢ U1 ⬌* U2.
#h #g #G #L #T1 #T2 #d1 #d2 * #T #HT1 #HT2 #U1 #HTU1 #U2 #HTU2
/3 width=8 by scpds_inv_lstas_eq, cprs_div/
qed-.

(* Properties on parallel equivalence for terms *****************************)

lemma cpcs_scpes: ∀h,g,G,L,T1,d11. ⦃G, L⦄ ⊢ T1 ▪[h, g] d11 →
                  ∀U1,d12. d12 ≤ d11 → ⦃G, L⦄ ⊢ T1 •*[h, d12] U1 →
                  ∀T2,d21. ⦃G, L⦄ ⊢ T2 ▪[h, g] d21 →
                  ∀U2,d22. d22 ≤ d21 → ⦃G, L⦄ ⊢ T2 •*[h, d22] U2 →
                  ⦃G, L⦄ ⊢ U1 ⬌* U2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g, d12, d22] T2.
#h #g #G #L #T1 #d11 #HT1 #U1 #d12 #Hd121 #HTU1 #T2 #d21 #HT2 #U2 #d22 #Hd221 #HTU2 #HU12
elim (cpcs_inv_cprs … HU12) -HU12 /3 width=6 by scpds_div, ex4_2_intro/
qed.
