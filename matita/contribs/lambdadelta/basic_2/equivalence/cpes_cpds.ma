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

include "basic_2/computation/cpds.ma".
include "basic_2/equivalence/cpcs_cpcs.ma".
include "basic_2/equivalence/cpes.ma".

(* DECOMPOSED EXTENDED PARALLEL EQUIVALENCE FOR TERMS ***********************)

(* Advanced properties ******************************************************)

lemma cpds_cpes_dx: ∀h,g,G,L,T1,T2. ⦃G, L⦄ ⊢ T1 •*➡*[h, g] T2 → ⦃G, L⦄ ⊢ T1 •*⬌*[h, g] T2.
#h #g #G #L #T1 #T2 * /3 width=7 by cpcs_cprs_dx, ex4_3_intro/
qed.

(* Advanced inversion lemmas ************************************************)

lemma cpes_inv_abst2: ∀h,g,a,G,L,W1,T1,T. ⦃G, L⦄ ⊢ T •*⬌*[h, g] ⓛ{a}W1.T1 →
                      ∃∃W2,T2. ⦃G, L⦄ ⊢ T •*➡*[h, g] ⓛ{a}W2.T2 & ⦃G, L⦄ ⊢ ⓛ{a}W1.T1 ➡* ⓛ{a}W2.T2.
#h #g #a #G #L #W1 #T1 #T * #T0 #l #l0 #Hl0 #Hl #HT0 #H
elim (cpcs_inv_abst2 … H) -H /3 width=7 by ex4_3_intro, ex2_2_intro/
qed-.
