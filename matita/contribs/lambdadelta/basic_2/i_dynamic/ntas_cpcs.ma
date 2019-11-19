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

include "basic_2/rt_equivalence/cpcs_cprs.ma".
include "basic_2/i_dynamic/ntas.ma".

(* ITERATED NATIVE TYPE ASSIGNMENT FOR TERMS ********************************)

(* Properties with r-equivalence for terms **********************************)

lemma ntas_zero (h) (a) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 ![h,a] → ⦃G,L⦄ ⊢ T2 ![h,a] → ⦃G,L⦄ ⊢ T1 ⬌*[h] T2 → ⦃G,L⦄ ⊢ T1 :*[h,a,0] T2.
#h #a #G #L #T1 #T2 #HT1 #HT2 #H
elim (cpcs_inv_cprs … H) -H #T0 #HT10 #HT20
/2 width=3 by ntas_intro/
qed.

(* Inversion lemmas with r-equivalence for terms ****************************)

lemma ntas_inv_zero (h) (a) (G) (L):
      ∀T1,T2. ⦃G,L⦄ ⊢ T1 :*[h,a,0] T2 →
      ∧∧ ⦃G,L⦄ ⊢ T1 ![h,a] & ⦃G,L⦄ ⊢ T2 ![h,a] & ⦃G,L⦄ ⊢ T1 ⬌*[h] T2.
#h #a #G #L #T1 #T2 * #T0 #HT1 #HT2 #HT20 #HT10
/3 width=3 by cprs_div, and3_intro/
qed-.
