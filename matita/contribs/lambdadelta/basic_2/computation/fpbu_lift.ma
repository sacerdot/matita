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

include "basic_2/static/ssta_ssta.ma".
include "basic_2/computation/cpxs_lift.ma".
include "basic_2/computation/fpbu.ma".

(* UNITARY "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **************)

(* Advanced properties ******************************************************)

lemma lsstas_fpbu: ∀h,g,G,L,T1,T2,l2. ⦃G, L⦄ ⊢ T1 •*[h, g, l2] T2 → (T1 = T2 → ⊥) →
                   ∀l1. l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 → ⦃G, L, T1⦄ ≻[h, g] ⦃G, L, T2⦄.
/4 width=5 by fpbu_cpxs, lsstas_cpxs/ qed.

lemma ssta_fpbu: ∀h,g,G,L,T1,T2,l. ⦃G, L⦄ ⊢ T1 ▪[h, g] l+1 →
                 ⦃G, L⦄ ⊢ T1 •[h, g] T2 → ⦃G, L, T1⦄ ≻[h, g] ⦃G, L, T2⦄.
#h #g #G #L #T1 #T2 #l #HT1 #HT12 elim (eq_term_dec T1 T2)
/3 width=5 by ssta_lsstas, lsstas_fpbu/ #H destruct 
elim (ssta_inv_refl_pos … HT1 … HT12)
qed.
