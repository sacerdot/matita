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

include "basic_2/unfold/lsstas_lift.ma".
include "basic_2/computation/fpbs.ma".

(* "BIG TREE" PARALLEL COMPUTATION FOR CLOSURES *****************************)

(* Advanced properties ******************************************************)

lemma lsstas_fpbs: ∀h,g,G,L,T1,T2,l2. ⦃G, L⦄ ⊢ T1 •*[h, g, l2] T2 →
                   ∀l1. l2 ≤ l1 → ⦃G, L⦄ ⊢ T1 ▪[h, g] l1 → ⦃G, L, T1⦄ ≥[h, g] ⦃G, L, T2⦄.
#h #g #G #L #T1 #T2 #l2 #H @(lsstas_ind_dx … H) -l2 -T2 //
#l2 #T #T2 #HT1 #HT2 #IHT1 #l1 >commutative_plus #Hl21 #Hl1
elim (le_inv_plus_l … Hl21) -Hl21 #Hl12 #Hl21
lapply (lsstas_da_conf … HT1 … Hl1) -HT1
>(plus_minus_m_m … Hl12) -Hl12
/3 width=5 by fpb_ssta, fpbs_strap1/
qed.
