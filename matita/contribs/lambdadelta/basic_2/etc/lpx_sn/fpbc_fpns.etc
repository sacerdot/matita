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

include "basic_2/computation/fpns_fpns.ma".
include "basic_2/computation/fpbu_fpns.ma".
include "basic_2/computation/fpbc.ma".

(* SINGLE-STEP "BIG TREE" PROPER PARALLEL COMPUTATION FOR CLOSURES **********)

(* Properties on parallel computation for "big tree" normal forms ***********)

lemma fpbc_fpns_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ≻⋕[h, g] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ⊢ ⋕➡*[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≻⋕[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 *
/3 width=9 by fpns_trans, ex2_3_intro/
qed-.

lemma fpns_fpbc_trans: ∀h,g,G1,G,G2,L1,L,L2,T1,T,T2. ⦃G1, L1, T1⦄ ⊢ ⋕➡*[h, g] ⦃G, L, T⦄ →
                       ⦃G, L, T⦄ ≻⋕[h, g] ⦃G2, L2, T2⦄ → ⦃G1, L1, T1⦄ ≻⋕[h, g] ⦃G2, L2, T2⦄.
#h #g #G1 #G #G2 #L1 #L #L2 #T1 #T #T2 #H1 *
#G0 #L0 #T0 #H0 #H02 elim (fpns_fpbu_trans … H1 … H0) -G -L -T
/3 width=9 by fpns_trans, ex2_3_intro/
qed-.
