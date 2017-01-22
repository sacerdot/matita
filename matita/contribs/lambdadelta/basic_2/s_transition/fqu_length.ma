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

include "basic_2/syntax/lenv_length.ma".
include "basic_2/s_transition/fqu.ma".

(* SUPCLOSURE ***************************************************************)

(* Forward lemmas with length for local environments ************************)

fact fqu_fwd_length_lref1_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                               ∀i. T1 = #i → |L2| < |L1|.
#G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 // [2: #p]
#I #G #L #V #T #j #H destruct
qed-.

lemma fqu_fwd_length_lref1: ∀G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊐ ⦃G2, L2, T2⦄ →
                            |L2| < |L1|.
/2 width=7 by fqu_fwd_length_lref1_aux/
qed-.

(* Inversion lemmas with length for local environments **********************)

fact fqu_inv_eq_aux: ∀G1,G2,L1,L2,T1,T2. ⦃G1, L1, T1⦄ ⊐ ⦃G2, L2, T2⦄ →
                     G1 = G2 → |L1| = |L2| → T1 = T2 → ⊥.
#G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[1: #I #G #L #V #_ #H elim (succ_inv_refl_sn … H)
|5: #I #G #L #V #T #U #_ #_ #H elim (succ_inv_refl_sn … H)
]
/2 width=4 by discr_tpair_xy_y, discr_tpair_xy_x/
qed-.

lemma fqu_inv_eq: ∀G,L1,L2,T. ⦃G, L1, T⦄ ⊐ ⦃G, L2, T⦄ → |L1| = |L2| → ⊥.
#G #L1 #L2 #T #H #H0 @(fqu_inv_eq_aux … H … H0) // (**) (* full auto fails *)
qed-. 
