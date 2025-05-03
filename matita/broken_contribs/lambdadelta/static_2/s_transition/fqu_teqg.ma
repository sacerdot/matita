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

include "static_2/syntax/teqg.ma".
include "static_2/s_transition/fqu_length.ma".

(* SUPCLOSURE ***************************************************************)

(* Inversion lemmas with context-free generic equivalence for terms *********)

fact fqu_inv_teqg_aux (S) (b):
     ∀G1,G2,L1,L2,T1,T2. ❨G1,L1,T1❩ ⬂[b] ❨G2,L2,T2❩ →
     G1 = G2 → |L1| = |L2| → T1 ≛[S] T2 → ⊥.
#S #b #G1 #G2 #L1 #L2 #T1 #T2 * -G1 -G2 -L1 -L2 -T1 -T2
[1: #I #G #L #V #_ #H elim (eq_inv_nsucc_refl … H)
|6: #I #G #L #T #U #_ #_ #H elim (eq_inv_nsucc_refl … H)
]
/2 width=6 by teqg_inv_pair_xy_y, teqg_inv_pair_xy_x/
qed-.

(* Basic_2A1: uses: fqu_inv_eq *)
lemma fqu_inv_teqg (S) (b):
      ∀G,L1,L2,T1,T2. ❨G,L1,T1❩ ⬂[b] ❨G,L2,T2❩ →
      |L1| = |L2| → T1 ≛[S] T2 → ⊥.
#S #b #G #L1 #L2 #T1 #T2 #H
@(fqu_inv_teqg_aux … H) // (**) (* full auto fails *)
qed-.
