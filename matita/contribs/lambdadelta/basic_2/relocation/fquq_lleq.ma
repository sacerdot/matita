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

include "basic_2/relocation/fqu_lleq.ma".
include "basic_2/relocation/fquq_alt.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* Properties on lazy equivalence for local environments ********************)

lemma lleq_fquq_trans: ∀G1,G2,L2,K2,T,U. ⦃G1, L2, T⦄ ⊃⸮ ⦃G2, K2, U⦄ →
                       ∀L1. L1 ⋕[T, 0] L2 →
                       ∃∃K1. ⦃G1, L1, T⦄ ⊃⸮ ⦃G2, K1, U⦄ & K1 ⋕[U, 0] K2.
#G1 #G2 #L2 #K2 #T #U #H #L1 #HL12 elim(fquq_inv_gen … H) -H
[ #H elim (lleq_fqu_trans … H … HL12) -L2 /3 width=3 by fqu_fquq, ex2_intro/
| * #HG #HL #HT destruct /2 width=3 by ex2_intro/
]
qed-.
