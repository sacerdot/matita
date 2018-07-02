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

include "static_2/s_transition/fqu_length.ma".
include "static_2/s_transition/fquq.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* Forward lemmas with length for local environments ************************)

lemma fquq_fwd_length_lref1: ∀b,G1,G2,L1,L2,T2,i. ⦃G1, L1, #i⦄ ⊐⸮[b] ⦃G2, L2, T2⦄ →
                             |L2| ≤ |L1|.
#b #G1 #G2 #L1 #L2 #T2 #i #H elim H -H [2: * ]
/3 width=6 by fqu_fwd_length_lref1, lt_to_le/
qed-.
