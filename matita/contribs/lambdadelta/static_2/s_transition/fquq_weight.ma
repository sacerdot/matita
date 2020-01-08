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

include "static_2/s_transition/fqu_weight.ma".
include "static_2/s_transition/fquq.ma".

(* OPTIONAL SUPCLOSURE ******************************************************)

(* Forward lemmas with weight for closures **********************************)

lemma fquq_fwd_fw: ∀b,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ⬂⸮[b] ❪G2,L2,T2❫ →
                   ♯❨G2,L2,T2❩ ≤ ♯❨G1,L1,T1❩.
#b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -H [2: * ]
/3 width=2 by fqu_fwd_fw, lt_to_le/
qed-.
