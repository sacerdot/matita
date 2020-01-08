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

include "static_2/syntax/lenv_length.ma".
include "static_2/s_transition/fqu.ma".

(* SUPCLOSURE ***************************************************************)

(* Forward lemmas with length for local environments ************************)

fact fqu_fwd_length_lref1_aux: ∀b,G1,G2,L1,L2,T1,T2. ❪G1,L1,T1❫ ⬂[b] ❪G2,L2,T2❫ →
                               ∀i. T1 = #i → |L2| < |L1|.
#b #G1 #G2 #L1 #L2 #T1 #T2 #H elim H -G1 -G2 -L1 -L2 -T1 -T2 // [2,3: #p]
#I #G #L #V #T [1,2: #_ ] #j #H destruct
qed-.

lemma fqu_fwd_length_lref1: ∀b,G1,G2,L1,L2,T2,i. ❪G1,L1,#i❫ ⬂[b] ❪G2,L2,T2❫ →
                            |L2| < |L1|.
/2 width=8 by fqu_fwd_length_lref1_aux/
qed-.
