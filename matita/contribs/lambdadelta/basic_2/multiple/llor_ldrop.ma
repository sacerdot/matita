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

include "basic_2/multiple/frees_lift.ma".
include "basic_2/multiple/llor.ma".

(* POINTWISE UNION FOR LOCAL ENVIRONMENTS ***********************************)

(* Advanced properties ******************************************************)

lemma llor_skip: ∀L1,L2,U,d. |L1| ≤ |L2| → yinj (|L1|) ≤ d → L1 ⩖[U, d] L2 ≡ L1.
#L1 #L2 #U #d #HL12 #Hd @and3_intro // -HL12
#I1 #I2 #I #K1 #K2 #K #W1 #W2 #W #i #HLK1 #_ #HLK -L2 -K2
lapply (ldrop_mono … HLK … HLK1) -HLK #H destruct
lapply (ldrop_fwd_length_lt2 … HLK1) -K1
/5 width=3 by ylt_yle_trans, ylt_inj, or3_intro0, and3_intro/
qed.

axiom llor_total: ∀L1,L2,T,d. |L1| ≤ |L2| → ∃L. L1 ⩖[T, d] L2 ≡ L.
