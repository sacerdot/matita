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

include "static_2/syntax/teq_teq.ma".
include "static_2/syntax/teq_ext.ma".

(* SYNTACTIC EQUIVALENCE ****************************************************)

(* Main properties **********************************************************)

theorem ceq_ext_trans (I):
        ∀L1,I1. L1 ⊢ I1 ≡ I → ∀L2,I2. L2 ⊢ I ≡ I2 → ∀L3. L3 ⊢ I1 ≡ I2.
#I #L1 #I1 * -I1 -I //
#I1 #V1 #V #HV1 #L2 #Z #H
elim (ext2_inv_pair_sn … H) -H #V2 #HV2 #H #L3 destruct
/3 width=3 by ext2_pair, teq_trans/
qed-.
