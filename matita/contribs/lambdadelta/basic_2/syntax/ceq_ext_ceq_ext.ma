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

include "basic_2/syntax/lenv_ceq.ma".

(* CONTEXT-DEPENDENT SYNTACTIC EQUIVALENCE FOR BINDERS **********************)

(* Main properties **********************************************************)

theorem ceq_ext_trans: ∀L1,I1,I. ceq_ext L1 I1 I →
                       ∀L2,I2. ceq_ext L2 I I2 → ∀L3. ceq_ext L3 I1 I2. 
#L1 #I1 #I * -I1 -I //
#I1 #V1 #V #HV1 #L2 #Z #H elim (ext2_inv_pair_sn … H) -H //
qed-.
