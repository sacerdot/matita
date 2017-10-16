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

include "basic_2/syntax/ext2.ma".

(* EXTENSION TO BINDERS OF A RELATION FOR TERMS *****************************)

(* Main properties **********************************************************)

theorem ext2_trans: ∀R. Transitive … R → Transitive … (ext2 R).
#R #HR #I1 #I #H elim H -I1 -I
[ #I1 #J #H >(ext2_inv_unit_sn … H) -J /2 width=1 by ext2_unit/
| #I1 #V1 #V #HV1 #J #H elim (ext2_inv_pair_sn … H) -H 
  #V2 #HV2 #H destruct /3 width=3 by ext2_pair/
]
qed-.
