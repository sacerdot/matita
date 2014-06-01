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

include "basic_2/substitution/lsuby.ma".

(* LOCAL ENVIRONMENT REFINEMENT FOR EXTENDED SUBSTITUTION *******************)

(* Main properties **********************************************************)

theorem lsuby_trans: ∀d,e. Transitive … (lsuby d e).
#d #e #L1 #L2 #H elim H -L1 -L2 -d -e
[ #L1 #d #e #X #H lapply (lsuby_inv_atom1 … H) -H
  #H destruct //
| #I1 #I2 #L1 #L #V1 #V #_ #IHL1 #X #H elim (lsuby_inv_zero1 … H) -H //
  * #I2 #L2 #V2 #HL2 #H destruct /3 width=1 by lsuby_zero/
| #I1 #I2 #L1 #L2 #V #e #_ #IHL1 #X #H elim (lsuby_inv_pair1 … H) -H //
  * #I2 #L2 #HL2 #H destruct /3 width=1 by lsuby_pair/
| #I1 #I2 #L1 #L2 #V1 #V2 #d #e #_ #IHL1 #X #H elim (lsuby_inv_succ1 … H) -H //
  * #I2 #L2 #V2 #HL2 #H destruct /3 width=1 by lsuby_succ/
]
qed-.
