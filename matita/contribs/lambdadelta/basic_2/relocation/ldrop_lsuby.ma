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

include "basic_2/relocation/lsuby_lsuby.ma".
include "basic_2/relocation/ldrop.ma".

(* BASIC SLICING FOR LOCAL ENVIRONMENTS *************************************)

(* Properties on local environment refinement for extended substitution *****)

lemma dedropable_sn_TC: ∀R. dedropable_sn R → dedropable_sn (TC … R).
#R #HR #L1 #K1 #s #d #e #HLK1 #K2 #H elim H -K2
[ #K2 #HK12 elim (HR … HLK1 … HK12) -HR -K1
  /3 width=4 by inj, ex3_intro/
| #K #K2 #_ #HK2 * #L #H1L1 #HLK #H2L1 elim (HR … HLK … HK2) -HR -K
  /3 width=6 by lsuby_trans, step, ex3_intro/
]
qed-.
