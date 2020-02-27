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

include "ground/lib/arith.ma".

(* ARITHMETICAL PROPERTIES FOR λδ-2B ****************************************)

lemma arith_l4 (m11) (m12) (m21) (m22):
               m21+m22-(m11+m12) = m21-m11-m12+(m22-(m11-m21)-(m12-(m21-m11))).
#m11 #m12 #m21 #m22 >minus_plus
elim (le_or_ge (m11+m12) m21) #Hm1121
[ lapply (transitive_le m11 ??? Hm1121) // #Hm121
  lapply (le_plus_to_minus_l … Hm1121) #Hm12211
  <plus_minus // @eq_f2 // >(eq_minus_O m11 ?) // >(eq_minus_O m12 ?) //
| >(eq_minus_O m21 ?) // <plus_O_n <minus_plus <commutative_plus
  elim (le_or_ge m11 m21) #Hm121
  [ lapply (le_plus_to_minus_comm … Hm1121) #Hm2112
    >(eq_minus_O m11 ?) // <plus_minus_associative // <minus_le_minus_minus_comm //
  | >(eq_minus_O m21 ?) // <minus_le_minus_minus_comm //
  ]
]
qed.

lemma arith_l3 (m) (n1) (n2): n1+n2-m = n1-m+(n2-(m-n1)).
// qed.

lemma arith_l2 (n1) (n2): ↑n2-n1 = 1-n1+(n2-(n1-1)).
#n1 #n2 <arith_l3 //
qed.

lemma arith_l1: ∀x. 1 = 1-x+(x-(x-1)).
#x <arith_l2 //
qed.
