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

include "ground/lib/relations.ma".
include "ground/notation/xoa/sum_2.ma".

(* TYPES ********************************************************************)

inductive sum_2 (A1,A2:Type[0]): Type[0] ≝
| in_1_2: A1 → sum_2 A1 A2
| in_2_2: A2 → sum_2 A1 A2
.

interpretation
  "multiple sum (2)"
  'Sum A1 A2 = (sum_2 A1 A2).

(* Basic constructions ******************************************************)

lemma eq_sum_2_dec (A1,A2:Type[0]):
      (∀a1,a2. Decidable (a1 ={A1} a2)) →
      (∀a1,a2. Decidable (a1 ={A2} a2)) →
      ∀a1,a2. Decidable (a1 ={++A1|A2} a2).
#A1 #A2 #HA1 #HA2 * #a1 * #a2
[ elim (HA1 a1 a2) -HA1 -HA2 #Hna destruct
  [ /2 width=1 by or_introl/]
|4: elim (HA2 a1 a2) -HA1 -HA2 #Hna destruct
  [ /2 width=1 by or_introl/]
]
@or_intror
#H0 destruct
/2 width=1 by/
qed-.
