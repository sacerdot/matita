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

include "preamble.ma".

(* TRICHOTOMY OPERATOR ******************************************************)

(* Note: this is "if eqb n1 n2 then a2 else if leb n1 n2 then a1 else a3" *)
let rec tri (A:Type[0]) n1 n2 a1 a2 a3 on n1 : A ≝
  match n1 with 
  [ O    ⇒ match n2 with [ O ⇒ a2 | S n2 ⇒ a1 ]
  | S n1 ⇒ match n2 with [ O ⇒ a3 | S n2 ⇒ tri A n1 n2 a1 a2 a3 ]
  ].

lemma tri_lt: ∀A,a1,a2,a3,n2,n1. n1 < n2 → tri A n1 n2 a1 a2 a3 = a1.
#A #a1 #a2 #a3 #n2 elim n2 -n2
[ #n1 #H elim (lt_zero_false … H)
| #n2 #IH #n1 elim n1 -n1 // /3 width=1/
]
qed.

lemma tri_eq: ∀A,a1,a2,a3,n. tri A n n a1 a2 a3 = a2.
#A #a1 #a2 #a3 #n elim n -n normalize //
qed.

lemma tri_gt: ∀A,a1,a2,a3,n1,n2. n2 < n1 → tri A n1 n2 a1 a2 a3 = a3.
#A #a1 #a2 #a3 #n1 elim n1 -n1
[ #n2 #H elim (lt_zero_false … H)
| #n1 #IH #n2 elim n2 -n2 // /3 width=1/
]
qed.
