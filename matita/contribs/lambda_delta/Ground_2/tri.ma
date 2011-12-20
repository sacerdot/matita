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

include "Ground_2/arith.ma".

(* TRICOTOMY FUNCTION *******************************************************)

let rec tri (A:Type[0]) m n a b c on m : A ≝
  match m with 
  [ O   ⇒ match n with [ O ⇒ b | S n ⇒ a ]
  | S m ⇒ match n with [ O ⇒ c | S n ⇒ tri A m n a b c ]
  ]. 

(* Basic properties *********************************************************)

lemma tri_lt: ∀A,a,b,c,n,m. m < n → tri A m n a b c = a.
#A #a #b #c #n elim n -n
[ #m #H elim (lt_zero_false … H)
| #n #IH #m elim m -m // /3 width=1/
]
qed.

lemma tri_eq: ∀A,a,b,c,m. tri A m m a b c = b.
#A #a #b #c #m elim m -m normalize //
qed.

lemma tri_gt: ∀A,a,b,c,m,n. n < m → tri A m n a b c = c.
#A #a #b #c #m elim m -m
[ #n #H elim (lt_zero_false … H)
| #m #IH #n elim n -n // /3 width=1/
]
qed.

