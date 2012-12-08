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

include "basics/star.ma".
include "basics/lists/lstar.ma".
include "arithmetics/exp.ma".

include "xoa_notation.ma".
include "xoa.ma".

(* logic *)

(* Note: For some reason this cannot be in the standard library *) 
interpretation "logical false" 'false = False.

notation "⊥"
  non associative with precedence 90
  for @{'false}.

(* relations *)

definition confluent1: ∀A. relation A → predicate A ≝ λA,R,a0.
                       ∀a1. R a0 a1 → ∀a2. R a0 a2 →
                       ∃∃a. R a1 a & R a2 a. 

(* Note: confluent1 would be redundant if \Pi-reduction where enabled *)                       
definition confluent: ∀A. predicate (relation A) ≝ λA,R.
                      ∀a0. confluent1 … R a0.

(* arithmetics *)

lemma lt_refl_false: ∀n. n < n → ⊥.
#n #H elim (lt_to_not_eq … H) -H /2 width=1/
qed-.

lemma lt_zero_false: ∀n. n < 0 → ⊥.
#n #H elim (lt_to_not_le … H) -H /2 width=1/
qed-.

lemma plus_lt_false: ∀m,n. m + n < m → ⊥.
#m #n #H elim (lt_to_not_le … H) -H /2 width=1/
qed-.

lemma lt_or_eq_or_gt: ∀m,n. ∨∨ m < n | n = m | n < m.
#m #n elim (lt_or_ge m n) /2 width=1/
#H elim H -m /2 width=1/
#m #Hm * #H /2 width=1/ /3 width=1/
qed-.

(* trichotomy operator *)

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

(* lists *)

(* Note: notation for nil not involving brackets *)
notation > "◊"
  non associative with precedence 90
  for @{'nil}.

definition map_cons: ∀A. A → list (list A) → list (list A) ≝ λA,a.
                     map … (cons … a).

interpretation "map_cons" 'ho_cons a l = (map_cons ? a l).

notation "hvbox(a ::: break l)"
  right associative with precedence 47
  for @{'ho_cons $a $l}.
