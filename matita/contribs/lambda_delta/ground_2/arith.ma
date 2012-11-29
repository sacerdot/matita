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

include "arithmetics/nat.ma".
include "ground_2/star.ma".

(* ARITHMETICAL PROPERTIES **************************************************)

(* Equations ****************************************************************)

lemma plus_n_2: ∀n. n + 2 = n + 1 + 1.
// qed.

lemma le_plus_minus: ∀m,n,p. p ≤ n → m + n - p = m + (n - p).
/2 by plus_minus/ qed.

lemma le_plus_minus_comm: ∀n,m,p. p ≤ m → m + n - p = m - p + n.
/2 by plus_minus/ qed.

lemma arith_b1: ∀a,b,c1. c1 ≤ b → a - c1 - (b - c1) = a - b.
#a #b #c1 #H >minus_minus_comm >minus_le_minus_minus_comm //
qed.

lemma arith_b2: ∀a,b,c1,c2. c1 + c2 ≤ b → a - c1 - c2 - (b - c1 - c2) = a - b.
#a #b #c1 #c2 #H >minus_plus >minus_plus >minus_plus /2 width=1/
qed.

lemma arith_c1x: ∀x,a,b,c1. x + c1 + a - (b + c1) = x + a - b.
/3 by monotonic_le_minus_l, le_to_le_to_eq, le_n/ qed.

lemma arith_h1: ∀a1,a2,b,c1. c1 ≤ a1 → c1 ≤ b →
                a1 - c1 + a2 - (b - c1) = a1 + a2 - b.
#a1 #a2 #b #c1 #H1 #H2 >plus_minus // /2 width=1/
qed.

(* Inversion & forward lemmas ***********************************************)

axiom eq_nat_dec: ∀n1,n2:nat. Decidable (n1 = n2).

axiom lt_dec: ∀n1,n2. Decidable (n1 < n2).

lemma lt_or_eq_or_gt: ∀m,n. ∨∨ m < n | n = m | n < m.
#m #n elim (lt_or_ge m n) /2 width=1/
#H elim H -m /2 width=1/
#m #Hm * #H /2 width=1/ /3 width=1/
qed-.

lemma lt_refl_false: ∀n. n < n → ⊥.
#n #H elim (lt_to_not_eq … H) -H /2 width=1/
qed-.

lemma lt_zero_false: ∀n. n < 0 → ⊥.
#n #H elim (lt_to_not_le … H) -H /2 width=1/
qed-.

lemma false_lt_to_le: ∀x,y. (x < y → ⊥) → y ≤ x.
#x #y #H elim (decidable_lt x y) /2 width=1/
#Hxy elim (H Hxy)
qed-.

lemma le_plus_xySz_x_false: ∀y,z,x. x + y + S z ≤ x → ⊥.
#y #z #x elim x -x
[ #H lapply (le_n_O_to_eq … H) -H
  <plus_n_Sm #H destruct
| /3 width=1 by le_S_S_to_le/
]
qed-.

lemma plus_xySz_x_false: ∀z,x,y. x + y + S z = x → ⊥.
/2 width=4 by le_plus_xySz_x_false/ qed-.

(* Iterators ****************************************************************)

(* Note: see also: lib/arithemetcs/bigops.ma *)
let rec iter (n:nat) (B:Type[0]) (op: B → B) (nil: B) ≝
  match n with
   [ O   ⇒ nil
   | S k ⇒ op (iter k B op nil)
   ].

interpretation "iterated function" 'exp op n = (iter n ? op).

lemma iter_SO: ∀B:Type[0]. ∀f:B→B. ∀b,l. f^(l+1) b = f (f^l b).
#B #f #b #l >commutative_plus //
qed.

lemma iter_n_Sm: ∀B:Type[0]. ∀f:B→B. ∀b,l. f^l (f b) = f (f^l b).
#B #f #b #l elim l -l normalize //
qed.

(* Trichotomy operator ******************************************************)

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
