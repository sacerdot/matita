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
include "Ground_2/star.ma".

(* ARITHMETICAL PROPERTIES **************************************************)

(* equations ****************************************************************)

lemma plus_plus_comm_23: ∀x,y,z. x + y + z = x + z + y.
// qed.

lemma le_plus_minus: ∀m,n,p. p ≤ n → m + n - p = m + (n - p).
/2 by plus_minus/ qed.

lemma le_plus_minus_comm: ∀n,m,p. p ≤ m → m + n - p = m - p + n.
/2 by plus_minus/ qed.

lemma minus_minus_comm: ∀a,b,c. a - b - c = a - c - b.
 /3 by monotonic_le_minus_l, le_to_le_to_eq/ qed.

lemma minus_le_minus_minus_comm: ∀b,c,a. c ≤ b → a - (b - c) = a + c - b.
#b elim b -b
[ #c #a #H >(le_n_O_to_eq … H) -H //
| #b #IHb #c elim c -c //
  #c #_ #a #Hcb
  lapply (le_S_S_to_le … Hcb) -Hcb #Hcb
  <plus_n_Sm normalize /2 width=1/
]
qed.

lemma arith_b1: ∀a,b,c1. c1 ≤ b → a - c1 - (b - c1) = a - b.
#a #b #c1 #H >minus_plus /3 width=1/
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

(* inversion & forward lemmas ***********************************************)

axiom eq_nat_dec: ∀n1,n2:nat. Decidable (n1 = n2).

axiom lt_dec: ∀n1,n2. Decidable (n1 < n2).

lemma lt_or_ge: ∀m,n. m < n ∨ n ≤ m.
#m #n elim (decidable_lt m n) /2 width=1/ /3 width=1/
qed-.

lemma lt_or_eq_or_gt: ∀m,n. ∨∨ m < n | n = m | n < m.
#m elim m -m
[ * /2 width=1/
| #m #IHm * /2 width=1/
  #n elim (IHm n) -IHm #H 
  [ @or3_intro0 | @or3_intro1 destruct | @or3_intro2 ] // /2 width=1/ (**) (* /3 width=1/ is slow *)
qed-.

lemma le_inv_plus_plus_r: ∀x,y,z. x + z ≤ y + z → x ≤ y.
/2 by le_plus_to_le/ qed-.

lemma le_inv_plus_l: ∀x,y,z. x + y ≤ z → x ≤ z - y ∧ y ≤ z.
/3 width=2/ qed-.

lemma lt_refl_false: ∀n. n < n → False.
#n #H elim (lt_to_not_eq … H) -H /2 width=1/
qed-.

lemma lt_zero_false: ∀n. n < 0 → False.
#n #H elim (lt_to_not_le … H) -H /2 width=1/
qed-.

lemma plus_S_eq_O_false: ∀n,m. n + S m = 0 → False.
#n #m <plus_n_Sm #H destruct
qed-.

lemma plus_lt_false: ∀m,n. m + n < m → False.
#m #n #H1 lapply (le_plus_n_r n m) #H2
lapply (le_to_lt_to_lt … H2 H1) -H2 -H1 #H
elim (lt_refl_false … H)
qed-.

lemma false_lt_to_le: ∀x,y. (x < y → False) → y ≤ x.
#x #y #H elim (decidable_lt x y) /2 width=1/
#Hxy elim (H Hxy)
qed-.

lemma le_fwd_plus_plus_ge: ∀m1,m2. m2 ≤ m1 → ∀n1,n2. m1 + n1 ≤ m2 + n2 → n1 ≤ n2.
#m1 #m2 #H elim H -m1
[ /2 width=2/
| #m1 #_ #IHm1 #n1 #n2 #H @IHm1 /2 width=3/
]
qed-.
