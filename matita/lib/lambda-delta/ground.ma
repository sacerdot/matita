(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic
    ||A||  Library of Mathematics, developed at the Computer Science
    ||T||  Department of the University of Bologna, Italy.
    ||I||
    ||T||
    ||A||  This file is distributed under the terms of the
    \   /  GNU General Public License Version 2
     \ /
      V_______________________________________________________________ *)

include "arithmetics/nat.ma".

(* ARITHMETICAL PROPERTIES **************************************************)

lemma plus_S_eq_O_false: ∀n,m. n + S m = 0 → False.
#n #m <plus_n_Sm #H destruct
qed.

lemma plus_S_le_to_pos: ∀n,m,p. n + S m ≤ p → 0 < p.
#n #m #p <plus_n_Sm #H @(lt_to_le_to_lt … H) //
qed.

lemma minus_le: ∀m,n. m - n ≤ m.
/2/ qed.

lemma le_O_to_eq_O: ∀n. n ≤ 0 → n = 0.
/2/ qed.

lemma lt_to_le: ∀a,b. a < b → a ≤ b.
/2/ qed.

lemma lt_refl_false: ∀n. n < n → False.
#n #H elim (lt_to_not_eq … H) -H /2/
qed.

lemma lt_zero_false: ∀n. n < 0 → False.
#n #H elim (lt_to_not_le … H) -H /2/
qed.

lemma lt_or_ge: ∀m,n. m < n ∨ n ≤ m.
#m #n elim (decidable_lt m n) /3/
qed.

lemma le_to_lt_or_eq: ∀m,n. m ≤ n → m < n ∨ m = n.
#m #n * -n /3/
qed. 

lemma plus_le_weak: ∀m,n,p. m + n ≤ p → n ≤ p.
/2/ qed.

lemma plus_lt_false: ∀m,n. m + n < m → False.
#m #n #H1 lapply (le_plus_n_r n m) #H2
lapply (le_to_lt_to_lt … H2 H1) -H2 H1 #H
elim (lt_refl_false … H)
qed.

lemma monotonic_lt_minus_l: ∀p,q,n. n ≤ q → q < p → q - n < p - n.
#p #q #n #H1 #H2
@lt_plus_to_minus_r <plus_minus_m_m //.
qed.

lemma plus_le_minus: ∀a,b,c. a + b ≤ c → a ≤ c - b.
/2/ qed.

lemma lt_plus_minus: ∀i,u,d. u ≤ i → i < d + u → i - u < d.
/2/ qed.

lemma plus_plus_comm_23: ∀m,n,p. m + n + p = m + p + n.
// qed.

lemma le_plus_minus_comm: ∀n,m,p. p ≤ m → m + n - p = m - p + n.
#n #m #p #lepm @plus_to_minus <associative_plus
>(commutative_plus p) <plus_minus_m_m //
qed.

lemma minus_le_minus_minus_comm: ∀m,p,n. 
                                 p ≤ m → m - p ≤ n → n + p - m = n - (m - p).
#m elim m -m
[ #p #n #H >(le_O_to_eq_O … H) -H //
| #m #IHm #p elim p -p //
  #p #_ #n #Hpm <plus_n_Sm @IHm /2/
]
qed.

lemma minus_plus_comm: ∀a,b,c. a - b - c = a - (c + b).
// qed.

lemma minus_minus_comm: ∀a,b,c. a - b - c = a - c - b.
/3/ qed.

lemma le_plus_minus: ∀a,b,c. c ≤ b → a + b - c = a + (b - c).
/2/ qed.

lemma plus_minus_m_m_comm: ∀n,m. m ≤ n → n = m + (n - m).
/2/ qed.

theorem minus_plus_m_m_comm: ∀n,m. n = (m + n) - m.
/2/ qed.

lemma arith_a2: ∀a,c1,c2. c1 + c2 ≤ a → a - c1 - c2 + (c1 + c2) = a.
/2/ qed.

lemma arith_b1: ∀a,b,c1. c1 ≤ b → a - c1 - (b - c1) = a - b.
#a #b #c1 #H >minus_plus @eq_f2 /2/
qed.

lemma arith_b2: ∀a,b,c1,c2. c1 + c2 ≤ b → a - c1 - c2 - (b - c1 - c2) = a - b.
#a #b #c1 #c2 #H >minus_plus >minus_plus >minus_plus /2/
qed.

lemma arith_c1: ∀a,b,c1. a + c1 - (b + c1) = a - b.
// qed.

lemma arith_c1x: ∀x,a,b,c1. x + c1 + a - (b + c1) = x + a - b.
#x #a #b #c1 >plus_plus_comm_23 //
qed.

lemma arith_d1: ∀a,b,c1. c1 ≤ b → a + c1 + (b - c1) = a + b.
/2/ qed.

lemma arith_e2: ∀a,c1,c2. a ≤ c1 → c1 + c2 - (c1 - a + c2) = a.
/3/ qed.

lemma arith_f1: ∀a,b,c1. a + b ≤ c1 → c1 - (c1 - a - b) = a + b.
#a #b #c1 #H >minus_plus <minus_minus //
qed.

lemma arith_g1: ∀a,b,c1. c1 ≤ b → a - (b - c1) - c1 = a - b.
/2/ qed.

lemma arith_h1: ∀a1,a2,b,c1. c1 ≤ a1 → c1 ≤ b →
                a1 - c1 + a2 - (b - c1) = a1 + a2 - b.
#a1 #a2 #b #c1 #H1 #H2 <le_plus_minus_comm /2/
qed.

lemma arith_z1: ∀a,b,c1. a + c1 - b - c1 = a - b.
// qed.

(* unstable *****************************************************************)

lemma arith1: ∀n,h,m,p. n + h + m ≤ p + h → n + m ≤ p.
/2/ qed.

lemma arith2: ∀j,i,e,d. d + e ≤ i → d ≤ i - e + j.
#j #i #e #d #H lapply (plus_le_minus … H) -H /2/
qed.

lemma arith3: ∀a1,a2,b,c1. a1 + a2 ≤ b → a1 + c1 + a2 ≤ b + c1.
/2/ qed.

lemma arith4: ∀h,d,e1,e2. d ≤ e1 + e2 → d + h ≤ e1 + h + e2.
/2/ qed.

lemma arith5: ∀a,b1,b2,c1. c1 ≤ b1 → c1 ≤ a → a < b1 + b2 → a - c1 < b1 - c1 + b2.
#a #b1 #b2 #c1 #H1 #H2 #H3
<le_plus_minus_comm // @monotonic_lt_minus_l //
qed.

lemma arith8: ∀a,b. a < a + b + 1.
// qed.

lemma arith9: ∀a,b,c. c < a + (b + c + 1) + 1.
// qed.

lemma arith10: ∀a,b,c,d,e. a ≤ b → c + (a - d - e) ≤ c + (b - d - e).
#a #b #c #d #e #H
>minus_plus >minus_plus @monotonic_le_plus_r @monotonic_le_minus_l //
qed.
