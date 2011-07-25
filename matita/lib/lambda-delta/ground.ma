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

include "basics/list.ma".
include "lambda-delta/xoa_defs.ma".
include "lambda-delta/xoa_notation.ma".

(* ARITHMETICAL PROPERTIES **************************************************)

lemma plus_plus_comm_23: ∀m,n,p. m + n + p = m + p + n.
// qed.

lemma minus_plus_comm: ∀a,b,c. a - b - c = a - (c + b).
// qed.

lemma arith8: ∀a,b. a < a + b + 1.
// qed.

lemma arith9: ∀a,b,c. c < a + (b + c + 1) + 1.
// qed.

lemma minus_le: ∀m,n. m - n ≤ m.
/2/ qed.

lemma plus_plus_minus_m_m: ∀e1,e2,d. e1 ≤ e2 → d + e1 + (e2 - e1) = d + e2.
/2/ qed.

lemma le_O_to_eq_O: ∀n. n ≤ 0 → n = 0.
/2/ qed.

lemma plus_le_minus: ∀a,b,c. a + b ≤ c → a ≤ c - b.
/2/ qed.

lemma le_plus_minus_comm: ∀n,m,p. p ≤ m → (m + n) - p = (m - p) + n.
#n #m #p #lepm @plus_to_minus <associative_plus
>(commutative_plus p) <plus_minus_m_m //
qed.

lemma le_plus_minus: ∀a,b,c. c ≤ b → a + b - c = a + (b - c).
/2/ qed.

lemma minus_le_minus_minus_comm: ∀m,p,n. 
                                 p ≤ m → m - p ≤ n → n + p - m = n - (m - p).
#m elim m -m
[ #p #n #H >(le_O_to_eq_O … H) -H //
| #m #IHm #p elim p -p //
  #p #_ #n #Hpm <plus_n_Sm @IHm /2/
]
qed.

lemma lt_refl_false: ∀n. n < n → False.
#n #H elim (lt_to_not_eq … H) -H /2/
qed.

lemma lt_zero_false: ∀n. n < 0 → False.
#n #H elim (lt_to_not_le … H) -H /2/
qed.

lemma lt_or_ge: ∀m,n. m < n ∨ n ≤ m.
#m #n elim (decidable_lt m n) /3/
qed.

lemma plus_lt_false: ∀m,n. m + n < m → False.
#m #n #H1 lapply (le_plus_n_r n m) #H2
lapply (le_to_lt_to_lt … H2 H1) -H2 H1 #H
elim (lt_refl_false … H)
qed.

lemma plus_S_eq_O_false: ∀n,m. n + S m = 0 → False.
#n #m <plus_n_Sm #H destruct
qed. 

lemma minus_minus_comm: ∀a,b,c. a - b - c = a - c - b.
/3/ qed.

lemma arith1: ∀n,h,m,p. n + h + m ≤ p + h → n + m ≤ p.
/2/ qed.

lemma arith6: ∀m,n. m < n → n - (n - m - 1) = m + 1.
#m #n #H >minus_plus <minus_minus //
qed.

lemma arith4: ∀h,d,e1,e2. d ≤ e1 + e2 → d + h ≤ e1 + h + e2.
/2/ qed.

lemma arith5: ∀i,h,d. i + h ≤ d → d - i - h + (i + h) = d.
/2/ qed.

lemma arith7: ∀i,d. i ≤ d → d - i + i = d.
/2/ qed.

lemma arith2: ∀j,i,e,d. d + e ≤ i → d ≤ i - e + j.
/3/ qed.

lemma arith3: ∀m,n,p. p ≤ m → m + n - (m - p + n) = p.
/3/ qed.

