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
include "lambda-delta/notation.ma".

(* ARITHMETICAL PROPERTIES **************************************************)

lemma plus_plus_comm_23: ∀m,n,p. m + n + p = m + p + n.
// qed.

lemma minus_le: ∀m,n. m - n ≤ m.
/2/ qed.


lemma plus_plus_minus_m_m: ∀e1,e2,d. e1 ≤ e2 → d + e1 + (e2 - e1) = d + e2.
/2/ qed.

lemma le_plus_minus_comm: ∀n,m,p. p ≤ m → (m + n) - p = (m - p) + n.
#n #m #p #lepm @plus_to_minus <associative_plus
>(commutative_plus p) <plus_minus_m_m //
qed.

lemma lt_false: ∀n. n < n → False.
#n #H lapply (lt_to_not_eq … H) -H #H elim H -H /2/
qed.

lemma arith1: ∀n,h,m,p. n + h + m ≤ p + h → n + m ≤ p.
/2/ qed.

lemma arith2: ∀j,i,e,d. d + e ≤ i → d ≤ i - e + j.
/3/ qed.

lemma arith3: ∀m,n,p. p ≤ m → m + n - (m - p + n) = p.
/3/ qed.

lemma arith4: ∀h,d,e1,e2. d ≤ e1 + e2 → d + h ≤ e1 + h + e2.
/2/ qed.
