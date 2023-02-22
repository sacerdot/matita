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

include "arithmetics/exp.ma".
include "../lambda_delta/ground_2/arith.ma".

lemma plus_inv_O3: ∀m,n. n + m = 0 → n = 0 ∧ m = 0.
#m * /2 width=1/ normalize
#n #H destruct
qed-.

lemma times_inv_S2_O3: ∀m,n. n * (S m) = 0 → n = 0.
#m #n <times_n_Sm #H
elim (plus_inv_O3 … H) -H //
qed-. 

lemma exp_n_m_plus_1: ∀n,m. n ^ (m + 1) = (n ^ m) * n.
// qed.

lemma times_n_plus_1_m: ∀n,m. (n + 1) * m = m + n * m.
#n #m >distributive_times_plus_r //
qed.

lemma lt_plus_nmn_false: ∀m,n. n + m < n → False. 
#m #n elim n -n
[ #H elim (lt_zero_false … H)
| /3 width=1/
]
qed-.

lemma not_b_divides_nbr: ∀b,r. 0 < r → r < b → 
                         ∀n,m. n * b + r = m * b → False.
#b #r #Hr #Hrb #n elim n -n
[ * normalize
  [ -Hrb #H destruct elim (lt_refl_false … Hr)
  | -Hr #m #H destruct
    elim (lt_plus_nmn_false … Hrb)
  ]
| #n #IHn * normalize
  [ -IHn -Hrb #H destruct
    elim (plus_inv_O3 … H) -H #_ #H destruct
    elim (lt_refl_false … Hr)
  | -Hr -Hrb /3 width=3/
  ]
]
qed-.
