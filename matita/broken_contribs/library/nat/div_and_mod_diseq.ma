(**************************************************************************)
(*       ___	                                                          *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "nat/lt_arith.ma".

(* the proof that 
     n \mod m < m, 
   called lt_mod_m_m, is in div_and_mod.
Other inequalities are also in lt_arith.ma.  
*)

theorem lt_div_S: \forall n,m. O < m \to 
n < S(n / m)*m.
intros.
change with (n < m +(n/m)*m).
rewrite > sym_plus.
rewrite > (div_mod n m H) in ⊢ (? % ?).
apply lt_plus_r.
apply lt_mod_m_m.
assumption.
qed.

theorem le_div: \forall n,m. O < n \to m/n \le m.
intros.
rewrite > (div_mod m n) in \vdash (? ? %)
  [apply (trans_le ? (m/n*n))
    [rewrite > times_n_SO in \vdash (? % ?).
     apply le_times
      [apply le_n|assumption]
    |apply le_plus_n_r
    ]
  |assumption
  ]
qed.

theorem le_plus_mod: \forall m,n,q. O < q \to
(m+n) \mod q \le m \mod q + n \mod q .
intros.
elim (decidable_le q (m \mod q + n \mod q))
  [apply not_lt_to_le.intro.
   apply (le_to_not_lt q q)
    [apply le_n
    |apply (le_to_lt_to_lt ? (m\mod q+n\mod q))
      [assumption
      |apply (trans_lt ? ((m+n)\mod q))
        [assumption
        |apply lt_mod_m_m.assumption
        ]
      ]
    ]
  |cut ((m+n)\mod q = m\mod q+n\mod q)
    [rewrite < Hcut.apply le_n
    |apply (div_mod_spec_to_eq2 (m+n) q ((m+n)/q) ((m+n) \mod q) (m/q + n/q))
      [apply div_mod_spec_div_mod.
       assumption
      |apply div_mod_spec_intro
        [apply not_le_to_lt.assumption
        |rewrite > (div_mod n q H) in ⊢ (? ? (? ? %) ?).
         rewrite < assoc_plus.
         rewrite < assoc_plus in ⊢ (? ? ? %).
         apply eq_f2
          [rewrite > (div_mod m q) in ⊢ (? ? (? % ?) ?)
            [rewrite > sym_times in ⊢ (? ? ? (? % ?)).
             rewrite > distr_times_plus.
             rewrite > sym_times in ⊢ (? ? ? (? (? % ?) ?)).
             rewrite > assoc_plus.
             rewrite > assoc_plus in ⊢ (? ? ? %).
             apply eq_f.
             rewrite > sym_plus.
             rewrite > sym_times.
             reflexivity
            |assumption
            ]
          |reflexivity
          ]
        ]
      ]
    ]
  ]
qed.

theorem le_plus_div: \forall m,n,q. O < q \to
m/q + n/q \le (m+n)/q.
intros.
apply (le_times_to_le q)
  [assumption
  |rewrite > distr_times_plus.
   rewrite > sym_times.
   rewrite > sym_times in ⊢ (? (? ? %) ?).
   rewrite > sym_times in ⊢ (? ? %).
   apply (le_plus_to_le ((m+n) \mod q)).
   rewrite > sym_plus in ⊢ (? ? %).
   rewrite < (div_mod ? ? H).
   rewrite > (div_mod n q H) in ⊢ (? ? (? ? %)).
   rewrite < assoc_plus.
   rewrite > sym_plus in ⊢ (? ? (? ? %)).
   rewrite < assoc_plus in ⊢ (? ? %).
   apply le_plus_l.
   rewrite > (div_mod m q H) in ⊢ (? ? (? % ?)).
   rewrite > assoc_plus.
   rewrite > sym_plus.
   apply le_plus_r.
   apply le_plus_mod.
   assumption
  ]
qed.

theorem le_times_to_le_div: \forall a,b,c:nat.
O \lt b \to (b*c) \le a \to c \le (a /b).
intros.
apply lt_S_to_le.
apply (lt_times_n_to_lt b)
  [assumption
  |rewrite > sym_times.
   apply (le_to_lt_to_lt ? a)
    [assumption
    |simplify.
     rewrite > sym_plus.
     rewrite > (div_mod a b) in ⊢ (? % ?)
      [apply lt_plus_r.
       apply lt_mod_m_m.
       assumption
      |assumption
      ]
    ]
  ]
qed.

theorem le_times_to_le_div2: \forall m,n,q. O < q \to 
n \le m*q \to n/q \le m.
intros.
apply (le_times_to_le q ? ? H).
rewrite > sym_times.
rewrite > sym_times in ⊢ (? ? %).
apply (le_plus_to_le (n \mod q)).
rewrite > sym_plus.
rewrite < div_mod
  [apply (trans_le ? (m*q))
    [assumption
    |apply le_plus_n
    ]
  |assumption
  ]
qed.

(* da spostare *)
theorem lt_m_nm: \forall n,m. O < m \to S O < n \to 
m < n*m.
intros.
elim H1
  [simplify.rewrite < plus_n_O.
   rewrite > plus_n_O in ⊢ (? % ?).
   apply lt_plus_r.assumption
  |simplify.
   rewrite > plus_n_O in ⊢ (? % ?).
   rewrite > sym_plus.
   apply lt_plus
    [assumption
    |assumption
    ]
  ]
qed.

theorem lt_times_to_lt: \forall i,n,m. O < i \to
i * n < i * m \to n < m.
intros.
apply not_le_to_lt.intro.
apply (lt_to_not_le ? ? H1).
apply le_times_r.
assumption.
qed.
   
theorem lt_times_to_lt_div: \forall m,n,q. n < m*q \to n/q < m.
intros.
apply (lt_times_to_lt q ? ? (lt_times_to_lt_O ? ? ? H)).
rewrite > sym_times.
rewrite > sym_times in ⊢ (? ? %).
apply (le_plus_to_le (n \mod q)).
rewrite < plus_n_Sm. 
rewrite > sym_plus.
rewrite < div_mod
  [apply (trans_le ? (m*q))
    [assumption
    |apply le_plus_n
    ]
  |apply (lt_times_to_lt_O ? ? ? H)
  ]
qed.

theorem lt_div: \forall n,m. O < m \to S O < n \to m/n < m.
intros.
apply lt_times_to_lt_div.
rewrite < sym_times.
apply lt_m_nm;assumption.
qed. 
  
theorem le_div_plus_S: \forall m,n,q. O < q \to
(m+n)/q \le S(m/q + n/q).
intros.
apply le_S_S_to_le.
apply lt_times_to_lt_div.
change in ⊢ (? ? %) with (q + (q + (m/q+n/q)*q)).
rewrite > sym_times.
rewrite > distr_times_plus.
rewrite > sym_times.
rewrite < assoc_plus in ⊢ (? ? (? ? %)).
rewrite < assoc_plus.
rewrite > sym_plus in ⊢ (? ? (? % ?)).
rewrite > assoc_plus.
apply lt_plus
  [change with (m < S(m/q)*q).
   apply lt_div_S.
   assumption
  |rewrite > sym_times.
   change with (n < S(n/q)*q).
   apply lt_div_S.
   assumption
  ]
qed.

theorem le_div_S_S_div: \forall n,m. O < m \to
(S n)/m \le S (n /m).
intros.
apply le_times_to_le_div2
  [assumption
  |simplify.
   rewrite > (div_mod n m H) in ⊢ (? (? %) ?).
   rewrite > plus_n_Sm.
   rewrite > sym_plus.
   apply le_plus_l.
   apply lt_mod_m_m.
   assumption.
  ]
qed.

theorem le_times_div_div_times: \forall a,n,m.O < m \to 
a*(n/m) \le a*n/m. 
intros.
apply le_times_to_le_div
  [assumption
  |rewrite > sym_times.
   rewrite > assoc_times.
   apply le_times_r.
   rewrite > (div_mod n m H) in ⊢ (? ? %).
   apply le_plus_n_r.
  ]
qed.

theorem monotonic_div: \forall n.O < n \to
monotonic nat le (\lambda m.div m n).
unfold monotonic.simplify.intros.
apply le_times_to_le_div
  [assumption
  |apply (trans_le ? x)
    [rewrite > sym_times.
     rewrite > (div_mod x n H) in ⊢ (? ? %).
     apply le_plus_n_r
    |assumption
    ]
  ]
qed.
 
theorem le_div_times_m: \forall a,i,m. O < i \to O < m \to
(a * (m / i)) / m \le a / i.
intros.
apply (trans_le ? ((a*m/i)/m))
  [apply monotonic_div
    [assumption
    |apply le_times_div_div_times.
     assumption
    ]
  |rewrite > eq_div_div_div_times
    [rewrite > sym_times in ⊢ (? (? ? %) ?).
     rewrite < eq_div_div_div_times
      [apply monotonic_div
        [assumption
        |rewrite > lt_O_to_div_times
          [apply le_n
          |assumption
          ]
        ]
      |assumption
      |assumption
      ]
    |assumption
    |assumption
    ]
  ]
qed.
       
theorem le_div_times_Sm: \forall a,i,m. O < i \to O < m \to
a / i \le (a * S (m / i))/m.
intros.
apply (trans_le ? ((a * S (m / i))/((S (m/i))*i)))
  [rewrite < (eq_div_div_div_times ? i)
    [rewrite > lt_O_to_div_times
      [apply le_n
      |apply lt_O_S
      ]
    |apply lt_O_S
    |assumption
    ]
  |apply le_times_to_le_div
    [assumption
    |apply (trans_le ? (m*(a*S (m/i))/(S (m/i)*i)))
      [apply le_times_div_div_times.
       rewrite > (times_n_O O).
       apply lt_times
        [apply lt_O_S
        |assumption
        ]
      |rewrite > sym_times.
       apply le_times_to_le_div2
        [rewrite > (times_n_O O).
         apply lt_times
          [apply lt_O_S
          |assumption
          ]
        |apply le_times_r.
         apply lt_to_le.
         apply lt_div_S.
         assumption
        ]
      ]
    ]
  ]
qed.

