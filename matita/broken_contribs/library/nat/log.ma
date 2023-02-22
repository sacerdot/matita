(**************************************************************************)
(*       ___	                                                            *)
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

include "datatypes/constructors.ma".
include "nat/minimization.ma".
include "nat/relevant_equations.ma".
include "nat/primes.ma".
include "nat/iteration2.ma".
include "nat/div_and_mod_diseq.ma".

definition log \def \lambda p,n.
max n (\lambda x.leb (exp p x) n).

theorem le_exp_log: \forall p,n. O < n \to
exp p (log p n) \le n.
intros.
apply leb_true_to_le.
unfold log.
apply (f_max_true (\lambda x.leb (exp p x) n)).
apply (ex_intro ? ? O).
split
  [apply le_O_n
  |apply le_to_leb_true.simplify.assumption
  ]
qed.

theorem log_SO: \forall n. S O < n \to log n (S O) = O.
intros.
apply sym_eq.apply le_n_O_to_eq.
apply (le_exp_to_le n)
  [assumption
  |simplify in ⊢ (? ? %).
   apply le_exp_log.
   apply le_n
  ]
qed.

theorem lt_to_log_O: \forall n,m. O < m \to m < n \to log n m = O.
intros.
apply sym_eq.apply le_n_O_to_eq.
apply le_S_S_to_le.
apply (lt_exp_to_lt n)
  [apply (le_to_lt_to_lt ? m);assumption
  |simplify in ⊢ (? ? %).
   rewrite < times_n_SO.
   apply (le_to_lt_to_lt ? m)
    [apply le_exp_log.assumption
    |assumption
    ]
  ]
qed.

theorem lt_log_n_n: \forall p, n. S O < p \to O < n \to log p n < n.
intros.
cut (log p n \le n)
  [elim (le_to_or_lt_eq ? ? Hcut)
    [assumption
    |absurd (exp p n \le n)
      [rewrite < H2 in ⊢ (? (? ? %) ?).
       apply le_exp_log.
       assumption
      |apply lt_to_not_le.
       apply lt_m_exp_nm.
       assumption
      ]
    ]
  |unfold log.apply le_max_n
  ]
qed.

theorem lt_O_log: \forall p,n. O < n \to p \le n \to O < log p n.
intros.
unfold log.
apply not_lt_to_le.
intro.
apply (leb_false_to_not_le ? ? ? H1).
rewrite > (exp_n_SO p).
apply (lt_max_to_false ? ? ? H2).
assumption.
qed.

theorem le_log_n_n: \forall p,n. S O < p \to log p n \le n.
intros.
cases n
  [apply le_n
  |apply lt_to_le.
   apply lt_log_n_n
    [assumption|apply lt_O_S]
  ]
qed.

theorem lt_exp_log: \forall p,n. S O < p \to n < exp p (S (log p n)).
intros.cases n
  [simplify.rewrite < times_n_SO.apply lt_to_le.assumption
  |apply not_le_to_lt.
   apply leb_false_to_not_le.
   apply (lt_max_to_false ? (S n1) (S (log p (S n1))))
    [apply le_S_S.apply le_n
    |apply lt_log_n_n
      [assumption|apply lt_O_S]
    ]
  ]
qed.

theorem log_times1: \forall p,n,m. S O < p \to O < n \to O < m \to
log p (n*m) \le S(log p n+log p m).
intros.
unfold in ⊢ (? (% ? ?) ?).
apply f_false_to_le_max
  [apply (ex_intro ? ? O).
   split
    [apply le_O_n
    |apply le_to_leb_true.
     simplify.
     rewrite > times_n_SO.
     apply le_times;assumption
    ]
  |intros.
   apply lt_to_leb_false.
   apply (lt_to_le_to_lt ? ((exp p (S(log p n)))*(exp p (S(log p m)))))
    [apply lt_times;apply lt_exp_log;assumption
    |rewrite < exp_plus_times.
     apply le_exp
      [apply lt_to_le.assumption
      |simplify.
       rewrite < plus_n_Sm.
       assumption
      ]
    ]
  ]
qed.
  
theorem log_times: \forall p,n,m.S O < p \to log p (n*m) \le S(log p n+log p m).
intros.
cases n
  [apply le_O_n
  |cases m
    [rewrite < times_n_O.
     apply le_O_n
    |apply log_times1
      [assumption
      |apply lt_O_S
      |apply lt_O_S
      ]
    ]
  ]
qed.

theorem log_times_l: \forall p,n,m.O < n \to O < m \to S O < p \to 
log p n+log p m \le log p (n*m) .
intros.
unfold log in ⊢ (? ? (% ? ?)).
apply f_m_to_le_max
  [elim H
    [rewrite > log_SO
      [simplify.
       rewrite < plus_n_O.
       apply le_log_n_n.
       assumption
      |assumption
      ]
    |elim H1
      [rewrite > log_SO
        [rewrite < plus_n_O.
         rewrite < times_n_SO.
         apply le_log_n_n.
         assumption
        |assumption
        ]
      |apply (trans_le ? (S n1 + S n2))
        [apply le_plus;apply le_log_n_n;assumption
        |simplify.
         apply le_S_S.
         rewrite < plus_n_Sm.
         change in ⊢ (? % ?) with ((S n1)+n2).
         rewrite > sym_plus.
         apply le_plus_r.
         change with (n1 < n1*S n2).
         rewrite > times_n_SO in ⊢ (? % ?).
         apply lt_times_r1
          [assumption
          |apply le_S_S.assumption
          ]
        ]
      ]
    ]
  |apply le_to_leb_true.
   rewrite > exp_plus_times.
   apply le_times;apply le_exp_log;assumption
  ]
qed.

theorem log_exp: \forall p,n,m.S O < p \to O < m \to
log p ((exp p n)*m)=n+log p m.
intros.
unfold log in ⊢ (? ? (% ? ?) ?).
apply max_spec_to_max.
unfold max_spec.
split
  [split
    [elim n
      [simplify.
       rewrite < plus_n_O.
       apply le_log_n_n.
       assumption
      |simplify.
       rewrite > assoc_times.
       apply (trans_le ? ((S(S O))*(p\sup n1*m)))
        [apply le_S_times_SSO
          [rewrite > (times_n_O O) in ⊢ (? % ?).
           apply lt_times
            [apply lt_O_exp.
             apply lt_to_le.
             assumption
            |assumption
            ]
          |assumption
          ]
        |apply le_times
          [assumption
          |apply le_n
          ]
        ]
      ]
    |simplify.
     apply le_to_leb_true.
     rewrite > exp_plus_times.
     apply le_times_r.
     apply le_exp_log.
     assumption
    ]
  |intros.
   simplify.
   apply lt_to_leb_false.
   apply (lt_to_le_to_lt ? ((exp p n)*(exp p (S(log p m)))))
    [apply lt_times_r1
      [apply lt_O_exp.apply lt_to_le.assumption
      |apply lt_exp_log.assumption
      ]
    |rewrite < exp_plus_times.
     apply le_exp
      [apply lt_to_le.assumption
      |rewrite < plus_n_Sm.
       assumption
      ]
    ]
  ]
qed.

theorem eq_log_exp: \forall p,n.S O < p \to
log p (exp p n)=n.
intros.
rewrite > times_n_SO in ⊢ (? ? (? ? %) ?).
rewrite > log_exp
  [rewrite > log_SO
    [rewrite < plus_n_O.reflexivity
    |assumption
    ]
  |assumption
  |apply le_n
  ]
qed.

theorem log_exp1: \forall p,n,m.S O < p \to
log p (exp n m) \le m*S(log p n).
intros.elim m
  [simplify in ⊢ (? (? ? %) ?).
   rewrite > log_SO
    [apply le_O_n
    |assumption
    ]
  |simplify.
   apply (trans_le ? (S (log p n+log p (n\sup n1))))
    [apply log_times.assumption
    |apply le_S_S.
     apply le_plus_r.
     assumption
    ]
  ]
qed.
    
theorem log_exp2: \forall p,n,m.S O < p \to O < n \to
m*(log p n) \le log p (exp n m).
intros.
apply le_S_S_to_le.
apply (lt_exp_to_lt p)
  [assumption
  |rewrite > sym_times.
   rewrite < exp_exp_times.
   apply (le_to_lt_to_lt ? (exp n m))
    [elim m
      [simplify.apply le_n
      |simplify.apply le_times
        [apply le_exp_log.
         assumption
        |assumption
        ]
      ]
    |apply lt_exp_log.
     assumption
    ]
  ]
qed.

lemma le_log_plus: \forall p,n.S O < p \to log p n \leq log p (S n).
intros;apply (bool_elim ? (leb (p*(exp p n)) (S n)))
  [simplify;intro;rewrite > H1;simplify;apply (trans_le ? n)
    [apply le_log_n_n;assumption
    |apply le_n_Sn]
  |intro;unfold log;simplify;rewrite > H1;simplify;apply le_max_f_max_g;
   intros;apply le_to_leb_true;constructor 2;apply leb_true_to_le;assumption]
qed.

theorem le_log: \forall p,n,m. S O < p \to n \le m \to 
log p n \le log p m.
intros.elim H1
  [constructor 1
  |apply (trans_le ? ? ? H3);apply le_log_plus;assumption]
qed.
         
theorem log_div: \forall p,n,m. S O < p \to O < m \to m \le n \to
log p (n/m) \le log p n -log p m.
intros.
apply le_plus_to_minus_r.
apply (trans_le ? (log p ((n/m)*m)))
  [apply log_times_l
    [apply le_times_to_le_div
      [assumption
      |rewrite < times_n_SO.
       assumption
      ]
    |assumption
    |assumption
    ]
  |apply le_log
    [assumption
    |rewrite > (div_mod n m) in ⊢ (? ? %)
      [apply le_plus_n_r
      |assumption
      ]
    ]
  ]
qed.

theorem log_n_n: \forall n. S O < n \to log n n = S O.
intros.
rewrite > exp_n_SO in ⊢ (? ? (? ? %) ?).
rewrite > times_n_SO in ⊢ (? ? (? ? %) ?).
rewrite > log_exp
  [rewrite > log_SO
    [reflexivity
    |assumption
    ]
  |assumption
  |apply le_n
  ]
qed.

theorem log_i_SSOn: \forall n,i. S O < n \to n < i \to i \le ((S(S O))*n) \to
log i ((S(S O))*n) = S O.
intros.
apply antisymmetric_le
  [apply not_lt_to_le.intro.
   apply (lt_to_not_le ((S(S O)) * n) (exp i (S(S O))))
    [rewrite > exp_SSO.
     apply lt_times
      [apply (le_to_lt_to_lt ? n);assumption
      |assumption
      ]
    |apply (trans_le ? (exp i (log i ((S(S O))*n))))
      [apply le_exp
        [apply (ltn_to_ltO ? ? H1)
        |assumption
        ]
      |apply le_exp_log.
       rewrite > (times_n_O O) in ⊢ (? % ?).
       apply lt_times
        [apply lt_O_S
        |apply lt_to_le.assumption
        ]
      ]
    ]
  |apply (trans_le ? (log i i))
    [rewrite < (log_n_n i) in ⊢ (? % ?)
      [apply le_log
        [apply (trans_lt ? n);assumption
        |apply le_n
        ]
      |apply (trans_lt ? n);assumption
      ]
    |apply le_log
      [apply (trans_lt ? n);assumption
      |assumption
      ]
    ]
  ]
qed.

theorem exp_n_O: \forall n. O < n \to exp O n = O.
intros.apply (lt_O_n_elim ? H).intros.
simplify.reflexivity.
qed.

(*
theorem tech1: \forall n,i.O < n \to
(exp (S n) (S(S i)))/(exp n (S i)) \le ((exp n i) + (exp (S n) (S i)))/(exp n i).
intros.
simplify in ⊢ (? (? ? %) ?).
rewrite < eq_div_div_div_times
  [apply monotonic_div
    [apply lt_O_exp.assumption
    |apply le_S_S_to_le.
     apply lt_times_to_lt_div.
     change in ⊢ (? % ?) with ((exp (S n) (S i)) + n*(exp (S n) (S i))).
      
      
  |apply (trans_le ? ((n)\sup(i)*(S n)\sup(S i)/(n)\sup(S i)))
    [apply le_times_div_div_times.
     apply lt_O_exp.assumption
    |apply le_times_to_le_div2
      [apply lt_O_exp.assumption
      |simplify.

theorem tech1: \forall a,b,n,m.O < m \to
n/m \le b \to (a*n)/m \le a*b.
intros.
apply le_times_to_le_div2
  [assumption
  |

theorem tech2: \forall n,m. O < n \to 
(exp (S n) m) / (exp n m) \le (n + m)/n.
intros.
elim m
  [rewrite < plus_n_O.simplify.
   rewrite > div_n_n.apply le_n
  |apply le_times_to_le_div
    [assumption
    |apply (trans_le ? (n*(S n)\sup(S n1)/(n)\sup(S n1)))
      [apply le_times_div_div_times.
       apply lt_O_exp
      |simplify in ⊢ (? (? ? %) ?).
       rewrite > sym_times in ⊢ (? (? ? %) ?). 
       rewrite < eq_div_div_div_times
        [apply le_times_to_le_div2
          [assumption
          |
      
      
theorem le_log_sigma_p:\forall n,m,p. O < m \to S O < p \to
log p (exp n m) \le sigma_p n (\lambda i.true) (\lambda i. (m / i)).
intros.
elim n
  [rewrite > exp_n_O
    [simplify.apply le_n
    |assumption
    ]
  |rewrite > true_to_sigma_p_Sn
    [apply (trans_le ? (m/n1+(log p (exp n1 m))))
      [
*)