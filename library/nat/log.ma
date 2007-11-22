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

set "baseuri" "cic:/matita/nat/log".

include "datatypes/constructors.ma".
include "nat/minimization.ma".
include "nat/relevant_equations.ma".
include "nat/primes.ma".

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

theorem le_log: \forall p,n,m. S O < p \to O < n \to n \le m \to 
log p n \le log p m.
intros.
apply le_S_S_to_le.
apply (lt_exp_to_lt p)
  [assumption
  |apply (le_to_lt_to_lt ? n)
    [apply le_exp_log.
     assumption
    |apply (le_to_lt_to_lt ? m)
      [assumption
      |apply lt_exp_log.
       assumption
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
        |apply (ltn_to_ltO ? ? H1)
        |apply le_n
        ]
      |apply (trans_lt ? n);assumption
      ]
    |apply le_log
      [apply (trans_lt ? n);assumption
      |apply (ltn_to_ltO ? ? H1)
      |assumption
      ]
    ]
  ]
qed.
