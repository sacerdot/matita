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

include "nat/exp.ma".
include "nat/factorial.ma".

theorem factS: \forall n. fact (S n) = (S n)*(fact n).
intro.simplify.reflexivity.
qed.

theorem exp_S: \forall n,m. exp m (S n) = m*exp m n.
intros.reflexivity.
qed.

theorem lt_O_to_fact1: \forall n.O<n \to
fact (2*n) \le (exp 2 (pred (2*n)))*(fact n)*(fact n).
intros.elim H
  [apply le_n
  |rewrite > times_SSO.
   rewrite > factS.
   rewrite > factS.
   rewrite < assoc_times.
   rewrite > factS.
   apply (trans_le ? ((2*(S n1))*(2*(S n1))*(fact (2*n1))))
    [apply le_times_l.
     rewrite > times_SSO.
     apply le_times_r.
     apply le_n_Sn
    |rewrite > assoc_times.
     rewrite > assoc_times.
     rewrite > assoc_times in ⊢ (? ? %).
     change in ⊢ (? ? (? (? ? %) ?)) with (S(2*n1)).
     rewrite > exp_S. 
     rewrite > assoc_times in ⊢ (? ? %).
     apply le_times_r.
     rewrite < assoc_times.
     rewrite < assoc_times.
     rewrite < sym_times in ⊢ (? (? (? % ?) ?) ?).
     rewrite > assoc_times.
     rewrite > assoc_times.
     rewrite > S_pred in ⊢ (? ? (? (? ? %) ?))
      [rewrite > exp_S. 
       rewrite > assoc_times in ⊢ (? ? %).
       apply le_times_r.
       rewrite > sym_times in ⊢ (? ? %).
       rewrite > assoc_times in ⊢ (? ? %).
       rewrite > assoc_times in ⊢ (? ? %).
       apply le_times_r.
       rewrite < assoc_times in ⊢ (? ? %).
       rewrite < assoc_times in ⊢ (? ? %).
       rewrite < sym_times in ⊢ (? ? (? (? % ?) ?)).
       rewrite > assoc_times in ⊢ (? ? %).
       rewrite > assoc_times in ⊢ (? ? %).
       apply le_times_r.
       rewrite > sym_times in ⊢ (? ? (? ? %)).
       rewrite > sym_times in ⊢ (? ? %).
       assumption
      |unfold.rewrite > times_n_SO in ⊢ (? % ?).
       apply le_times
        [apply le_n_Sn
        |assumption
        ]
      ]
    ]
  ]
qed.

theorem fact1: \forall n.
fact (2*n) \le (exp 2 (pred (2*n)))*(fact n)*(fact n).
intro.cases n
  [apply le_n
  |apply lt_O_to_fact1.
   apply lt_O_S
  ]
qed.

theorem lt_O_fact: \forall n. O < fact n.
intro.elim n
  [simplify.apply lt_O_S
  |rewrite > factS.
   rewrite > (times_n_O O).
   apply lt_times
    [apply lt_O_S
    |assumption
    ]
  ]
qed.

theorem fact2: \forall n.O < n \to
(exp 2 (2*n))*(fact n)*(fact n) < fact (S(2*n)).
intros.elim H
  [simplify.apply le_S.apply le_n
  |rewrite > times_SSO.
   rewrite > factS.
   rewrite > factS.
   rewrite < assoc_times.
   rewrite > factS.
   rewrite < times_SSO in ⊢ (? ? %).
   apply (trans_lt ? (((S(S O))*S n1)*((S(S O))*S n1*(S ((S(S O))*n1))!)))
    [rewrite > assoc_times in ⊢ (? ? %).
     rewrite > exp_S.
     rewrite > assoc_times.
     rewrite > assoc_times.
     rewrite > assoc_times.
     apply lt_times_r.
     rewrite > exp_S.
     rewrite > assoc_times.
     rewrite > sym_times in ⊢ (? ? %).
     rewrite > assoc_times in ⊢ (? ? %).
     rewrite > assoc_times in ⊢ (? ? %).
     apply lt_times_r.
     rewrite > sym_times.
     rewrite > assoc_times.
     rewrite > assoc_times.
     apply lt_times_r.
     rewrite < assoc_times.
     rewrite < assoc_times.
     rewrite > sym_times in ⊢ (? (? (? % ?) ?) ?).
     rewrite > assoc_times.
     rewrite > assoc_times.
     rewrite > sym_times in ⊢ (? ? %).
     apply lt_times_r.
     rewrite < assoc_times.
     rewrite < sym_times.
     rewrite < assoc_times.
     assumption
    |apply lt_times_l1
      [rewrite > (times_n_O O) in ⊢ (? % ?).
       apply lt_times
        [rewrite > (times_n_O O) in ⊢ (? % ?).
         apply lt_times
          [apply lt_O_S
          |apply lt_O_S
          ]
        |apply lt_O_fact
        ]
      |apply le_n
      ]
    ]
  ]
qed.

(* a slightly better result *)
theorem fact3: \forall n.O < n \to
(exp 2 (2*n))*(exp (fact n) 2) \le 2*n*fact (2*n).
intros.
elim H
  [simplify.apply le_n
  |rewrite > times_SSO.
   rewrite > factS.
   rewrite < times_exp.
   change in ⊢ (? (? % ?) ?) with ((S(S O))*((S(S O))*(exp (S(S O)) ((S(S O))*n1)))).
   rewrite > assoc_times.
   rewrite > assoc_times in ⊢ (? (? ? %) ?).
   rewrite < assoc_times in ⊢ (? (? ? (? ? %)) ?).
   rewrite < sym_times in ⊢ (? (? ? (? ? (? % ?))) ?).
   rewrite > assoc_times in ⊢ (? (? ? (? ? %)) ?).
   apply (trans_le ? (((S(S O))*((S(S O))*((S n1)\sup((S(S O)))*((S(S O))*n1*((S(S O))*n1)!))))))
    [apply le_times_r.
     apply le_times_r.
     apply le_times_r.
     assumption
    |rewrite > factS.
     rewrite > factS.
     rewrite < times_SSO.
     rewrite > assoc_times in ⊢ (? ? %). 
     apply le_times_r.
     rewrite < assoc_times.
     change in ⊢ (? (? (? ? %) ?) ?) with ((S n1)*((S n1)*(S O))).
     rewrite < assoc_times in ⊢ (? (? % ?) ?).
     rewrite < times_n_SO.
     rewrite > sym_times in ⊢ (? (? (? % ?) ?) ?).
     rewrite < assoc_times in ⊢ (? ? %).
     rewrite < assoc_times in ⊢ (? ? (? % ?)).
     apply le_times_r.
     apply le_times_l.
     apply le_S.apply le_n
    ]
  ]
qed.

theorem le_fact_10: fact (2*5) \le (exp 2 ((2*5)-2))*(fact 5)*(fact 5).
simplify in \vdash (? (? %) ?).
rewrite > factS in \vdash (? % ?).
rewrite > factS in \vdash (? % ?).rewrite < assoc_times in \vdash(? % ?).
rewrite > factS in \vdash (? % ?).rewrite < assoc_times in \vdash (? % ?).
rewrite > factS in \vdash (? % ?).rewrite < assoc_times in \vdash (? % ?).
rewrite > factS in \vdash (? % ?).rewrite < assoc_times in \vdash (? % ?).
apply le_times_l.
apply leb_true_to_le.reflexivity.
qed.

theorem ab_times_cd: \forall a,b,c,d.(a*b)*(c*d)=(a*c)*(b*d).
intros.
rewrite > assoc_times.
rewrite > assoc_times.
apply eq_f.
rewrite < assoc_times.
rewrite < assoc_times.
rewrite > sym_times in \vdash (? ? (? % ?) ?).
reflexivity.
qed.

(* an even better result *)
theorem lt_SSSSO_to_fact: \forall n.4<n \to
fact (2*n) \le (exp 2 ((2*n)-2))*(fact n)*(fact n).
intros.elim H
  [apply le_fact_10
  |rewrite > times_SSO.
   change in \vdash (? ? (? (? (? ? %) ?) ?)) with (2*n1 - O);
   rewrite < minus_n_O.
   rewrite > factS.
   rewrite > factS.
   rewrite < assoc_times.
   rewrite > factS.
   apply (trans_le ? ((2*(S n1))*(2*(S n1))*(fact (2*n1))))
    [apply le_times_l.
     rewrite > times_SSO.
     apply le_times_r.
     apply le_n_Sn
    |apply (trans_le ? (2*S n1*(2*S n1)*(2\sup(2*n1-2)*n1!*n1!)))
      [apply le_times_r.assumption
      |rewrite > assoc_times.
       rewrite > ab_times_cd in \vdash (? (? ? %) ?).
       rewrite < assoc_times.
       apply le_times_l.
       rewrite < assoc_times in \vdash (? (? ? %) ?).
       rewrite > ab_times_cd.
       apply le_times_l.
       rewrite < exp_S.
       rewrite < exp_S.
       apply le_exp
        [apply lt_O_S
        |rewrite > eq_minus_S_pred.
         rewrite < S_pred
          [rewrite > eq_minus_S_pred.
           rewrite < S_pred
            [rewrite < minus_n_O.
             apply le_n
            |elim H1;simplify
              [apply lt_O_S
              |apply lt_O_S
              ]
            ]
          |elim H1;simplify
            [apply lt_O_S
            |rewrite < plus_n_Sm.
             rewrite < minus_n_O.
             apply lt_O_S
            ]
          ]
        ]
      ]
    ]
  ]
qed.


(*
theorem stirling: \forall n,k.k \le n \to
log (fact n) < n*log n - n + k*log n.
intro.
apply (nat_elim1 n).
intros.
elim (lt_O_to_or_eq_S m)
  [elim H2.clear H2.
   elim H4.clear H4.
   rewrite > H2.
   apply (le_to_lt_to_lt ? (log ((exp (S(S O)) ((S(S O))*a))*(fact a)*(fact a))))
    [apply monotonic_log.
     apply fact1
    |rewrite > assoc_times in ⊢ (? (? %) ?).
     rewrite > log_exp.
     apply (le_to_lt_to_lt ? ((S(S O))*a+S(log a!+log a!)))
      [apply le_plus_r.
       apply log_times
      |rewrite < plus_n_Sm.
       rewrite > plus_n_O in ⊢ (? (? (? ? (? ? %))) ?).
       change with
        (S((S(S O))*a+((S(S O))*log a!)) < (S(S O))*a*log ((S(S O))*a)-(S(S O))*a+k*log ((S(S O))*a)).
       apply (trans_lt ? (S ((S(S O))*a+(S(S O))*(a*log a-a+k*log a))))
        [apply le_S_S.
         apply lt_plus_r.
         apply lt_times_r.
         apply H.
         assumption
        |
        
          [
       
       a*log a-a+k*log a
       
*)