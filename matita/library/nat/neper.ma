(**************************************************************************)
(*       __                                                               *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "nat/iteration2.ma".
include "nat/div_and_mod_diseq.ma".
include "nat/binomial.ma".
include "nat/log.ma".
include "nat/chebyshev.ma".
                  
theorem sigma_p_div_exp: \forall n,m.
sigma_p n (\lambda i.true) (\lambda i.m/(exp (S(S O)) i)) \le 
((S(S O))*m*(exp (S(S O)) n) - (S(S O))*m)/(exp (S(S O)) n).
intros.
elim n
  [apply le_O_n.
  |rewrite > true_to_sigma_p_Sn
    [apply (trans_le ? (m/(S(S O))\sup(n1)+((S(S O))*m*(S(S O))\sup(n1)-(S(S O))*m)/(S(S O))\sup(n1)))
      [apply le_plus_r.assumption
      |rewrite > assoc_times in ⊢ (? ? (? (? % ?) ?)).
       rewrite < distr_times_minus.
       change in ⊢ (? ? (? ? %)) with ((S(S O))*(exp (S(S O)) n1)).
       rewrite > sym_times in ⊢ (? ? (? % ?)).
       rewrite > sym_times in ⊢ (? ? (? ? %)).
       rewrite < lt_to_lt_to_eq_div_div_times_times
        [apply (trans_le ? ((m+((S(S O))*m*((S(S O)))\sup(n1)-(S(S O))*m))/((S(S O)))\sup(n1)))
          [apply le_plus_div.
           apply lt_O_exp.
           apply lt_O_S
          |change in ⊢ (? (? (? ? (? ? %)) ?) ?) with (m + (m +O)).
           rewrite < plus_n_O.
           rewrite < eq_minus_minus_minus_plus.
           rewrite > sym_plus.
           rewrite > sym_times in ⊢ (? (? (? (? (? (? % ?) ?) ?) ?) ?) ?).
           rewrite > assoc_times.
           rewrite < plus_minus_m_m
            [apply le_n
            |apply le_plus_to_minus_r.
             rewrite > plus_n_O in ⊢ (? (? ? %) ?).
             change in ⊢ (? % ?) with ((S(S O))*m). 
             rewrite > sym_times.
             apply le_times_r.
             rewrite > times_n_SO in ⊢ (? % ?).
             apply le_times_r.
             apply lt_O_exp.
             apply lt_O_S
            ]
          ]
        |apply lt_O_S
        |apply lt_O_exp.
         apply lt_O_S
        ]
      ]
    |reflexivity
    ]
  ]
qed.
   
theorem le_fact_exp: \forall i,m. i \le m \to m!≤ m \sup i*(m-i)!.
intro.elim i
  [rewrite < minus_n_O.
   simplify.rewrite < plus_n_O.
   apply le_n
  |simplify.
   apply (trans_le ? ((m)\sup(n)*(m-n)!))
    [apply H.
     apply lt_to_le.assumption
    |rewrite > sym_times in ⊢ (? ? (? % ?)).
     rewrite > assoc_times.
     apply le_times_r.
     generalize in match H1.
     cases m;intro
      [apply False_ind.
       apply (lt_to_not_le ? ? H2).
       apply le_O_n
      |rewrite > minus_Sn_m.
       simplify.
       apply le_plus_r.
       apply le_times_l.
       apply le_minus_m.
       apply le_S_S_to_le.
       assumption
      ]
    ]
  ]
qed.

theorem le_fact_exp1: \forall n. S O < n \to (S(S O))*n!≤ n \sup n.
intros.elim H
  [apply le_n
  |change with ((S(S O))*((S n1)*(fact n1)) \le (S n1)*(exp (S n1) n1)).   
   rewrite < assoc_times.
   rewrite < sym_times in ⊢ (? (? % ?) ?).
   rewrite > assoc_times.
   apply le_times_r.
   apply (trans_le ? (exp n1 n1))
    [assumption
    |apply monotonic_exp1.
     apply le_n_Sn
    ]
  ]
qed.
   
theorem le_exp_sigma_p_exp: \forall n. (exp (S n) n) \le
sigma_p (S n) (\lambda k.true) (\lambda k.(exp n n)/k!).
intro.
rewrite > exp_S_sigma_p.
apply le_sigma_p.
intros.unfold bc.
apply (trans_le ? ((exp n (n-i))*((n \sup i)/i!)))
  [rewrite > sym_times.
   apply le_times_r.
   rewrite > sym_times.
   rewrite < eq_div_div_div_times
    [apply monotonic_div
      [apply lt_O_fact
      |apply le_times_to_le_div2
        [apply lt_O_fact
        |apply le_fact_exp.
         apply le_S_S_to_le.
         assumption
        ]
      ]
    |apply lt_O_fact
    |apply lt_O_fact
    ]
  |rewrite > (plus_minus_m_m ? i) in ⊢ (? ? (? (? ? %) ?))
    [rewrite > exp_plus_times.
     apply le_times_div_div_times.
     apply lt_O_fact
    |apply le_S_S_to_le.
     assumption
    ]
  ]
qed.
    
theorem lt_exp_sigma_p_exp: \forall n. S O < n \to
(exp (S n) n) <
sigma_p (S n) (\lambda k.true) (\lambda k.(exp n n)/k!).
intros.
rewrite > exp_S_sigma_p.
apply lt_sigma_p
  [intros.unfold bc.
   apply (trans_le ? ((exp n (n-i))*((n \sup i)/i!)))
    [rewrite > sym_times.
     apply le_times_r.
     rewrite > sym_times.
     rewrite < eq_div_div_div_times
      [apply monotonic_div
        [apply lt_O_fact
        |apply le_times_to_le_div2
          [apply lt_O_fact
          |apply le_fact_exp.
           apply le_S_S_to_le.
           assumption
          ]
        ]
      |apply lt_O_fact
      |apply lt_O_fact
      ]
    |rewrite > (plus_minus_m_m ? i) in ⊢ (? ? (? (? ? %) ?))
      [rewrite > exp_plus_times.
       apply le_times_div_div_times.
       apply lt_O_fact
      |apply le_S_S_to_le.
       assumption
      ]
    ]
  |apply (ex_intro ? ? n).
   split
    [split
      [apply le_n
      |reflexivity
      ]
    |rewrite < minus_n_n.
     rewrite > bc_n_n.
     simplify.unfold lt.
     apply le_times_to_le_div
      [apply lt_O_fact
      |rewrite > sym_times.
       apply le_fact_exp1.
       assumption
      ]
    ]
  ]
qed.

theorem le_exp_SSO_fact:\forall n. 
exp (S(S O)) (pred n) \le n!.
intro.elim n
  [apply le_n
  |change with ((S(S O))\sup n1 ≤(S n1)*n1!).
   apply (nat_case1 n1);intros
    [apply le_n
    |change in ⊢ (? % ?) with ((S(S O))*exp (S(S O)) (pred (S m))).
     apply le_times
      [apply le_S_S.apply le_S_S.apply le_O_n
      |rewrite < H1.assumption
      ]
    ]
  ]
qed.
       
theorem lt_SO_to_lt_exp_Sn_n_SSSO: \forall n. S O < n \to 
(exp (S n) n) < (S(S(S O)))*(exp n n).
intros.  
apply (lt_to_le_to_lt ? (sigma_p (S n) (\lambda k.true) (\lambda k.(exp n n)/k!)))
  [apply lt_exp_sigma_p_exp.assumption
  |apply (trans_le ? (sigma_p (S n) (\lambda i.true) (\lambda i.(exp n n)/(exp (S(S O)) (pred i)))))
    [apply le_sigma_p.intros.
     apply le_times_to_le_div
      [apply lt_O_exp.
       apply lt_O_S
      |apply (trans_le ? ((S(S O))\sup (pred i)* n \sup n/i!))
        [apply le_times_div_div_times.
         apply lt_O_fact
        |apply le_times_to_le_div2
          [apply lt_O_fact
          |rewrite < sym_times.
           apply le_times_r.
           apply le_exp_SSO_fact
          ]
        ]
      ]
    |rewrite > eq_sigma_p_pred
      [rewrite > div_SO.
       rewrite > sym_plus.
       change in ⊢ (? ? %) with ((exp n n)+(S(S O)*(exp n n))).
       apply le_plus_r.
       apply (trans_le ? (((S(S O))*(exp n n)*(exp (S(S O)) n) - (S(S O))*(exp n n))/(exp (S(S O)) n)))
        [apply sigma_p_div_exp
        |apply le_times_to_le_div2
          [apply lt_O_exp.
           apply lt_O_S.
          |apply le_minus_m
          ]
        ]
      |reflexivity
      ]
    ]
  ]
qed.     
    
theorem lt_exp_Sn_n_SSSO: \forall n.
(exp (S n) n) < (S(S(S O)))*(exp n n).
intro.cases n;intros
  [simplify.apply le_S.apply le_n
  |cases n1;intros
    [simplify.apply le_n
    |apply lt_SO_to_lt_exp_Sn_n_SSSO.
     apply le_S_S.apply le_S_S.apply le_O_n
    ]
  ]
qed.

theorem lt_exp_Sn_m_SSSO: \forall n,m. O < m \to
divides n m \to
(exp (S n) m) < (exp (S(S(S O))) (m/n)) *(exp n m).
intros.
elim H1.rewrite > H2.
rewrite < exp_exp_times.
rewrite < exp_exp_times.
rewrite > sym_times in ⊢ (? ? (? (? ? (? % ?)) ?)).
rewrite > lt_O_to_div_times
  [rewrite > times_exp.
   apply lt_exp1
    [apply (O_lt_times_to_O_lt ? n).
     rewrite > sym_times.
     rewrite < H2.
     assumption
    |apply lt_exp_Sn_n_SSSO
    ]
  |apply (O_lt_times_to_O_lt ? n1).
   rewrite < H2.
   assumption
  ]
qed.

theorem le_log_exp_Sn_log_exp_n: \forall n,m,p. O < m \to S O < p \to
divides n m \to
log p (exp (S n) m) \le S((m/n)*S(log p (S(S(S O))))) + log p (exp n m).
intros.
apply (trans_le ? (log p (((S(S(S O))))\sup(m/n)*((n)\sup(m)))))
  [apply le_log
    [assumption
    |apply lt_to_le.
     apply lt_exp_Sn_m_SSSO;assumption
    ]
  |apply (trans_le ? (S(log p (exp (S(S(S O))) (m/n)) + log p (exp n m))))
    [apply log_times.
     assumption
    |change in ⊢ (? ? %) with (S (m/n*S (log p (S(S(S O))))+log p ((n)\sup(m)))).
     apply le_S_S.
     apply le_plus_l.
     apply log_exp1.
     assumption
    ]
  ]
qed.

theorem le_log_exp_fact_sigma_p: \forall a,b,n,p. S O < p \to
O < a \to a \le b \to b \le n \to
log p (exp b n!) - log p (exp a n!) \le
sigma_p b (\lambda i.leb a i) (\lambda i.S((n!/i)*S(log p (S(S(S O)))))).
intros 7.
elim b
  [simplify.
   apply (lt_O_n_elim ? (lt_O_fact n)).intro.
   apply le_n.
  |apply (bool_elim ? (leb a n1));intro
    [rewrite > true_to_sigma_p_Sn
      [apply (trans_le ? (S (n!/n1*S (log p (S(S(S O)))))+(log p ((n1)\sup(n!))-log p ((a)\sup(n!)))))
        [rewrite > sym_plus. 
         rewrite > plus_minus
          [apply le_plus_to_minus_r.
           rewrite < plus_minus_m_m
            [rewrite > sym_plus.
             apply le_log_exp_Sn_log_exp_n
              [apply lt_O_fact
              |assumption
              |apply divides_fact;
                 [apply (trans_le ? ? ? H1);apply leb_true_to_le;assumption
                 |apply lt_to_le;assumption]]
            |apply le_log
              [assumption
              |cut (O = exp O n!)
                 [apply monotonic_exp1;constructor 2;
                  apply leb_true_to_le;assumption
                 |elim n
                    [reflexivity
                    |simplify;rewrite > exp_plus_times;rewrite < H6;
                     rewrite > sym_times;rewrite < times_n_O;reflexivity]]]]
        |apply le_log
          [assumption
          |apply monotonic_exp1;apply leb_true_to_le;assumption]]
      |rewrite > sym_plus;rewrite > sym_plus in \vdash (? ? %);apply le_minus_to_plus;
       rewrite < minus_plus_m_m;apply H3;apply lt_to_le;assumption]
    |assumption]
  |lapply (not_le_to_lt ? ? (leb_false_to_not_le ? ? H5));
   rewrite > eq_minus_n_m_O
    [apply le_O_n
    |apply le_log
       [assumption
       |apply monotonic_exp1;assumption]]]]
qed.

theorem le_exp_div:\forall n,m,q. O < m \to 
exp (n/m) q \le (exp n q)/(exp m q).
intros.
apply le_times_to_le_div
  [apply lt_O_exp.
   assumption
  |rewrite > times_exp.
   rewrite < sym_times.
   apply monotonic_exp1.
   rewrite > (div_mod n m) in ⊢ (? ? %)
    [apply le_plus_n_r
    |assumption
    ]
  ]
qed.

theorem le_log_div_sigma_p: \forall a,b,n,p. S O < p \to
O < a \to a \le b \to b \le n \to
log p (b/a) \le
(sigma_p b (\lambda i.leb a i) (\lambda i.S((n!/i)*S(log p (S(S(S O)))))))/n!.
intros.
apply le_times_to_le_div
  [apply lt_O_fact
  |apply (trans_le ? (log p (exp (b/a) n!)))
    [apply log_exp2
      [assumption
      |apply le_times_to_le_div
        [assumption
        |rewrite < times_n_SO.
         assumption
        ]
      ]
    |apply (trans_le ? (log p ((exp b n!)/(exp a n!)))) 
      [apply le_log
        [assumption
        |apply le_exp_div.assumption
        ]
      |apply (trans_le ? (log p (exp b n!) - log p (exp a n!)))
        [apply log_div
          [assumption
          |apply lt_O_exp.
           assumption
          |apply monotonic_exp1.
           assumption
          ]
        |apply le_log_exp_fact_sigma_p;assumption
        ]
      ]
    ]
  ]
qed.
      
theorem sigma_p_log_div1: \forall n,b. S O < b \to
sigma_p (S n) (\lambda p.(primeb p \land (leb (S n) (p*p)))) (\lambda p.(log b (n/p)))
\le sigma_p (S n) (\lambda p.primeb p \land (leb (S n) (p*p))) (\lambda p.(sigma_p n (\lambda i.leb p i) (\lambda i.S((n!/i)*S(log b (S(S(S O)))))))/n!
).
intros.
apply le_sigma_p.intros.
apply le_log_div_sigma_p
  [assumption
  |apply prime_to_lt_O.
   apply primeb_true_to_prime.
   apply (andb_true_true ? ? H2)
  |apply le_S_S_to_le.
   assumption
  |apply le_n
  ]
qed.

theorem sigma_p_log_div2: \forall n,b. S O < b \to
sigma_p (S n) (\lambda p.(primeb p \land (leb (S n) (p*p)))) (\lambda p.(log b (n/p)))
\le 
(sigma_p (S n) (\lambda p.primeb p \land (leb (S n) (p*p))) (\lambda p.(sigma_p n (\lambda i.leb p i) (\lambda i.S((n!/i)))))*S(log b (S(S(S O))))/n!).
intros.
apply (trans_le ? (sigma_p (S n) (\lambda p.primeb p \land (leb (S n) (p*p))) (\lambda p.(sigma_p n (\lambda i.leb p i) (\lambda i.S((n!/i)*S(log b (S(S(S O)))))))/n!
)))
  [apply sigma_p_log_div1.assumption
  |apply le_times_to_le_div
    [apply lt_O_fact
    |rewrite > distributive_times_plus_sigma_p.
     rewrite < sym_times in ⊢ (? ? %).
     rewrite > distributive_times_plus_sigma_p.
     apply le_sigma_p.intros.
     apply (trans_le ? ((n!*(sigma_p n (λj:nat.leb i j) (λi:nat.S (n!/i*S (log b (S(S(S O)))))))/n!)))
      [apply le_times_div_div_times.
       apply lt_O_fact
      |rewrite > sym_times.
       rewrite > lt_O_to_div_times
        [rewrite > distributive_times_plus_sigma_p.
         apply le_sigma_p.intros.
         rewrite < times_n_Sm in ⊢ (? ? %).
         rewrite > plus_n_SO.
         rewrite > sym_plus.
         apply le_plus
          [apply le_S_S.apply le_O_n
          |rewrite < sym_times.
           apply le_n
          ]
        |apply lt_O_fact
        ]
      ]
    ]
  ]
qed.

theorem sigma_p_log_div: \forall n,b. S O < b \to
sigma_p (S n) (\lambda p.(primeb p \land (leb (S n) (p*p)))) (\lambda p.(log b (n/p)))
\le (sigma_p n (\lambda i.leb (S n) (i*i)) (\lambda i.(prim i)*S(n!/i)))*S(log b (S(S(S O))))/n!
.
intros.
apply (trans_le ? (sigma_p (S n) (\lambda p.primeb p \land (leb (S n) (p*p))) (\lambda p.(sigma_p n (\lambda i.leb p i) (\lambda i.S((n!/i)))))*S(log b (S(S(S O))))/n!))
  [apply sigma_p_log_div2.assumption
  |apply monotonic_div
    [apply lt_O_fact
    |apply le_times_l.
     unfold prim.
     cut
     (sigma_p (S n) (λp:nat.primeb p∧leb (S n) (p*p))
      (λp:nat.sigma_p n (λi:nat.leb p i) (λi:nat.S (n!/i)))
     = sigma_p n (λi:nat.leb (S n) (i*i))
       (λi:nat.sigma_p (S n) (\lambda p.primeb p \land leb (S n) (p*p) \land leb p i) (λp:nat.S (n!/i))))
      [rewrite > Hcut.
       apply le_sigma_p.intros.
       rewrite < sym_times.
       rewrite > distributive_times_plus_sigma_p.
       rewrite < times_n_SO.
       cut 
        (sigma_p (S n) (λp:nat.primeb p∧leb (S n) (p*p) \land leb p i) (λp:nat.S (n!/i))
         = sigma_p (S i) (\lambda p.primeb p \land leb (S n) (p*p) \land leb p i) (λp:nat.S (n!/i)))
        [rewrite > Hcut1.
         apply le_sigma_p1.intros.
         rewrite < andb_sym.
         rewrite < andb_sym in ⊢ (? (? (? (? ? %)) ?) ?).
         apply (bool_elim  ? (leb i1 i));intros
          [apply (bool_elim  ? (leb (S n) (i1*i1)));intros
            [apply le_n
            |apply le_O_n
            ]
          |apply le_O_n
          ]
        |apply or_false_to_eq_sigma_p
          [apply le_S.assumption
          |intros.
           left.rewrite > (lt_to_leb_false i1 i)
            [rewrite > andb_sym.reflexivity
            |assumption
            ]
          ]
        ]
      |apply sigma_p_sigma_p.intros.
       apply (bool_elim ? (leb x y));intros
        [apply (bool_elim ? (leb (S n) (x*x)));intros
          [rewrite > le_to_leb_true in ⊢ (? ? ? (? % ?))
            [reflexivity
            |apply (trans_le ? (x*x))
              [apply leb_true_to_le.assumption
              |apply le_times;apply leb_true_to_le;assumption
              ]
            ]
          |rewrite < andb_sym in ⊢ (? ? (? % ?) ?).
           rewrite < andb_sym in ⊢ (? ? ? (? ? (? % ?))).
           rewrite < andb_sym in ⊢ (? ? ? %).
           reflexivity
          ]
        |rewrite < andb_sym.
         rewrite > andb_assoc in ⊢ (? ? ? %).
         rewrite < andb_sym in ⊢ (? ? ? (? % ?)).
         reflexivity
        ]
      ]
    ]
  ]
qed.

theorem le_sigma_p_div_log_div_pred_log : \forall n,b,m. S O < b \to b*b \leq n \to
sigma_p (S n) (\lambda i.leb (S n) (i*i)) (\lambda i.m/(log b i))
\leq ((S (S O)) * n * m)/(pred (log b n)).
intros.
apply (trans_le ? (sigma_p (S n) 
             (\lambda i.leb (S n) (i*i)) (\lambda i.(S (S O))*m/(pred (log b n)))))
  [apply le_sigma_p;intros;apply le_times_to_le_div
     [rewrite > minus_n_O in ⊢ (? ? (? %));rewrite < eq_minus_S_pred;
      apply le_plus_to_minus_r;simplify;
      rewrite < (eq_log_exp b ? H);
      apply le_log;
          [assumption
          |simplify;rewrite < times_n_SO;assumption]
     |apply (trans_le ? ((pred (log b n) * m)/log b i))
        [apply le_times_div_div_times;apply lt_O_log
          [elim (le_to_or_lt_eq ? ? (le_O_n i))
            [assumption
            |apply False_ind;apply not_eq_true_false;rewrite < H3;rewrite < H4;
             reflexivity]
          |apply (le_exp_to_le1 ? ? (S (S O)))
            [apply lt_O_S;
            |apply (trans_le ? (S n))
               [apply le_S;simplify;rewrite < times_n_SO;assumption
               |rewrite > exp_SSO;apply leb_true_to_le;assumption]]]
        |apply le_times_to_le_div2
          [apply lt_O_log
            [elim (le_to_or_lt_eq ? ? (le_O_n i))
              [assumption
              |apply False_ind;apply not_eq_true_false;rewrite < H3;rewrite < H4;
               reflexivity]
          |apply (le_exp_to_le1 ? ? (S (S O)))
            [apply lt_O_S;
            |apply (trans_le ? (S n))
               [apply le_S;simplify;rewrite < times_n_SO;assumption
               |rewrite > exp_SSO;apply leb_true_to_le;assumption]]]
          |rewrite > sym_times in \vdash (? ? %);rewrite < assoc_times;
           apply le_times_l;rewrite > sym_times;
           rewrite > minus_n_O in \vdash (? (? %) ?);
           rewrite < eq_minus_S_pred;apply le_plus_to_minus;
           simplify;rewrite < plus_n_O;apply (trans_le ? (log b (i*i)))
             [apply le_log
                [assumption
                |apply lt_to_le;apply leb_true_to_le;assumption]
             |rewrite > sym_plus;simplify;apply log_times;assumption]]]]
        |rewrite > times_n_SO in \vdash (? (? ? ? (\lambda i:?.%)) ?);
         rewrite < distributive_times_plus_sigma_p;
         apply (trans_le ? ((((S (S O))*m)/(pred (log b n)))*n))
           [apply le_times_r;apply (trans_le ? (sigma_p (S n) (\lambda i:nat.leb (S O) (i*i)) (\lambda Hbeta1:nat.S O)))
             [apply le_sigma_p1;intros;do 2 rewrite < times_n_SO;
              apply (bool_elim ? (leb (S n) (i*i)))
                [intro;cut (leb (S O) (i*i) = true)
                  [rewrite > Hcut;apply le_n
                  |apply le_to_leb_true;apply (trans_le ? (S n))
                     [apply le_S_S;apply le_O_n
                     |apply leb_true_to_le;assumption]]
                |intro;simplify in \vdash (? % ?);apply le_O_n]
             |elim n
                [simplify;apply le_n
                |apply (bool_elim ? (leb (S O) ((S n1)*(S n1))));intro
                   [rewrite > true_to_sigma_p_Sn
                      [change in \vdash (? % ?) with (S (sigma_p (S n1) (\lambda i:nat.leb (S O) (i*i)) (\lambda Hbeta1:nat.S O)));
                       apply le_S_S;assumption
                      |assumption]
                   |rewrite > false_to_sigma_p_Sn
                      [apply le_S;assumption
                      |assumption]]]]
          |rewrite > sym_times in \vdash (? % ?);
           rewrite > sym_times in \vdash (? ? (? (? % ?) ?));
           rewrite > assoc_times;
           apply le_times_div_div_times;
           rewrite > minus_n_O in ⊢ (? ? (? %));rewrite < eq_minus_S_pred;
           apply le_plus_to_minus_r;simplify;
           rewrite < (eq_log_exp b ? H);
           apply le_log;
             [assumption
             |simplify;rewrite < times_n_SO;assumption]]]
qed.

lemma neper_sigma_p1 : \forall n,a.n \divides a \to
exp (a * S n) n =
sigma_p (S n) (\lambda x.true) (\lambda k.(bc n k)*(exp n (n-k))*(exp a n)).
intros;rewrite < times_exp;rewrite > exp_S_sigma_p;
rewrite > distributive_times_plus_sigma_p;
apply eq_sigma_p;intros;
  [reflexivity
  |rewrite > sym_times;reflexivity;]
qed.

lemma eq_exp_pi_p : \forall a,n.(exp a n) = pi_p n (\lambda x.true) (\lambda x.a).
intros;elim n
  [simplify;reflexivity
  |change in \vdash (? ? % ?) with (a*exp a n1);rewrite > true_to_pi_p_Sn
     [apply eq_f2
        [reflexivity
        |assumption]
     |reflexivity]]
qed.

lemma eq_fact_pi_p : \forall n.n! = pi_p n (\lambda x.true) (\lambda x.S x).
intros;elim n
  [simplify;reflexivity
  |rewrite > true_to_pi_p_Sn
     [change in \vdash (? ? % ?) with (S n1*n1!);apply eq_f2
        [reflexivity
        |assumption]
     |reflexivity]]
qed.

lemma divides_pi_p : \forall m,n,p,f.m \leq n \to pi_p m p f \divides pi_p n p f.
intros;elim H
  [apply divides_n_n
  |apply (bool_elim ? (p n1));intro
     [rewrite > true_to_pi_p_Sn
        [rewrite > sym_times;rewrite > times_n_SO;apply divides_times
           [assumption
           |apply divides_SO_n]
        |assumption]
     |rewrite > false_to_pi_p_Sn;assumption]]
qed.

lemma divides_fact_fact : \forall m,n.m \leq n \to m! \divides n!.
intros;do 2 rewrite > eq_fact_pi_p;apply divides_pi_p;assumption.
qed.

lemma divides_times_to_eq : \forall a,b,c.O < c \to c \divides a \to a*b/c = a/c*b.
intros;elim H1;rewrite > H2;cases H;rewrite > assoc_times;do 2 rewrite > div_times;
reflexivity;
qed.

lemma divides_pi_p_to_eq : \forall k,p,f,g.(\forall x.p x = true \to O < g x \land (g x \divides f x)) \to
pi_p k p f/pi_p k p g = pi_p k p (\lambda x.(f x)/(g x)).
intros;
cut (\forall k1.(pi_p k1 p g \divides pi_p k1 p f))
  [|intro;elim k1
     [simplify;apply divides_n_n
     |apply (bool_elim ? (p n));intro;
        [rewrite > true_to_pi_p_Sn
           [rewrite > true_to_pi_p_Sn
              [elim (H n)
                 [elim H4;elim H1;rewrite > H5;rewrite > H6;
                  rewrite < assoc_times;rewrite > assoc_times in ⊢ (? ? (? % ?));
                  rewrite > sym_times in ⊢ (? ? (? (? ? %) ?));
                  rewrite > assoc_times;rewrite > assoc_times;
                  apply divides_times
                    [apply divides_n_n
                    |rewrite > times_n_SO in \vdash (? % ?);apply divides_times
                       [apply divides_n_n
                       |apply divides_SO_n]]
                 |assumption]
              |assumption]
           |assumption]
        |rewrite > false_to_pi_p_Sn
           [rewrite > false_to_pi_p_Sn
              [assumption
              |assumption]
           |assumption]]]]
elim k
  [simplify;reflexivity
  |apply (bool_elim ? (p n))
     [intro;rewrite > true_to_pi_p_Sn;
        [rewrite > true_to_pi_p_Sn;
           [rewrite > true_to_pi_p_Sn;
              [elim (H n);
                 [elim H4;rewrite > H5;rewrite < eq_div_div_div_times;
                    [cases H3
                       [rewrite > assoc_times;do 2 rewrite > div_times;
                        elim (Hcut n);rewrite > H6;rewrite < assoc_times;
                        rewrite < sym_times in \vdash (? ? (? (? % ?) ?) ?);
                        cut (O < pi_p n p g)
                          [rewrite < H1;rewrite > H6;cases Hcut1;
                           rewrite > assoc_times;do 2 rewrite > div_times;reflexivity
                          |elim n
                             [simplify;apply le_n
                             |apply (bool_elim ? (p n3));intro
                                [rewrite > true_to_pi_p_Sn
                                   [rewrite > (times_n_O O);apply lt_times
                                      [elim (H n3);assumption
                                      |assumption]
                                   |assumption]
                                |rewrite > false_to_pi_p_Sn;assumption]]]
                       |rewrite > assoc_times;do 2 rewrite > div_times;
                        elim (Hcut n);rewrite > H7;rewrite < assoc_times;
                        rewrite < sym_times in \vdash (? ? (? (? % ?) ?) ?);
                        cut (O < pi_p n p g)
                          [rewrite < H1;rewrite > H7;cases Hcut1;
                           rewrite > assoc_times;do 2 rewrite > div_times;reflexivity
                          |elim n
                             [simplify;apply le_n
                             |apply (bool_elim ? (p n3));intro
                                [rewrite > true_to_pi_p_Sn
                                   [rewrite > (times_n_O O);apply lt_times
                                      [elim (H n3);assumption
                                      |assumption]
                                   |assumption]
                                |rewrite > false_to_pi_p_Sn;assumption]]]]
                    |assumption
                    |(*già usata 2 volte: fattorizzare*)
                     elim n
                       [simplify;apply le_n
                       |apply (bool_elim ? (p n2));intro
                          [rewrite > true_to_pi_p_Sn
                             [rewrite > (times_n_O O);apply lt_times
                                [elim (H n2);assumption
                                |assumption]
                             |assumption]
                          |rewrite > false_to_pi_p_Sn;assumption]]]
                 |assumption]
              |assumption]
           |assumption]
        |assumption]
     |intro;rewrite > (false_to_pi_p_Sn ? ? ? H2);
      rewrite > (false_to_pi_p_Sn ? ? ? H2);rewrite > (false_to_pi_p_Sn ? ? ? H2);
      assumption]]
qed.

lemma divides_times_to_divides_div : \forall a,b,c.O < b \to 
                                    a*b \divides c \to a \divides c/b.
intros;elim H1;rewrite > H2;rewrite > sym_times in \vdash (? ? (? (? % ?) ?));
rewrite > assoc_times;cases H;rewrite > div_times;rewrite > times_n_SO in \vdash (? % ?);
apply divides_times
  [1,3:apply divides_n_n
  |*:apply divides_SO_n]
qed.

lemma neper_sigma_p2 : \forall n,a.O < n \to n \divides a \to
sigma_p (S n) (\lambda x.true) (\lambda k.((bc n k)*(exp a n)*(exp n (n-k)))/(exp n n))
= sigma_p (S n) (\lambda x.true) 
(\lambda k.(exp a (n-k))*(pi_p k (\lambda y.true) (\lambda i.a - (a*i/n)))/k!).
intros;apply eq_sigma_p;intros;
  [reflexivity
  |transitivity (bc n x*exp a n/exp n x)
     [rewrite > minus_n_O in ⊢ (? ? (? ? (? ? %)) ?);
      rewrite > (minus_n_n x);
      rewrite < (eq_plus_minus_minus_minus n x x);
        [rewrite > exp_plus_times;
         rewrite > sym_times;rewrite > sym_times in \vdash (? ? (? ? %) ?);
         rewrite < sym_times;
         rewrite < sym_times in ⊢ (? ? (? ? %) ?);
         rewrite < lt_to_lt_to_eq_div_div_times_times;
           [reflexivity
           |*:apply lt_O_exp;assumption]
        |apply le_n
        |apply le_S_S_to_le;assumption]
     |rewrite > minus_n_O in ⊢ (? ? (? (? ? (? ? %)) ?) ?);
      rewrite > (minus_n_n x);
      rewrite < (eq_plus_minus_minus_minus n x x);
        [rewrite > exp_plus_times;
         unfold bc;
         elim (bc2 n x)
           [rewrite > H3;cut (x!*n1 = pi_p x (\lambda i.true) (\lambda i.(n - i)))
              [rewrite > sym_times in ⊢ (? ? (? (? (? (? % ?) ?) ?) ?) ?);
               rewrite > assoc_times;
               rewrite < sym_times in ⊢ (? ? (? (? (? % ?) ?) ?) ?);
               rewrite < lt_to_lt_to_eq_div_div_times_times;
                 [rewrite > Hcut;rewrite < assoc_times;
                  cut (pi_p x (λi:nat.true) (λi:nat.n-i)/x!*(a)\sup(x)
                    = pi_p x (λi:nat.true) (λi:nat.(n-i))*pi_p x (\lambda i.true) (\lambda i.a)/x!)
                    [rewrite > Hcut1;rewrite < times_pi_p;
                     rewrite > divides_times_to_eq in \vdash (? ? % ?);
                       [rewrite > eq_div_div_div_times;
                          [rewrite > sym_times in ⊢ (? ? (? (? ? %) ?) ?);
                           rewrite < eq_div_div_div_times;
                             [cut (exp n x = pi_p x (\lambda i.true) (\lambda i.n))
                                [rewrite > Hcut2;rewrite > divides_pi_p_to_eq
                                   [rewrite > sym_times in \vdash (? ? ? %);
                                    rewrite > divides_times_to_eq in \vdash (? ? ? %);
                                      [apply eq_f2
                                         [apply eq_f2
                                            [apply eq_pi_p;intros
                                               [reflexivity
                                               |rewrite > sym_times;
                                                rewrite > distr_times_minus;elim H1;
                                                rewrite > H5;(* in ⊢ (? ? (? (? ? (? % ?)) ?) ?);*)
                                                rewrite > sym_times;rewrite > assoc_times;
                                                rewrite < distr_times_minus;
                                                generalize in match H;cases n;intros
                                                  [elim (not_le_Sn_O ? H6)
                                                  |do 2 rewrite > div_times;reflexivity]]
                                            |reflexivity]
                                         |reflexivity]
                                      |apply lt_O_fact
                                      |cut (pi_p x (λy:nat.true) (λi:nat.a-a*i/n) = (exp a x)/(exp n x)*(n!/(n-x)!))
                                         [rewrite > Hcut3;rewrite > times_n_SO;
                                          rewrite > sym_times;apply divides_times
                                            [apply divides_SO_n;
                                            |apply divides_times_to_divides_div;
                                               [apply lt_O_fact
                                               |apply bc2;apply le_S_S_to_le;assumption]]
                                         |cut (pi_p x (\lambda y.true) (\lambda i. a - a*i/n) =
                                              pi_p x (\lambda y.true) (\lambda i. a*(n-i)/n))
                                            [rewrite > Hcut3;
                                             rewrite < (divides_pi_p_to_eq ? ? (\lambda i.(a*(n-i))) (\lambda i.n))
                                               [rewrite > (times_pi_p ? ? (\lambda i.a) (\lambda i.(n-i)));
                                                rewrite > divides_times_to_eq;
                                                  [apply eq_f2
                                                     [apply eq_f2;rewrite < eq_exp_pi_p;reflexivity
                                                     |rewrite < Hcut;rewrite > H3;
                                                      rewrite < sym_times in ⊢ (? ? ? (? (? % ?) ?));
                                                      rewrite > (S_pred ((n-x)!));
                                                        [rewrite > assoc_times;
                                                         rewrite > div_times;reflexivity
                                                        |apply lt_O_fact]]
                                                  |unfold lt;cut (1 = pi_p x (\lambda y.true) (\lambda y.1))
                                                     [rewrite > Hcut4;apply le_pi_p;intros;assumption
                                                     |elim x
                                                        [simplify;reflexivity
                                                        |rewrite > true_to_pi_p_Sn;
                                                           [rewrite < H4;reflexivity
                                                           |reflexivity]]]
                                                  |elim x
                                                     [simplify;apply divides_SO_n
                                                     |rewrite > true_to_pi_p_Sn
                                                        [rewrite > true_to_pi_p_Sn
                                                           [apply divides_times;assumption
                                                           |reflexivity]
                                                        |reflexivity]]]
                                               |intros;split
                                                  [assumption
                                                  |rewrite > times_n_SO;apply divides_times
                                                     [assumption
                                                     |apply divides_SO_n]]]
                                            |apply eq_pi_p;intros;
                                               [reflexivity
                                               |elim H1;rewrite > H5;rewrite > (S_pred n);
                                                  [rewrite > assoc_times;
                                                   rewrite > assoc_times;
                                                   rewrite > div_times;
                                                   rewrite > div_times;
                                                   rewrite > distr_times_minus;
                                                   rewrite > sym_times;
                                                   reflexivity
                                                  |assumption]]]]]
                                   |intros;split
                                      [assumption
                                      |rewrite > sym_times;rewrite > times_n_SO;
                                       apply divides_times
                                         [assumption
                                         |apply divides_SO_n]]]
                                |rewrite < eq_exp_pi_p;reflexivity]
                             |apply lt_O_exp;assumption
                             |apply lt_O_fact]
                          |apply lt_O_fact
                          |apply lt_O_exp;assumption]
                       |apply lt_O_exp;assumption
                       |rewrite > (times_pi_p ? ? (\lambda x.(n-x)) (\lambda x.a));
                        rewrite > divides_times_to_eq
                          [rewrite > times_n_SO;rewrite > sym_times;apply divides_times
                             [apply divides_SO_n
                             |elim x
                                [simplify;apply divides_SO_n
                                |change in \vdash (? % ?) with (n*(exp n n2));
                                 rewrite > true_to_pi_p_Sn
                                   [apply divides_times;assumption
                                   |reflexivity]]]
                          |apply lt_O_fact
                          |apply (witness ? ? n1);symmetry;assumption]]
                    |rewrite > divides_times_to_eq;
                       [apply eq_f2
                          [reflexivity
                          |elim x
                             [simplify;reflexivity
                             |change in \vdash (? ? % ?) with (a*(exp a n2));
                              rewrite > true_to_pi_p_Sn
                                [apply eq_f2
                                   [reflexivity
                                   |assumption]
                                |reflexivity]]]
                       |apply lt_O_fact
                       |apply (witness ? ? n1);symmetry;assumption]]
                 |apply lt_O_fact
                 |apply lt_O_fact]
              |apply (inj_times_r (pred ((n-x)!)));
               rewrite < (S_pred ((n-x)!))
                 [rewrite < assoc_times;rewrite < sym_times in \vdash (? ? (? % ?) ?);
                  rewrite < H3;generalize in match H2; elim x
                    [rewrite < minus_n_O;simplify;rewrite < times_n_SO;reflexivity
                    |rewrite < fact_minus in H4;
                       [rewrite > true_to_pi_p_Sn
                          [rewrite < assoc_times;rewrite > sym_times in \vdash (? ? ? (? % ?));
                           apply H4;apply lt_to_le;assumption
                          |reflexivity]
                       |apply le_S_S_to_le;assumption]]
                 |apply lt_O_fact]]
           |apply le_S_S_to_le;assumption]
        |apply le_n
        |apply le_S_S_to_le;assumption]]]
qed.

lemma divides_sigma_p_to_eq : \forall k,p,f,b.O < b \to 
 (\forall x.p x = true \to b \divides f x) \to
 (sigma_p k p f)/b = sigma_p k p (\lambda x. (f x)/b).
intros;cut (\forall k1.b \divides sigma_p k1 p f)
  [|intro;elim k1
     [simplify;apply (witness ? ? O);rewrite < times_n_O;reflexivity
     |apply (bool_elim ? (p n));intro
        [rewrite > true_to_sigma_p_Sn;
           [elim (H1 n);
              [elim H2;rewrite > H4;rewrite > H5;rewrite < distr_times_plus;
               rewrite > times_n_SO in \vdash (? % ?);apply divides_times
                 [apply divides_n_n
                 |apply divides_SO_n]
              |assumption]
           |assumption]
        |rewrite > false_to_sigma_p_Sn;assumption]]]
elim k
  [cases H;simplify;reflexivity
  |apply (bool_elim ? (p n));intro
     [rewrite > true_to_sigma_p_Sn
        [rewrite > true_to_sigma_p_Sn
           [elim (H1 n);
              [elim (Hcut n);rewrite > H4;rewrite > H5;rewrite < distr_times_plus;
               rewrite < H2;rewrite > H5;cases H;do 3 rewrite > div_times;
               reflexivity
              |assumption]
           |assumption]
        |assumption]
     |do 2 try rewrite > false_to_sigma_p_Sn;assumption]]
qed.

lemma neper_sigma_p3 : \forall a,n.O < a \to O < n \to n \divides a \to (exp (S n) n)/(exp n n) =
sigma_p (S n) (\lambda x.true) 
(\lambda k.(exp a (n-k))*(pi_p k (\lambda y.true) (\lambda i.a - (a*i/n)))/k!)/(exp a n).
intros;transitivity ((exp a n)*(exp (S n) n)/(exp n n)/(exp a n))
  [rewrite > eq_div_div_div_times
     [rewrite < sym_times; rewrite < lt_to_lt_to_eq_div_div_times_times;
        [reflexivity
        |apply lt_O_exp;assumption
        |apply lt_O_exp;assumption]
     |apply lt_O_exp;assumption
     |apply lt_O_exp;assumption]
  |apply eq_f2;
     [rewrite > times_exp;rewrite > neper_sigma_p1
        [transitivity (sigma_p (S n) (λx:nat.true) (λk:nat.bc n k*(a)\sup(n)*(exp n (n-k))/(exp n n)))
           [elim H2;rewrite > H3;rewrite < times_exp;rewrite > sym_times in ⊢ (? ? (? (? ? ? (λ_:?.? ? %)) ?) ?);
            rewrite > sym_times in ⊢ (? ? ? (? ? ? (λ_:?.? (? (? ? %) ?) ?)));
            transitivity (sigma_p (S n) (λx:nat.true)
(λk:nat.(exp n n)*(bc n k*(n)\sup(n-k)*(n1)\sup(n)))/exp n n)
              [apply eq_f2
                 [apply eq_sigma_p;intros;
                    [reflexivity
                    |rewrite < assoc_times;rewrite > sym_times;reflexivity]
                 |reflexivity]
              |rewrite < (distributive_times_plus_sigma_p ? ? ? (\lambda k.bc n k*(exp n (n-k))*(exp n1 n)));
               transitivity (sigma_p (S n) (λx:nat.true)
                (λk:nat.bc n k*(n1)\sup(n)*(n)\sup(n-k)))
                 [rewrite > (S_pred (exp n n))
                    [rewrite > div_times;apply eq_sigma_p;intros
                       [reflexivity
                       |rewrite > sym_times;rewrite > sym_times in ⊢ (? ? ? (? % ?));
                        rewrite > assoc_times in \vdash (? ? ? %);reflexivity]
                    |apply lt_O_exp;assumption]
                 |apply eq_sigma_p;intros
                    [reflexivity
                    |rewrite < assoc_times;rewrite > assoc_times in \vdash (? ? ? %);
                     rewrite > sym_times in \vdash (? ? ? (? (? ? %) ?));
                     rewrite < assoc_times;rewrite > sym_times in \vdash (? ? ? %);
                     rewrite > (S_pred (exp n n))
                       [rewrite > div_times;reflexivity
                       |apply lt_O_exp;assumption]]]]
           |rewrite > neper_sigma_p2;
              [reflexivity
              |assumption
              |assumption]]
        |assumption]
     |reflexivity]]
qed.

theorem neper_monotonic : \forall n. O < n \to
(exp (S n) n)/(exp n n) \leq (exp (S (S n)) (S n))/(exp (S n) (S n)).
intros;rewrite > (neper_sigma_p3 (n*S n) n)
  [rewrite > (neper_sigma_p3 (n*S n) (S n))
     [change in ⊢ (? ? (? ? %)) with ((n * S n)*(exp (n * S n) n));
      rewrite < eq_div_div_div_times
        [apply monotonic_div;
           [apply lt_O_exp;rewrite > (times_n_O O);apply lt_times
              [assumption
              |apply lt_O_S]
           |apply le_times_to_le_div
              [rewrite > (times_n_O O);apply lt_times
                 [assumption
                 |apply lt_O_S]
              |rewrite > distributive_times_plus_sigma_p;
               apply (trans_le ? (sigma_p (S n) (λx:nat.true)
                 (λk:nat.((n*S n))\sup(S n-k)*pi_p k (λy:nat.true) (λi:nat.n*S n-n*S n*i/S n)/k!)))
                 [apply le_sigma_p;intros;rewrite > sym_times in ⊢ (? (? ? %) ?);
                  rewrite > sym_times in \vdash (? ? (? % ?));
                  rewrite > divides_times_to_eq in \vdash (? ? %)
                    [rewrite > divides_times_to_eq in \vdash (? % ?)
                       [rewrite > sym_times in \vdash (? (? ? %) ?);
                        rewrite < assoc_times;
                        rewrite > sym_times in \vdash (? ? %);
                        rewrite > minus_Sn_m;
                          [apply le_times_r;apply monotonic_div
                             [apply lt_O_fact
                             |apply le_pi_p;intros;apply monotonic_le_minus_r;
                              rewrite > assoc_times in \vdash (? % ?);
                              rewrite > sym_times in \vdash (? % ?);
                              rewrite > assoc_times in \vdash (? % ?);
                              rewrite > div_times;
                              rewrite > (S_pred n) in \vdash (? ? %);
                                [rewrite > assoc_times;rewrite > div_times;
                                 rewrite < S_pred
                                   [rewrite > sym_times;apply le_times_l;apply le_S;apply le_n
                                   |assumption]
                                |assumption]]
                          |apply le_S_S_to_le;assumption]
                       |apply lt_O_fact
                       |cut (pi_p i (λy:nat.true) (λi:nat.n*S n-n*S n*i/n) = 
                             pi_p i (\lambda y.true) (\lambda i.S n) *
                             pi_p i (\lambda y.true) (\lambda i.(n-i)))
                          [rewrite > Hcut;rewrite > times_n_SO;
                           rewrite > sym_times;apply divides_times
                             [apply divides_SO_n
                             |elim (bc2 n i);
                                [apply (witness ? ? n1);
                                 cut (pi_p i (\lambda y.true) (\lambda i.n-i) = (n!/(n-i)!))
                                   [rewrite > Hcut1;rewrite > H3;rewrite > sym_times in ⊢ (? ? (? (? % ?) ?) ?);
                                    rewrite > (S_pred ((n-i)!))
                                      [rewrite > assoc_times;rewrite > div_times;
                                       reflexivity
                                      |apply lt_O_fact]
                                   |generalize in match H1;elim i
                                      [rewrite < minus_n_O;rewrite > div_n_n;
                                         [reflexivity
                                         |apply lt_O_fact]
                                      |rewrite > true_to_pi_p_Sn
                                         [rewrite > H4
                                            [rewrite > sym_times;rewrite < divides_times_to_eq
                                               [rewrite < fact_minus
                                                  [rewrite > sym_times in ⊢ (? ? (? ? %) ?);
                                                   rewrite < lt_to_lt_to_eq_div_div_times_times;
                                                     [reflexivity
                                                     |apply lt_to_lt_O_minus;apply le_S_S_to_le;
                                                      assumption
                                                     |apply lt_O_fact;]
                                                  |apply le_S_S_to_le;assumption]
                                               |apply lt_O_fact
                                               |apply divides_fact_fact;
                                                apply le_plus_to_minus;
                                                rewrite > plus_n_O in \vdash (? % ?);
                                                apply le_plus_r;apply le_O_n]
                                            |apply lt_to_le;assumption]
                                         |reflexivity]]]
                                |apply le_S_S_to_le;assumption]]
                          |rewrite < times_pi_p;apply eq_pi_p;intros;
                             [reflexivity
                             |rewrite > distr_times_minus;rewrite > assoc_times;
                              rewrite > (S_pred n) in \vdash (? ? (? ? (? (? % ?) %)) ?)
                                [rewrite > div_times;rewrite > sym_times;reflexivity
                                |assumption]]]]
                    |apply lt_O_fact
                    |cut (pi_p i (λy:nat.true) (λi:nat.n*S n-n*S n*i/S n) = 
                             pi_p i (\lambda y.true) (\lambda i.n) *
                             pi_p i (\lambda y.true) (\lambda i.(S n-i)))
                          [rewrite > Hcut;rewrite > times_n_SO;rewrite > sym_times;
                           apply divides_times
                             [apply divides_SO_n
                             |elim (bc2 (S n) i);
                                [apply (witness ? ? n1);
                                 cut (pi_p i (\lambda y.true) (\lambda i.S n-i) = ((S n)!/(S n-i)!))
                                   [rewrite > Hcut1;rewrite > H3;rewrite > sym_times in ⊢ (? ? (? (? % ?) ?) ?);
                                    rewrite > (S_pred ((S n-i)!))
                                      [rewrite > assoc_times;rewrite > div_times;
                                       reflexivity
                                      |apply lt_O_fact]
                                   |generalize in match H1;elim i
                                      [rewrite < minus_n_O;rewrite > div_n_n;
                                         [reflexivity
                                         |apply lt_O_fact]
                                      |rewrite > true_to_pi_p_Sn
                                         [rewrite > H4
                                            [rewrite > sym_times;rewrite < divides_times_to_eq
                                               [rewrite < fact_minus
                                                  [rewrite > sym_times in ⊢ (? ? (? ? %) ?);
                                                   rewrite < lt_to_lt_to_eq_div_div_times_times;
                                                     [reflexivity
                                                     |apply lt_to_lt_O_minus;apply lt_to_le;
                                                      assumption
                                                     |apply lt_O_fact]
                                                  |apply lt_to_le;assumption]
                                               |apply lt_O_fact
                                               |apply divides_fact_fact;
                                                apply le_plus_to_minus;
                                                rewrite > plus_n_O in \vdash (? % ?);
                                                apply le_plus_r;apply le_O_n]
                                            |apply lt_to_le;assumption]
                                         |reflexivity]]]
                                |apply lt_to_le;assumption]]
                          |rewrite < times_pi_p;apply eq_pi_p;intros;
                             [reflexivity
                             |rewrite > distr_times_minus;rewrite > sym_times in \vdash (? ? (? ? (? (? % ?) ?)) ?);
                              rewrite > assoc_times;rewrite > div_times;reflexivity]]]
                    |rewrite > true_to_sigma_p_Sn in \vdash (? ? %)
                       [rewrite > sym_plus;rewrite > plus_n_O in \vdash (? % ?);
                        apply le_plus_r;apply le_O_n
                       |reflexivity]]]]
           |rewrite > (times_n_O O);apply lt_times
              [assumption
              |apply lt_O_S]
           |apply lt_O_exp;rewrite > (times_n_O O);apply lt_times
              [assumption
              |apply lt_O_S]]
        |rewrite > (times_n_O O);apply lt_times
           [assumption
           |apply lt_O_S]
        |apply lt_O_S
        |apply (witness ? ? n);apply sym_times]
     |rewrite > (times_n_O O);apply lt_times
        [assumption
        |apply lt_O_S]
     |assumption
     |apply (witness ? ? (S n));reflexivity]
qed.

theorem le_SSO_neper : \forall n.O < n \to (2 \leq (exp (S n) n)/(exp n n)).
intros;elim H
  [simplify;apply le_n
  |apply (trans_le ? ? ? H2);apply neper_monotonic;assumption]
qed.

theorem le_SSO_exp_neper : \forall n.O < n \to 2*(exp n n) \leq exp (S n) n.
intros;apply (trans_le ? ((exp (S n) n)/(exp n n)*(exp n n)))
  [apply le_times_l;apply le_SSO_neper;assumption
  |rewrite > sym_times;apply (trans_le ? ? ? (le_times_div_div_times ? ? ? ?))
     [apply lt_O_exp;assumption
     |cases (lt_O_exp ? n H);rewrite > div_times;apply le_n]]
qed.
                                       
(* theorem le_log_exp_Sn_log_exp_n: \forall n,m,a,p. O < m \to S O < p \to
divides n m \to
log p (exp n m) - log p (exp a m) \le
sigma_p (S n) (\lambda i.leb (S a) i) (\lambda i.S((m/i)*S(log p (S(S(S O)))))).
intros.
elim n
  [rewrite > false_to_sigma_p_Sn.
   simplify.
   apply (lt_O_n_elim ? H).intro.
   simplify.apply le_O_n
  |apply (bool_elim ? (leb a n1));intro
    [rewrite > true_to_sigma_p_Sn
      [apply (trans_le ? (S (m/S n1*S (log p (S(S(S O)))))+(log p ((n1)\sup(m))-log p ((a)\sup(m)))))
        [rewrite > sym_plus. 
         rewrite > plus_minus
          [apply le_plus_to_minus_r.
           rewrite < plus_minus_m_m
            [rewrite > sym_plus.
             apply le_log_exp_Sn_log_exp_n.


* a generalization 
theorem le_exp_sigma_p_exp_m: \forall m,n. (exp (S m) n) \le
sigma_p (S n) (\lambda k.true) (\lambda k.((exp m (n-k))*(exp n k))/(k!)).
intros.
rewrite > exp_S_sigma_p.
apply le_sigma_p.
intros.unfold bc.
apply (trans_le ? ((exp m (n-i))*((n \sup i)/i!)))
  [rewrite > sym_times.
   apply le_times_r.
   rewrite > sym_times.
   rewrite < eq_div_div_div_times
    [apply monotonic_div
      [apply lt_O_fact
      |apply le_times_to_le_div2
        [apply lt_O_fact
        |apply le_fact_exp.
         apply le_S_S_to_le.
         assumption
        ]
      ]
    |apply lt_O_fact
    |apply lt_O_fact
    ]
  |apply le_times_div_div_times.
   apply lt_O_fact
  ]
qed.

theorem lt_exp_sigma_p_exp_m: \forall m,n. S O < n \to
(exp (S m) n) <
sigma_p (S n) (\lambda k.true) (\lambda k.((exp m (n-k))*(exp n k))/(k!)).
intros.
rewrite > exp_S_sigma_p.
apply lt_sigma_p
  [intros.unfold bc.
   apply (trans_le ? ((exp m (n-i))*((n \sup i)/i!)))
    [rewrite > sym_times.
     apply le_times_r.
     rewrite > sym_times.
     rewrite < eq_div_div_div_times
      [apply monotonic_div
        [apply lt_O_fact
        |apply le_times_to_le_div2
          [apply lt_O_fact
          |apply le_fact_exp.
           apply le_S_S_to_le.
           assumption
          ]
        ]
      |apply lt_O_fact
      |apply lt_O_fact
      ]
    |apply le_times_div_div_times.
     apply lt_O_fact
    ]
  |apply (ex_intro ? ? n).
   split
    [split
      [apply le_n
      |reflexivity
      ]
    |rewrite < minus_n_n.
     rewrite > bc_n_n.
     simplify.unfold lt.
     apply le_times_to_le_div
      [apply lt_O_fact
      |rewrite > sym_times.
       rewrite < plus_n_O.
       apply le_fact_exp1.
       assumption
      ]
    ]
  ]
qed.
   
theorem lt_SO_to_lt_exp_Sn_n_SSSO_bof: \forall m,n. S O < n \to 
(exp (S m) n) < (S(S(S O)))*(exp m n).
intros.  
apply (lt_to_le_to_lt ? (sigma_p (S n) (\lambda k.true) (\lambda k.((exp m (n-k))*(exp n k))/(k!))))
  [apply lt_exp_sigma_p_exp_m.assumption
  |apply (trans_le ? (sigma_p (S n) (\lambda i.true) (\lambda i.(exp n n)/(exp (S(S O)) (pred i)))))
    [apply le_sigma_p.intros.
     apply le_times_to_le_div
      [apply lt_O_exp.
       apply lt_O_S
      |apply (trans_le ? ((S(S O))\sup (pred i)* n \sup n/i!))
        [apply le_times_div_div_times.
         apply lt_O_fact
        |apply le_times_to_le_div2
          [apply lt_O_fact
          |rewrite < sym_times.
           apply le_times_r.
           apply le_exp_SSO_fact
          ]
        ]
      ]
    |rewrite > eq_sigma_p_pred
      [rewrite > div_SO.
       rewrite > sym_plus.
       change in ⊢ (? ? %) with ((exp n n)+(S(S O)*(exp n n))).
       apply le_plus_r.
       apply (trans_le ? (((S(S O))*(exp n n)*(exp (S(S O)) n) - (S(S O))*(exp n n))/(exp (S(S O)) n)))
        [apply sigma_p_div_exp
        |apply le_times_to_le_div2
          [apply lt_O_exp.
           apply lt_O_S.
          |apply le_minus_m
          ]
        ]
      |reflexivity
      ]
    ]
  ]
qed.     
*)
