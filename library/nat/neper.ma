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
  |apply (O_lt_times_to_O_lt ? n2).
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
                 [rewrite > Hcut;apply monotonic_exp1;constructor 2;
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