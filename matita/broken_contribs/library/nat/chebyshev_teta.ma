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

include "nat/binomial.ma".
include "nat/pi_p.ma".

(* This is chebishev teta function *)

definition teta: nat \to nat \def
\lambda n. pi_p (S n) primeb (\lambda p.p).

theorem lt_O_teta: \forall n. O < teta n.
intros.elim n
  [apply le_n
  |unfold teta.apply (bool_elim ? (primeb (S n1)));intro 
    [rewrite > true_to_pi_p_Sn
      [rewrite > (times_n_O O).
       apply lt_times
        [apply lt_O_S
        |assumption
        ]
      |assumption
      ]
    |rewrite > false_to_pi_p_Sn;assumption
    ]
  ]
qed.

definition M \def \lambda m.bc (S(2*m)) m.

theorem lt_M: \forall m. O < m \to M m < exp 2 (2*m).
intros.
apply (lt_times_to_lt 2)
  [apply lt_O_S
  |change in ⊢ (? ? %) with (exp 2 (S(2*m))).
   change in ⊢ (? ? (? % ?)) with (1+1).
   rewrite > exp_plus_sigma_p.
   apply (le_to_lt_to_lt ? (sigma_p (S (S (2*m))) (λk:nat.orb (eqb k m) (eqb k (S m)))
            (λk:nat.bc (S (2*m)) k*(1)\sup(S (2*m)-k)*(1)\sup(k))))
    [rewrite > (sigma_p_gi ? ? m)
      [rewrite > (sigma_p_gi ? ? (S m))
        [rewrite > (false_to_eq_sigma_p O (S(S(2*m))))
          [simplify in ⊢ (? ? (? ? (? ? %))).
           simplify in ⊢ (? % ?).
           rewrite < exp_SO_n.rewrite < exp_SO_n.
           rewrite < exp_SO_n.rewrite < exp_SO_n.
           rewrite < times_n_SO.rewrite < times_n_SO.
           rewrite < times_n_SO.rewrite < times_n_SO.
           apply le_plus
            [unfold M.apply le_n
            |apply le_plus_l.unfold M.
             change in \vdash (? ? %) with (fact (S(2*m))/(fact (S m)*(fact ((2*m)-m)))).
             simplify in \vdash (? ? (? ? (? ? (? (? % ?))))).
             rewrite < plus_n_O.rewrite < minus_plus_m_m.
             rewrite < sym_times in \vdash (? ? (? ? %)).
             change in \vdash (? % ?) with (fact (S(2*m))/(fact m*(fact (S(2*m)-m)))).
             simplify in \vdash (? (? ? (? ? (? (? (? %) ?)))) ?).
             rewrite < plus_n_O.change in \vdash (? (? ? (? ? (? (? % ?)))) ?) with (S m + m).
             rewrite < minus_plus_m_m.
             apply le_n
            ]
          |apply le_O_n
          |intros.
           elim (eqb i m);elim (eqb i (S m));reflexivity
          ]
        |apply le_S_S.apply le_S_S.
         apply le_times_n.
         apply le_n_Sn
        |rewrite > (eq_to_eqb_true ? ? (refl_eq ? (S m))).
         rewrite > (not_eq_to_eqb_false (S m) m)
          [reflexivity
          |intro.apply (not_eq_n_Sn m).
           apply sym_eq.assumption
          ]
        ]
      |apply le_S.apply le_S_S.
       apply le_times_n.
       apply le_n_Sn
      |rewrite > (eq_to_eqb_true ? ? (refl_eq ? (S m))).
       reflexivity
      ]
    |rewrite > (bool_to_nat_to_eq_sigma_p (S(S(2*m))) ? (\lambda k.true) ? 
      (\lambda k.bool_to_nat (eqb k m\lor eqb k (S m))*(bc (S (2*m)) k*(1)\sup(S (2*m)-k)*(1)\sup(k))))
     in \vdash (? % ?)
      [apply lt_sigma_p
        [intros.elim (eqb i m\lor eqb i (S m))
          [rewrite > sym_times.rewrite < times_n_SO.apply le_n
          |apply le_O_n
          ]
        |apply (ex_intro ? ? O).
         split
          [split[apply lt_O_S|reflexivity]
          |rewrite > (not_eq_to_eqb_false ? ? (not_eq_O_S m)).
           rewrite > (not_eq_to_eqb_false ? ? (lt_to_not_eq ? ? H)).
           simplify in \vdash (? % ?).
           rewrite < exp_SO_n.rewrite < exp_SO_n.
           rewrite > bc_n_O.simplify.
           apply le_n
          ]
        ]
      |intros.rewrite > sym_times in \vdash (? ? ? %).
       rewrite < times_n_SO.
       reflexivity
      ]
    ]
  ]
qed.
      
theorem divides_fact_to_divides: \forall p,n. prime p \to divides p n! \to 
\exists m.O < m \land m \le n \land divides p m.  
intros 3.elim n
  [apply False_ind.elim H.
   apply (lt_to_not_le ? ? H2).
   apply divides_to_le[apply le_n|assumption]
  |rewrite > factS in H2.
   elim (divides_times_to_divides ? ? ? H H2)
    [apply (ex_intro ? ? (S n1)).split
      [split
        [apply lt_O_S
        |apply le_n
        ]
      |assumption
      ]
    |elim (H1 H3).elim H4.elim H5.
     apply (ex_intro ? ? a).split
      [split
        [assumption
        |apply le_S.assumption
        ]
      |assumption
      ]
    ]
  ]
qed.
      
theorem divides_fact_to_le: \forall p,n. prime p \to divides p n! \to 
p \le n.  
intros.
elim (divides_fact_to_divides p n H H1).
elim H2.elim H3.
apply (trans_le ? a)
  [apply divides_to_le;assumption
  |assumption
  ]
qed.
     
theorem prime_to_divides_M: \forall m,p. prime p \to S m < p \to p \le S(2*m) \to
divides p (M m).      
intros.unfold M.
elim (bc2 (S(2*m)) m)
  [unfold bc.rewrite > H3.
   rewrite > sym_times.
   rewrite > lt_O_to_div_times
    [elim (divides_times_to_divides p (m!*(S (2*m)-m)!) n1)
      [apply False_ind.
       elim (divides_times_to_divides p (m!) (S (2*m)-m)!)
        [apply (lt_to_not_le ? ? (lt_to_le ? ? H1)).
         apply divides_fact_to_le;assumption
        |apply (lt_to_not_le ? ? H1).
         apply divides_fact_to_le
          [assumption
          |cut (S m = S(2*m)-m)
            [rewrite > Hcut.assumption
            |simplify in ⊢ (? ? ? (? (? %) ?)).
             rewrite < plus_n_O.
             change in ⊢ (? ? ? (? % ?)) with (S m + m).
             apply minus_plus_m_m
            ]
          ]
        |assumption
        |assumption
        ]
      |assumption
      |assumption
      |rewrite < H3.
       apply divides_fact
        [apply prime_to_lt_O.assumption
        |assumption
        ]
      ]
    |rewrite > (times_n_O O).
     apply lt_times;apply lt_O_fact
    ]
  |simplify in ⊢ (? ? (? %)).
   rewrite < plus_n_O.
   change in ⊢ (? ? %) with (S m + m).
   apply le_plus_n
  ]
qed.
             
theorem divides_pi_p_M1: \forall m.\forall i. i \le (S(S(2*m))) \to 
divides (pi_p i (\lambda p.leb (S(S m)) p \land primeb p)(\lambda p.p)) (M m).
intros 2.
elim i
  [simplify.apply (witness ? ? (M m)).rewrite > sym_times.apply times_n_SO
  |apply (bool_elim ? (leb (S (S m)) n \land primeb n));intro
    [rewrite > true_to_pi_p_Sn
      [apply divides_to_divides_times
        [apply primeb_true_to_prime.
         apply (andb_true_true_r ? ? H2).
        |cut (\forall p.prime p \to n \le p \to ¬p∣pi_p n (λp:nat.leb (S (S m)) p∧primeb p) (λp:nat.p))
          [apply Hcut
            [apply primeb_true_to_prime.
             apply (andb_true_true_r ? ? H2)
            |apply le_n
            ]
          |intros 2.
           elim n
            [simplify.intro.elim H3.apply (lt_to_not_le ? ? H6).
             apply divides_to_le
              [apply le_n
              |assumption
              ]
            |apply (bool_elim ? (leb (S (S m)) n1∧primeb n1));intro
              [rewrite > true_to_pi_p_Sn
                [intro.elim (divides_times_to_divides ? ? ? H3 H7)
                  [apply (le_to_not_lt ? ? H5).
                   apply le_S_S.
                   apply divides_to_le
                    [apply prime_to_lt_O.
                     apply primeb_true_to_prime.
                     apply (andb_true_true_r ? ? H6)
                    |assumption
                    ]
                  |apply H4
                    [apply lt_to_le.assumption
                    |assumption
                    ]
                  ]
                |assumption
                ]
              |rewrite > false_to_pi_p_Sn
                [apply H4.
                 apply lt_to_le.assumption
                |assumption
                ]
              ]
            ]
          ]
        |apply prime_to_divides_M
          [apply primeb_true_to_prime.
           apply (andb_true_true_r ? ? H2)
          |apply leb_true_to_le.
           apply (andb_true_true ? ? H2)
          |apply le_S_S_to_le.assumption
          ]
        |apply H.
         apply lt_to_le.
         assumption
        ]
      |assumption
      ]
    |rewrite > false_to_pi_p_Sn
      [apply H.
       apply lt_to_le.
       assumption
      |assumption
      ]
    ]
  ]
qed.

theorem divides_pi_p_M:\forall m.
divides (pi_p (S(S(2*m))) (\lambda p.leb (S(S m)) p \land primeb p)(\lambda p.p)) (M m).
intros. 
apply divides_pi_p_M1.
apply le_n.
qed.  

theorem teta_pi_p_teta: \forall m. teta (S (2*m))
=pi_p (S (S (2*m))) (λp:nat.leb (S (S m)) p∧primeb p) (λp:nat.p)*teta (S m).
intro.unfold teta.
rewrite > (eq_pi_p1 ? (\lambda p.leb p (S m) \land primeb p) ? (\lambda p.p) (S(S m)))
  [rewrite < (false_to_eq_pi_p (S(S m)) (S(S(2*m))))
    [generalize in match (S(S(2*m))).intro.
     elim n
      [simplify.reflexivity
      |apply (bool_elim ? (primeb n1));intro
        [rewrite > true_to_pi_p_Sn
          [apply (bool_elim ? (leb n1 (S m))); intro
            [rewrite > false_to_pi_p_Sn
              [rewrite > true_to_pi_p_Sn
                [rewrite < assoc_times.
                 rewrite > sym_times in ⊢ (? ? ? (? % ?)).
                 rewrite > assoc_times.
                 apply eq_f.
                 assumption
                |apply true_to_true_to_andb_true;assumption
                ]
              |rewrite > lt_to_leb_false
                [reflexivity
                |apply le_S_S.
                 apply leb_true_to_le.
                 assumption
                ]
              ]
            |rewrite > true_to_pi_p_Sn
              [rewrite > false_to_pi_p_Sn
                [rewrite > assoc_times.
                 apply eq_f.
                 assumption
                |rewrite > H2.reflexivity
                ]
              |rewrite > H1.
               rewrite > le_to_leb_true
                [reflexivity
                |apply not_le_to_lt.
                 apply leb_false_to_not_le.
                 assumption
                ]
              ]
            ]
          |assumption 
          ]
        |rewrite > false_to_pi_p_Sn
          [rewrite > false_to_pi_p_Sn
            [rewrite > false_to_pi_p_Sn
              [assumption
              |rewrite > H1.
               rewrite > andb_sym.
               reflexivity
              ]
            |rewrite > H1.
             rewrite > andb_sym.
             reflexivity
            ]
          |assumption
          ]
        ]
      ]
    |apply le_S_S.apply le_S_S.
     apply le_times_n.
     apply le_n_Sn
    |intros.
     rewrite > lt_to_leb_false
      [reflexivity
      |assumption
      ]
    ]
  |intros.
   rewrite > le_to_leb_true
    [reflexivity
    |apply le_S_S_to_le.
     assumption
    ]
  |intros.reflexivity
  ]
qed.                  

theorem div_teta_teta: \forall m. 
teta (S(2*m))/teta (S m) = pi_p (S(S(2*m))) (\lambda p.leb (S(S m)) p \land primeb p)(\lambda p.p).
intros.apply (div_mod_spec_to_eq ? ? ? ? ? O (div_mod_spec_div_mod ? ? ? ))
  [apply lt_O_teta
  |apply div_mod_spec_intro
    [apply lt_O_teta
    |rewrite < plus_n_O.
     apply teta_pi_p_teta
    ]
  ]
qed.
                     
theorem le_teta_M_teta: \forall m. 
teta (S(2*m)) \le (M m)*teta (S m).  
intro.
rewrite > teta_pi_p_teta. 
apply le_times_l.
apply divides_to_le
  [unfold M.apply lt_O_bc.apply lt_to_le.
   apply le_S_S.apply le_times_n.
   apply le_n_Sn
  |apply divides_pi_p_M
  ]
qed.

theorem lt_O_to_le_teta_exp_teta: \forall m. O < m\to
teta (S(2*m)) < exp 2 (2*m)*teta (S m). 
intros. 
apply (le_to_lt_to_lt ? (M m*teta (S m)))
  [apply le_teta_M_teta
  |apply lt_times_l1
    [apply lt_O_teta
    |apply lt_M.
     assumption
    ]
  ]
qed.

theorem teta_pred: \forall n. S O < n \to teta (2*n) = teta (pred (2*n)).
intros.unfold teta.
rewrite > false_to_pi_p_Sn
  [rewrite < S_pred
    [reflexivity
    |rewrite > (times_n_O 2) in ⊢ (? % ?).
     apply lt_times_r.
     apply lt_to_le.assumption
    ]
  |apply not_prime_to_primeb_false.
   intro.
   elim H1.
   apply (lt_to_not_eq ? ? H).
   apply (injective_times_r 1).
   rewrite < times_n_SO.
   apply H3
    [apply (witness ? ? n).reflexivity
    |apply le_n
    ]
  ]
qed.
  
theorem le_teta: \forall m.teta m \le exp 2 (2*m).
intro.apply (nat_elim1 m).intros.
elim (or_eq_eq_S m1).
elim H1
  [rewrite > H2.
   generalize in match H2.
   cases a
    [intro.apply le_n
    |cases n;intros
      [apply leb_true_to_le.reflexivity
      |rewrite > teta_pred
        [rewrite > times_SSO.
         change in ⊢ (? (? %) ?) with (S (2*S n1)).
         apply (trans_le ? (exp 2 (2*(S n1))*teta (S (S n1))))
          [apply lt_to_le.
           apply lt_O_to_le_teta_exp_teta.
           apply lt_O_S
          |rewrite < times_SSO.
           change in ⊢ (? ? (? ? %)) with ((2*S (S n1))+((2*S (S n1)) + O)).
           rewrite < plus_n_O.
           rewrite > exp_plus_times.
           apply le_times
            [apply le_exp
              [apply lt_O_S
              |apply le_times_r.
               apply le_n_Sn
              ]
            |apply H.
             rewrite > H3. 
             apply lt_m_nm
              [apply lt_O_S
              |apply le_n
              ]
            ]
          ]
        |apply le_S_S.apply lt_O_S
        ]
      ]
    ]
  |rewrite > H2.
   generalize in match H2.
   cases a;intro
    [apply leb_true_to_le.reflexivity
    |apply (trans_le ? (exp 2 (2*(S n))*teta (S (S n))))
      [apply lt_to_le.
       apply lt_O_to_le_teta_exp_teta.
       apply lt_O_S
      |change in ⊢ (? ? (? ? %)) with (S (2*S n) + (S (2*S n) +O)).
       rewrite < plus_n_O.
       rewrite < plus_n_Sm.
       rewrite < sym_plus.
       rewrite > plus_n_Sm.
       rewrite > exp_plus_times.
       apply le_times_r.
       rewrite < times_SSO.
       apply H.
       rewrite > H3.
       apply le_S_S.
       apply lt_m_nm
        [apply lt_O_S
        |apply le_n
        ]
      ]
    ]
  ]
qed.
   
(*             
alias id "sqrt" = "cic:/matita/nat/sqrt/sqrt.con".
alias id "not" = "cic:/matita/logic/connectives/Not.con".
theorem absurd_bound: \forall n. exp 2 7 \le n \to 
(\forall p. n < p \to p < 2*n \to not (prime p)) \to
bc (2*n) n < exp (2*n) (div (sqrt (2*n)) 2 - 1)*exp 4 (div (2*n) 3).
intros.
cut (O < n)
  [cut (sqrt (2*n) < div (2*n) 3)
    [
  |
*)
             
