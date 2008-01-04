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



include "nat/log.ma".
include "nat/pi_p.ma".
include "nat/factorization.ma".
include "nat/factorial2.ma".

definition prim: nat \to nat \def
\lambda n. sigma_p (S n) primeb (\lambda p.(S O)).

(* This is chebishev psi funcion *)
definition A: nat \to nat \def
\lambda n. pi_p (S n) primeb (\lambda p.exp p (log p n)).

theorem le_Al1: \forall n.
A n \le pi_p (S n) primeb (\lambda p.n).
intro.unfold A.
cases n
  [simplify.apply le_n
  |apply le_pi_p.
   intros.
   apply le_exp_log.
   apply lt_O_S
  ]
qed.

theorem le_Al: \forall n.
A n \le exp n (prim n).
intro.unfold prim.
rewrite < exp_sigma_p.
apply le_Al1.
qed.

theorem leA_r2: \forall n.
exp n (prim n) \le A n * A n.
intro.unfold prim.
elim (le_to_or_lt_eq ? ? (le_O_n n))
  [rewrite < (exp_sigma_p (S n) n primeb).
   unfold A.
   rewrite < times_pi_p.
   apply le_pi_p.
   intros.
   rewrite < exp_plus_times.
   apply (trans_le ? (exp i (S(log i n))))
    [apply lt_to_le.
     apply lt_exp_log.
     apply prime_to_lt_SO.
     apply primeb_true_to_prime.
     assumption
    |apply le_exp
      [apply prime_to_lt_O.
       apply primeb_true_to_prime.
       assumption
      |rewrite > plus_n_O.
       simplify.
       rewrite > plus_n_Sm.
       apply le_plus_r.
       apply lt_O_log
        [assumption
        |apply le_S_S_to_le.
         apply H1
        ]
      ]
    ]
  |rewrite < H. apply le_n
  ]
qed.

(* an equivalent formulation for psi *)
definition A': nat \to nat \def
\lambda n. pi_p (S n) primeb 
  (\lambda p.(pi_p (log p n) (\lambda i.true) (\lambda i.p))).

theorem eq_A_A': \forall n.A n = A' n.
intro.unfold A.unfold A'.
apply eq_pi_p
  [intros.reflexivity
  |intros.
   apply (trans_eq ? ? (exp x (sigma_p (log x n) (λi:nat.true) (λi:nat.(S O)))))
    [apply eq_f.apply sym_eq.apply sigma_p_true
    |apply sym_eq.apply exp_sigma_p
    ]
  ]
qed.

theorem eq_pi_p_primeb_divides_b: \forall n,m.
pi_p n (\lambda p.primeb p \land divides_b p m) (\lambda p.exp p (ord m p))
= pi_p n primeb (\lambda p.exp p (ord m p)).
intro.
elim n
  [reflexivity
  |apply (bool_elim ? (primeb n1));intro
    [rewrite > true_to_pi_p_Sn in ⊢ (? ? ? %)
      [apply (bool_elim ? (divides_b n1 m));intro
        [rewrite > true_to_pi_p_Sn
          [apply eq_f.
           apply H
          |apply true_to_true_to_andb_true;assumption
          ]
        |rewrite > false_to_pi_p_Sn
          [rewrite > not_divides_to_ord_O
            [simplify in ⊢ (? ? ? (? % ?)).
             rewrite > sym_times.
             rewrite < times_n_SO.
             apply H
            |apply primeb_true_to_prime.assumption
            |apply divides_b_false_to_not_divides.
             assumption
            ]
          |rewrite > H1.rewrite > H2.reflexivity
          ]
        ]
      |assumption
      ]
    |rewrite > false_to_pi_p_Sn
      [rewrite > false_to_pi_p_Sn
        [apply H
        |assumption
        ]
      |rewrite > H1.reflexivity
      ]
    ]
  ]
qed.
    
theorem lt_max_to_pi_p_primeb: \forall q,m. O < m \to max m (\lambda i.primeb i \land divides_b i m) < q \to
m = pi_p q (\lambda i.primeb i \land divides_b i m) (\lambda p.exp p (ord m p)).
intro.elim q
  [apply False_ind.
   apply (not_le_Sn_O ? H1)
  |apply (bool_elim ? (primeb n∧divides_b n m));intro
    [rewrite > true_to_pi_p_Sn
      [rewrite > (exp_ord n m) in ⊢ (? ? % ?)
        [apply eq_f.
         rewrite > (H (ord_rem m n))
          [apply eq_pi_p1
            [intros.
             apply (bool_elim ? (primeb x));intro
              [simplify.
               apply (bool_elim ? (divides_b x (ord_rem m n)));intro
                [apply sym_eq.
                 apply divides_to_divides_b_true
                  [apply prime_to_lt_O.
                   apply primeb_true_to_prime.
                   assumption
                  |apply (trans_divides ? (ord_rem m n))
                    [apply divides_b_true_to_divides.
                     assumption
                    |apply divides_ord_rem
                      [apply (trans_lt ? x)
                        [apply prime_to_lt_SO.
                         apply primeb_true_to_prime.
                         assumption
                        |assumption
                        ]
                      |assumption
                      ]
                    ]
                  ]
                |apply sym_eq.
                 apply not_divides_to_divides_b_false
                  [apply prime_to_lt_O.
                   apply primeb_true_to_prime.
                   assumption
                  |apply ord_O_to_not_divides
                    [assumption
                    |apply primeb_true_to_prime.
                     assumption
                    |rewrite < (ord_ord_rem n)
                      [apply not_divides_to_ord_O
                        [apply primeb_true_to_prime.
                         assumption
                        |apply divides_b_false_to_not_divides.
                         assumption
                        ]
                      |assumption
                      |apply primeb_true_to_prime.
                       apply (andb_true_true ? ? H3)
                      |apply primeb_true_to_prime.
                       assumption
                      |assumption
                      ]
                    ]
                  ]
                ]
              |reflexivity
              ]
            |intros.
             apply eq_f.
             apply ord_ord_rem
              [assumption
              |apply primeb_true_to_prime.
               apply (andb_true_true ? ? H3)
              |apply primeb_true_to_prime.
               apply (andb_true_true ? ? H5)
              |assumption
              ]
            ]
          |apply lt_O_ord_rem
            [apply prime_to_lt_SO.
             apply primeb_true_to_prime.
             apply (andb_true_true ? ? H3)
            |assumption
            ]
          |apply not_eq_to_le_to_lt
            [elim (exists_max_forall_false (λi:nat.primeb i∧divides_b i (ord_rem m n)) (ord_rem m n))
              [elim H4.
               intro.rewrite > H7 in H6.simplify in H6.
               apply (not_divides_ord_rem m n)
                [assumption
                |apply prime_to_lt_SO.
                 apply primeb_true_to_prime.
                 apply (andb_true_true ? ? H3)
                |apply divides_b_true_to_divides.
                 apply (andb_true_true_r ? ? H6)
                ]
              |elim H4.rewrite > H6.
               apply lt_to_not_eq.
               apply prime_to_lt_O.
               apply primeb_true_to_prime.
               apply (andb_true_true ? ? H3)
              ]
            |apply (trans_le ? (max m (λi:nat.primeb i∧divides_b i (ord_rem m n))))
              [apply le_to_le_max.
               apply divides_to_le
                [assumption
                |apply divides_ord_rem
                  [apply prime_to_lt_SO.
                   apply primeb_true_to_prime.
                   apply (andb_true_true ? ? H3)
                  |assumption
                  ]
                ]
              |apply (trans_le ? (max m (λi:nat.primeb i∧divides_b i m)))
                [apply le_max_f_max_g.
                 intros.
                 apply (bool_elim ? (primeb i));intro
                  [simplify.
                   apply divides_to_divides_b_true
                    [apply prime_to_lt_O.
                     apply primeb_true_to_prime.
                     assumption
                    |apply (trans_divides ? (ord_rem m n))
                      [apply divides_b_true_to_divides.
                       apply (andb_true_true_r ? ? H5)
                      |apply divides_ord_rem
                        [apply prime_to_lt_SO.
                         apply primeb_true_to_prime.
                         apply (andb_true_true ? ? H3)
                        |assumption
                        ]
                      ]
                    ]
                  |rewrite > H6 in H5.
                   assumption
                  ]
                |apply le_S_S_to_le.
                 assumption
                ]
              ]
            ]
          ]
        |apply prime_to_lt_SO.
         apply primeb_true_to_prime.
         apply (andb_true_true ? ? H3)
        |assumption
        ]
      |assumption
      ]
    |elim (le_to_or_lt_eq ? ? H1)
      [rewrite > false_to_pi_p_Sn
        [apply H
          [assumption
          |apply false_to_lt_max
            [apply (lt_to_le_to_lt ? (max m (λi:nat.primeb i∧divides_b i m)))
              [apply lt_to_le.
               apply lt_SO_max_prime.
               assumption
              |apply le_S_S_to_le.
               assumption
              ]
            |assumption
            |apply le_S_S_to_le.
             assumption
            ]
          ]
        |assumption
        ]
      |rewrite < H4.
       rewrite < (pi_p_false (λp:nat.p\sup(ord (S O) p)) (S n) ) in ⊢ (? ? % ?).
       apply eq_pi_p
        [intros.
         apply (bool_elim ? (primeb x));intro
          [apply sym_eq.
           change with (divides_b x (S O) =false).
           apply not_divides_to_divides_b_false
            [apply prime_to_lt_O.
             apply primeb_true_to_prime.
             assumption
            |intro.
             apply (le_to_not_lt x (S O))
              [apply divides_to_le
                [apply lt_O_S.assumption
                |assumption
                ]
              |elim (primeb_true_to_prime ? H6).
               assumption
              ]
            ]
          |reflexivity
          ]
        |intros.reflexivity
        ]
      ]
    ]
  ]
qed.

(* factorization of n into primes *)
theorem pi_p_primeb_divides_b: \forall n. O < n \to 
n = pi_p (S n) (\lambda i.primeb i \land divides_b i n) (\lambda p.exp p (ord n p)).
intros.
apply lt_max_to_pi_p_primeb
  [assumption
  |apply le_S_S.
   apply le_max_n
  ]
qed.

theorem pi_p_primeb: \forall n. O < n \to 
n = pi_p (S n) primeb (\lambda p.exp p (ord n p)).
intros.
rewrite < eq_pi_p_primeb_divides_b.
apply pi_p_primeb_divides_b.
assumption.
qed.

theorem le_ord_log: \forall n,p. O < n \to S O < p \to
ord n p \le log p n.
intros.
rewrite > (exp_ord p) in ⊢ (? ? (? ? %))
  [rewrite > log_exp
    [apply le_plus_n_r
    |assumption
    |apply lt_O_ord_rem;assumption
    ]
  |assumption
  |assumption
  ]
qed.

theorem sigma_p_divides_b:
\forall m,n,p. O < n \to prime p \to \lnot divides p n \to
m = sigma_p m (λi:nat.divides_b (p\sup (S i)) ((exp p m)*n)) (λx:nat.S O).
intro.elim m
  [reflexivity
  |simplify in ⊢ (? ? ? (? % ? ?)).
   rewrite > true_to_sigma_p_Sn
    [rewrite > sym_plus.rewrite < plus_n_SO.
     apply eq_f.
     rewrite > (H n1 p H1 H2 H3) in ⊢ (? ? % ?).
     apply eq_sigma_p1
      [intros.
       apply (bool_elim ? (divides_b (p\sup(S x)) (p\sup n*n1)));intro
        [apply sym_eq.
         apply divides_to_divides_b_true
          [apply lt_O_exp.
           apply prime_to_lt_O.
           assumption
          |apply (witness ? ? ((exp p (n - x))*n1)).
           rewrite < assoc_times.
           rewrite < exp_plus_times.
           apply eq_f2
            [apply eq_f.simplify.
             apply eq_f.
             rewrite > sym_plus.
             apply plus_minus_m_m.
             apply lt_to_le.assumption
            |reflexivity
            ]
          ]
        |apply sym_eq.
         apply False_ind.
         apply (divides_b_false_to_not_divides ? ? H5).
         apply (witness ? ? ((exp p (n - S x))*n1)).
         rewrite < assoc_times.
         rewrite < exp_plus_times.
         apply eq_f2
          [apply eq_f.
           rewrite > sym_plus.
           apply plus_minus_m_m.
           assumption
          |reflexivity
          ]
        ]
      |intros.reflexivity
      ]
    |apply divides_to_divides_b_true
      [apply lt_O_exp.
       apply prime_to_lt_O.assumption
      |apply (witness ? ? n1).reflexivity
      ]
    ]
  ]
qed.
  
theorem sigma_p_divides_b1:
\forall m,n,p,k. O < n \to prime p \to \lnot divides p n \to m \le k \to
m = sigma_p k (λi:nat.divides_b (p\sup (S i)) ((exp p m)*n)) (λx:nat.S O).
intros.
lapply (prime_to_lt_SO ? H1) as H4.
lapply (prime_to_lt_O ? H1) as H5.
rewrite > (false_to_eq_sigma_p m k)
  [apply sigma_p_divides_b;assumption
  |assumption
  |intros.
   apply not_divides_to_divides_b_false
    [apply lt_O_exp.assumption
    |intro.apply (le_to_not_lt ? ? H6).
     unfold lt.
     rewrite < (ord_exp p)
      [rewrite > (plus_n_O m).
       rewrite < (not_divides_to_ord_O ? ? H1 H2).
       rewrite < (ord_exp p ? H4) in ⊢ (? ? (? % ?)).
       rewrite < ord_times
        [apply divides_to_le_ord
          [apply lt_O_exp.assumption
          |rewrite > (times_n_O O).
           apply lt_times
            [apply lt_O_exp.assumption
            |assumption
            ]
          |assumption
          |assumption
          ]
        |apply lt_O_exp.assumption
        |assumption
        |assumption
        ]
      |assumption
      ]
    ]
  ]
qed.

theorem eq_ord_sigma_p:
\forall n,m,x. O < n \to prime x \to 
exp x m \le n \to n < exp x (S m) \to
ord n x=sigma_p m (λi:nat.divides_b (x\sup (S i)) n) (λx:nat.S O).
intros.
lapply (prime_to_lt_SO ? H1).
rewrite > (exp_ord x n) in ⊢ (? ? ? (? ? (λi:?.? ? %) ?))
  [apply sigma_p_divides_b1
    [apply lt_O_ord_rem;assumption
    |assumption
    |apply not_divides_ord_rem;assumption
    |apply lt_S_to_le.
     apply (le_to_lt_to_lt ? (log x n))
      [apply le_ord_log;assumption
      |apply (lt_exp_to_lt x)
        [assumption
        |apply (le_to_lt_to_lt ? n ? ? H3).
         apply le_exp_log.
         assumption
        ]
      ]
    ]
  |assumption
  |assumption
  ]
qed.
    
theorem pi_p_primeb1: \forall n. O < n \to 
n = pi_p (S n) primeb 
  (\lambda p.(pi_p (log p n) 
    (\lambda i.divides_b (exp p (S i)) n) (\lambda i.p))).
intros.
rewrite > (pi_p_primeb n H) in ⊢ (? ? % ?).
apply eq_pi_p1
  [intros.reflexivity
  |intros.
   rewrite > exp_sigma_p.
   apply eq_f.
   apply eq_ord_sigma_p
    [assumption
    |apply primeb_true_to_prime.
     assumption
    |apply le_exp_log.assumption
    |apply lt_exp_log.
     apply prime_to_lt_SO.
     apply primeb_true_to_prime.
     assumption
    ]
  ]
qed.

(* the factorial function *)
theorem eq_fact_pi_p:\forall n. fact n = 
pi_p (S n) (\lambda i.leb (S O) i) (\lambda i.i).
intro.elim n
  [reflexivity
  |change with ((S n1)*n1! = pi_p (S (S n1)) (λi:nat.leb (S O) i) (λi:nat.i)).
   rewrite > true_to_pi_p_Sn
    [apply eq_f.assumption
    |reflexivity
    ]
  ]
qed.
   
theorem eq_sigma_p_div: \forall n,q.O < q \to
sigma_p (S n) (λm:nat.leb (S O) m∧divides_b q m) (λx:nat.S O)
=n/q.
intros.
apply (div_mod_spec_to_eq n q ? (n \mod q) ? (n \mod q))
  [apply div_mod_spec_intro
    [apply lt_mod_m_m.assumption
    |elim n
      [simplify.elim q;reflexivity
      |elim (or_div_mod1 n1 q)
        [elim H2.clear H2.
         rewrite > divides_to_mod_O
          [rewrite < plus_n_O.
           rewrite > true_to_sigma_p_Sn
            [rewrite > H4 in ⊢ (? ? % ?).
             apply eq_f2
              [rewrite < sym_plus.
               rewrite < plus_n_SO.
               apply eq_f.
               apply (div_mod_spec_to_eq n1 q (div n1 q) (mod n1 q) ? (mod n1 q))
                [apply div_mod_spec_div_mod.
                 assumption
                |apply div_mod_spec_intro
                  [apply lt_mod_m_m.assumption
                  |assumption
                  ]
                ]
              |reflexivity
              ]
            |apply true_to_true_to_andb_true
              [reflexivity
              |apply divides_to_divides_b_true;assumption
              ]
            ]
          |assumption
          |assumption
          ]
        |elim H2.clear H2.
         rewrite > false_to_sigma_p_Sn
          [rewrite > mod_S
            [rewrite < plus_n_Sm.
             apply eq_f.
             assumption
            |assumption
            |elim (le_to_or_lt_eq (S (mod n1 q)) q)
              [assumption
              |apply False_ind.
               apply H3.
               apply (witness ? ? (S(div n1 q))).
               rewrite < times_n_Sm.
               rewrite < sym_plus.
               rewrite < H2 in ⊢ (? ? ? (? ? %)).
               rewrite > sym_times.
               assumption
              |apply lt_mod_m_m.
               assumption
              ]
            ]
          |rewrite > not_divides_to_divides_b_false
            [rewrite < andb_sym in ⊢ (? ? % ?).reflexivity
            |assumption
            |assumption
            ]
          ]
        |assumption
        ]
      ]
    ]
  |apply div_mod_spec_div_mod.
   assumption
  ]
qed.              

(* still another characterization of the factorial *)
theorem fact_pi_p: \forall n. fact n =
pi_p (S n) primeb 
  (\lambda p.(pi_p (log p n) 
    (\lambda i.true) (\lambda i.(exp p (n /(exp p (S i))))))).
intros.
rewrite > eq_fact_pi_p.
apply (trans_eq ? ? 
  (pi_p (S n) (λi:nat.leb (S O) i) 
   (λn.pi_p (S n) primeb 
    (\lambda p.(pi_p (log p n) 
     (\lambda i.divides_b (exp p (S i)) n) (\lambda i.p))))))
  [apply eq_pi_p1;intros
    [reflexivity
    |apply pi_p_primeb1.
     apply leb_true_to_le.assumption
    ]
  |apply (trans_eq ? ? 
    (pi_p (S n) (λi:nat.leb (S O) i)
     (λn:nat
      .pi_p (S n) (\lambda p.primeb p\land leb p n)
       (λp:nat.pi_p (log p n) (λi:nat.divides_b ((p)\sup(S i)) n) (λi:nat.p)))))
    [apply eq_pi_p1
      [intros.reflexivity
      |intros.apply eq_pi_p1
        [intros.elim (primeb x1)
          [simplify.apply sym_eq.
           apply le_to_leb_true.
           apply le_S_S_to_le.
           assumption
          |reflexivity
          ]
        |intros.reflexivity
        ]
      ]
    |apply (trans_eq ? ? 
      (pi_p (S n) (λi:nat.leb (S O) i)
       (λm:nat
        .pi_p (S n) (λp:nat.primeb p∧leb p m)
         (λp:nat.pi_p (log p m) (λi:nat.divides_b ((p)\sup(S i)) m) (λi:nat.p)))))
      [apply eq_pi_p1
        [intros.reflexivity
        |intros.
         apply sym_eq.
         apply false_to_eq_pi_p
          [assumption
          |intros.rewrite > lt_to_leb_false
            [elim primeb;reflexivity|assumption]
          ]
        ]
      |(* make a general theorem *)
       apply (trans_eq ? ? 
        (pi_p (S n) primeb
         (λp:nat
          .pi_p (S n) (λm.leb p m)
           (λm:nat.pi_p (log p m) (λi:nat.divides_b ((p)\sup(S i)) m) (λi:nat.p)))
        ))
        [apply pi_p_pi_p1.
         intros.
         apply (bool_elim ? (primeb y \land leb y x));intros
          [rewrite > (le_to_leb_true (S O) x)
            [reflexivity
            |apply (trans_le ? y)
              [apply prime_to_lt_O.
               apply primeb_true_to_prime.
               apply (andb_true_true ? ? H2)
              |apply leb_true_to_le.
               apply (andb_true_true_r ? ? H2)
              ]
            ]
          |elim (leb (S O) x);reflexivity
          ]
        |apply eq_pi_p1
          [intros.reflexivity
          |intros.
           apply (trans_eq ? ? 
            (pi_p (S n) (λm:nat.leb x m)
             (λm:nat.pi_p (log x n) (λi:nat.divides_b (x\sup(S i)) m) (λi:nat.x))))
            [apply eq_pi_p1
              [intros.reflexivity
              |intros.
               apply sym_eq.
               apply false_to_eq_pi_p
                [apply le_log
                  [apply prime_to_lt_SO.
                   apply primeb_true_to_prime.
                   assumption
                  |apply le_S_S_to_le.
                   assumption
                  ]
                |intros.
                 apply not_divides_to_divides_b_false
                  [apply lt_O_exp.
                   apply prime_to_lt_O.
                   apply primeb_true_to_prime.
                   assumption
                  |intro.
                   apply (lt_to_not_le x1 (exp x (S i)))
                    [apply (lt_to_le_to_lt ? (exp x (S(log x x1))))
                      [apply lt_exp_log.
                       apply prime_to_lt_SO.
                       apply primeb_true_to_prime.
                       assumption
                      |apply le_exp
                        [apply prime_to_lt_O.
                         apply primeb_true_to_prime.
                         assumption
                        |apply le_S_S.
                         assumption
                        ]
                      ]
                    |apply divides_to_le
                      [apply (lt_to_le_to_lt ? x)
                        [apply prime_to_lt_O.
                         apply primeb_true_to_prime.
                         assumption
                        |apply leb_true_to_le.
                         assumption
                        ]
                      |assumption
                      ]
                    ]
                  ]
                ]
              ]
            |apply 
             (trans_eq ? ? 
              (pi_p (log x n) (λi:nat.true)
               (λi:nat.pi_p (S n) (λm:nat.leb x m \land divides_b (x\sup(S i)) m) (λm:nat.x))))
              [apply (pi_p_pi_p1 (\lambda m,i.x)).
               intros.
               reflexivity
              |apply eq_pi_p1
                [intros.reflexivity
                |intros.
                 rewrite > exp_sigma_p.
                 apply eq_f.
                 apply (trans_eq ? ? 
                  (sigma_p (S n) (λm:nat.leb (S O) m∧divides_b (x\sup(S x1)) m) (λx:nat.S O)))
                  [apply eq_sigma_p1
                    [intros.
                     apply (bool_elim ? (divides_b (x\sup(S x1)) x2));intro
                      [apply (bool_elim ? (leb x x2));intro
                        [rewrite > le_to_leb_true
                          [reflexivity
                          |apply (trans_le ? x)
                            [apply prime_to_lt_O.
                             apply primeb_true_to_prime.
                             assumption
                            |apply leb_true_to_le.
                             assumption
                            ]
                          ]
                        |rewrite > lt_to_leb_false
                          [reflexivity
                          |apply not_le_to_lt.intro.
                           apply (leb_false_to_not_le ? ? H6).
                           apply (trans_le ? (exp x (S x1)))
                            [rewrite > times_n_SO in ⊢ (? % ?).
                             change with (exp x (S O) \le exp x (S x1)).
                             apply le_exp
                              [apply prime_to_lt_O.
                               apply primeb_true_to_prime.
                               assumption
                              |apply le_S_S.apply le_O_n.
                              ]
                            |apply divides_to_le
                              [assumption
                              |apply divides_b_true_to_divides.
                               assumption
                              ]
                            ]
                          ]
                        ]
                      |rewrite < andb_sym.
                       rewrite < andb_sym in ⊢ (? ? ? %).
                       reflexivity
                      ]
                    |intros.reflexivity
                    ]
                  |apply eq_sigma_p_div.
                   apply lt_O_exp.
                   apply prime_to_lt_O.
                   apply primeb_true_to_prime.
                   assumption
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
qed.

(* odd n is just mod n (S(S O)) 
let rec odd n \def
  match n with 
  [ O \Rightarrow O
  | S m \Rightarrow (S O) - odd m 
  ].

theorem le_odd_SO: \forall n. odd n \le S O.
intro.elim n
  [apply le_O_n
  |simplify.cases (odd n1)
    [simplify.apply le_n.
    |apply le_O_n
    ]
  ]
qed.

theorem SSO_odd: \forall n. n = (n/(S(S O)))*(S(S O)) + odd n.
intro.elim n
  [apply (lt_O_n_elim ? H).
   intro.simplify.reflexivity
  |
*)

theorem fact_pi_p2: \forall n. fact ((S(S O))*n) =
pi_p (S ((S(S O))*n)) primeb 
  (\lambda p.(pi_p (log p ((S(S O))*n)) 
    (\lambda i.true) (\lambda i.(exp p ((S(S O))*(n /(exp p (S i))))*(exp p (mod ((S(S O))*n /(exp p (S i))) (S(S O)))))))).
intros.rewrite > fact_pi_p.
apply eq_pi_p1
  [intros.reflexivity
  |intros.apply eq_pi_p
    [intros.reflexivity
    |intros.
     rewrite < exp_plus_times.
     apply eq_f.
     rewrite > sym_times in ⊢ (? ? ? (? % ?)).
     apply SSO_mod.
     apply lt_O_exp.
     apply prime_to_lt_O.
     apply primeb_true_to_prime.
     assumption
    ]
  ]
qed.

theorem fact_pi_p3: \forall n. fact ((S(S O))*n) =
pi_p (S ((S(S O))*n)) primeb 
  (\lambda p.(pi_p (log p ((S(S O))*n)) 
    (\lambda i.true) (\lambda i.(exp p ((S(S O))*(n /(exp p (S i))))))))*
pi_p (S ((S(S O))*n)) primeb 
  (\lambda p.(pi_p (log p ((S(S O))*n))   
    (\lambda i.true) (\lambda i.(exp p (mod ((S(S O))*n /(exp p (S i))) (S(S O))))))).
intros.
rewrite < times_pi_p.
rewrite > fact_pi_p2.
apply eq_pi_p;intros 
  [reflexivity
  |apply times_pi_p
  ]
qed.

theorem pi_p_primeb4: \forall n. S O < n \to
pi_p (S ((S(S O))*n)) primeb 
  (\lambda p.(pi_p (log p ((S(S O))*n)) 
    (\lambda i.true) (\lambda i.(exp p ((S(S O))*(n /(exp p (S i))))))))
= 
pi_p (S n) primeb 
  (\lambda p.(pi_p (log p (S(S O)*n)) 
    (\lambda i.true) (\lambda i.(exp p ((S(S O))*(n /(exp p (S i)))))))).
intros.
apply or_false_eq_SO_to_eq_pi_p
  [apply le_S_S.
   apply le_times_n.
   apply lt_O_S
  |intros.
   right.
   rewrite > log_i_SSOn
    [change with (i\sup((S(S O))*(n/i\sup(S O)))*(S O) = S O).
     rewrite < times_n_SO.
     rewrite > eq_div_O
      [reflexivity
      |simplify.rewrite < times_n_SO.assumption
      ]
    |assumption
    |assumption
    |apply le_S_S_to_le.assumption
    ]
  ]
qed.
   
theorem pi_p_primeb5: \forall n. S O < n \to
pi_p (S ((S(S O))*n)) primeb 
  (\lambda p.(pi_p (log p ((S(S O))*n)) 
    (\lambda i.true) (\lambda i.(exp p ((S(S O))*(n /(exp p (S i))))))))
= 
pi_p (S n) primeb 
  (\lambda p.(pi_p (log p n) 
    (\lambda i.true) (\lambda i.(exp p ((S(S O))*(n /(exp p (S i)))))))).
intros.
rewrite > (pi_p_primeb4 ? H).
apply eq_pi_p1;intros
  [reflexivity
  |apply or_false_eq_SO_to_eq_pi_p
    [apply le_log
      [apply prime_to_lt_SO.
       apply primeb_true_to_prime.
       assumption
      |apply le_times_n.
       apply lt_O_S
      ]
    |intros.right.
     rewrite > eq_div_O
      [simplify.reflexivity
      |apply (lt_to_le_to_lt ? (exp x (S(log x n))))
        [apply lt_exp_log.
         apply prime_to_lt_SO.
         apply primeb_true_to_prime.
         assumption
        |apply le_exp
          [apply prime_to_lt_O.
           apply primeb_true_to_prime.
           assumption
          |apply le_S_S.
           assumption
          ]
        ]
      ]
    ]
  ]
qed.

theorem exp_fact_SSO: \forall n.
exp (fact n) (S(S O))
= 
pi_p (S n) primeb 
  (\lambda p.(pi_p (log p n) 
    (\lambda i.true) (\lambda i.(exp p ((S(S O))*(n /(exp p (S i)))))))).
intros.
rewrite > fact_pi_p.
rewrite < exp_pi_p.
apply eq_pi_p;intros
  [reflexivity
  |apply sym_eq.
   apply exp_times_pi_p
  ]
qed.

definition B \def
\lambda n.
pi_p (S n) primeb 
  (\lambda p.(pi_p (log p n)   
    (\lambda i.true) (\lambda i.(exp p (mod (n /(exp p (S i))) (S(S O))))))).

theorem eq_fact_B:\forall n.S O < n \to
fact ((S(S O))*n) = exp (fact n) (S(S O)) * B((S(S O))*n).
intros. unfold B.
rewrite > fact_pi_p3.
apply eq_f2
  [apply sym_eq.
   rewrite > pi_p_primeb5
    [apply exp_fact_SSO
    |assumption
    ]
  |reflexivity
  ]
qed.

theorem le_B_A: \forall n. B n \le A n.
intro.unfold B.
rewrite > eq_A_A'.
unfold A'.
apply le_pi_p.intros.
apply le_pi_p.intros.
rewrite > exp_n_SO in ⊢ (? ? %).
apply le_exp
  [apply prime_to_lt_O.
   apply primeb_true_to_prime.
   assumption
  |apply le_S_S_to_le.
   apply lt_mod_m_m.
   apply lt_O_S
  ]
qed.

theorem le_fact_A:\forall n.S O < n \to
fact ((S(S O))*n) \le exp (fact n) (S(S O)) * A ((S(S O))*n).
intros.
rewrite > eq_fact_B
  [apply le_times_r.
   apply le_B_A
  |assumption
  ]
qed.

theorem lt_SO_to_le_B_exp: \forall n.S O < n \to
B ((S(S O))*n) \le exp (S(S O)) ((S(S O))*n).
intros.
apply (le_times_to_le (exp (fact n) (S(S O))))
  [apply lt_O_exp.
   apply lt_O_fact
  |rewrite < eq_fact_B
    [rewrite < sym_times in ⊢ (? ? %).
     rewrite > exp_SSO.
     rewrite < assoc_times.
     apply fact1
    |assumption
    ]
  ]
qed.

theorem le_B_exp: \forall n.
B ((S(S O))*n) \le exp (S(S O)) ((S(S O))*n).
intro.cases n
  [apply le_n
  |cases n1
    [simplify.apply le_S.apply le_S.apply le_n
    |apply lt_SO_to_le_B_exp.
     apply le_S_S.apply lt_O_S.
    ]
  ]
qed.

theorem lt_SO_to_le_exp_B: \forall n. S O < n \to
exp (S(S O)) ((S(S O))*n) \le (S(S O)) * n * B ((S(S O))*n).
intros.
apply (le_times_to_le (exp (fact n) (S(S O))))
  [apply lt_O_exp.
   apply lt_O_fact
  |rewrite < assoc_times in ⊢ (? ? %).
   rewrite > sym_times in ⊢ (? ? (? % ?)).
   rewrite > assoc_times in ⊢ (? ? %).
   rewrite < eq_fact_B
    [rewrite < sym_times.
     apply fact3.
     apply lt_to_le.assumption
    |assumption
    ]
  ]
qed.

theorem le_exp_B: \forall n. O < n \to
exp (S(S O)) ((S(S O))*n) \le (S(S O)) * n * B ((S(S O))*n).
intros.
elim H
  [apply le_n
  |apply lt_SO_to_le_exp_B.
   apply le_S_S.assumption
  ]
qed.

theorem eq_A_SSO_n: \forall n.O < n \to
A((S(S O))*n) =
 pi_p (S ((S(S O))*n)) primeb 
  (\lambda p.(pi_p (log p ((S(S O))*n) )   
    (\lambda i.true) (\lambda i.(exp p (bool_to_nat (leb (S n) (exp p (S i))))))))
 *A n.
intro.
rewrite > eq_A_A'.rewrite > eq_A_A'.
unfold A'.intros.
cut (
 pi_p (S n) primeb (λp:nat.pi_p (log p n) (λi:nat.true) (λi:nat.p))
 = pi_p (S ((S(S O))*n)) primeb
    (λp:nat.pi_p (log p ((S(S O))*n)) (λi:nat.true) (λi:nat.(p)\sup(bool_to_nat (\lnot (leb (S n) (exp p (S i))))))))
  [rewrite > Hcut.
   rewrite < times_pi_p.
   apply eq_pi_p1;intros
    [reflexivity
    |rewrite < times_pi_p.
     apply eq_pi_p;intros
      [reflexivity
      |apply (bool_elim ? (leb (S n) (exp x (S x1))));intro
        [simplify.rewrite < times_n_SO.apply times_n_SO
        |simplify.rewrite < plus_n_O.apply times_n_SO
        ]
      ]
    ]
  |apply (trans_eq ? ? (pi_p (S n) primeb 
    (\lambda p:nat.pi_p (log p n) (\lambda i:nat.true) (\lambda i:nat.(p)\sup(bool_to_nat (¬leb (S n) (exp p (S i))))))))
    [apply eq_pi_p1;intros
      [reflexivity
      |apply eq_pi_p1;intros
        [reflexivity
        |rewrite > lt_to_leb_false
          [simplify.apply times_n_SO
          |apply le_S_S.
           apply (trans_le ? (exp x (log x n)))
            [apply le_exp
              [apply prime_to_lt_O.
               apply primeb_true_to_prime.
               assumption
              |assumption
              ]
            |apply le_exp_log.
             assumption
            ]
          ]
        ]
      ]
    |apply (trans_eq ? ? 
      (pi_p (S ((S(S O))*n)) primeb
       (λp:nat.pi_p (log p n) (λi:nat.true)
        (λi:nat.(p)\sup(bool_to_nat (¬leb (S n) ((p)\sup(S i))))))))
      [apply sym_eq.
       apply or_false_eq_SO_to_eq_pi_p
        [apply le_S_S.
         simplify.
         apply le_plus_n_r
        |intros.right.
         rewrite > lt_to_log_O
          [reflexivity
          |assumption
          |assumption
          ]
        ]
      |apply eq_pi_p1;intros
        [reflexivity
        |apply sym_eq.
         apply or_false_eq_SO_to_eq_pi_p
          [apply le_log
            [apply prime_to_lt_SO.
             apply primeb_true_to_prime.
             assumption
            |simplify.
             apply le_plus_n_r
            ]
          |intros.right.
           rewrite > le_to_leb_true
            [simplify.reflexivity
            |apply (lt_to_le_to_lt ? (exp x (S (log x n))))
              [apply lt_exp_log.
               apply prime_to_lt_SO.
               apply primeb_true_to_prime.
               assumption
              |apply le_exp
                [apply prime_to_lt_O.
                 apply primeb_true_to_prime.
                 assumption
                |apply le_S_S.assumption
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
qed.
               
theorem le_A_BA1: \forall n. O < n \to 
A((S(S O))*n) \le B((S(S O))*n)*A n.
intros.
rewrite > eq_A_SSO_n
  [apply le_times_l.
   unfold B.
   apply le_pi_p.intros.
   apply le_pi_p.intros.
   apply le_exp
    [apply prime_to_lt_O.
     apply primeb_true_to_prime.
     assumption
    |apply (bool_elim ? (leb (S n) (exp i (S i1))));intro
      [simplify in ⊢ (? % ?).
       cut ((S(S O))*n/i\sup(S i1) = S O)
        [rewrite > Hcut.apply le_n
        |apply (div_mod_spec_to_eq 
          ((S(S O))*n) (exp i (S i1)) 
           ? (mod ((S(S O))*n) (exp i (S i1))) 
           ? (minus ((S(S O))*n) (exp i (S i1))) )
          [apply div_mod_spec_div_mod.
           apply lt_O_exp.
           apply prime_to_lt_O.
           apply primeb_true_to_prime.
           assumption
          |cut (i\sup(S i1)≤(S(S O))*n)
            [apply div_mod_spec_intro
              [apply lt_plus_to_lt_minus
                [assumption
                |simplify in ⊢ (? % ?).
                 rewrite < plus_n_O.
                 apply lt_plus
                  [apply leb_true_to_le.assumption
                  |apply leb_true_to_le.assumption
                  ]
                ]
              |rewrite > sym_plus.
               rewrite > sym_times in ⊢ (? ? ? (? ? %)).
               rewrite < times_n_SO.
               apply plus_minus_m_m.
               assumption
              ]
            |apply (trans_le ? (exp i (log i ((S(S O))*n))))
              [apply le_exp
                [apply prime_to_lt_O.
                 apply primeb_true_to_prime.
                 assumption
                |assumption
                ]
              |apply le_exp_log.
               rewrite > (times_n_O O) in ⊢ (? % ?).
               apply lt_times 
                [apply lt_O_S
                |assumption
                ]
              ]
            ]
          ]
        ]
      |apply le_O_n
      ]
    ]
  |assumption
  ]
qed.

theorem le_A_BA: \forall n. A((S(S O))*n) \le B((S(S O))*n)*A n.
intros.cases n
  [apply le_n
  |apply le_A_BA1.apply lt_O_S
  ]
qed.

theorem le_A_exp: \forall n.
A((S(S O))*n) \le (exp (S(S O)) ((S(S O)*n)))*A n.
intro.
apply (trans_le ? (B((S(S O))*n)*A n))
  [apply le_A_BA
  |apply le_times_l.
   apply le_B_exp
  ]
qed.

theorem le_A_exp1: \forall n.
A(exp (S(S O)) n) \le (exp (S(S O)) ((S(S O))*(exp (S(S O)) n))).
intro.elim n
  [simplify.apply le_S_S.apply le_O_n
  |change with (A ((S(S O))*((S(S O)))\sup n1)≤ ((S(S O)))\sup((S(S O))*((S(S O))\sup(S n1)))).
   apply (trans_le ? ((exp (S(S O)) ((S(S O)*(exp (S(S O)) n1))))*A (exp (S(S O)) n1)))
    [apply le_A_exp
    |apply (trans_le ? ((S(S O))\sup((S(S O))*((S(S O)))\sup(n1))*(S(S O))\sup((S(S O))*((S(S O)))\sup(n1))))
      [apply le_times_r.
       assumption
      |rewrite < exp_plus_times.
       simplify.rewrite < plus_n_O in ⊢ (? ? (? ? (? ? %))).
       apply le_n
      ]
    ]
  ]
qed.  

theorem monotonic_A: monotonic nat le A.
unfold.intros.
elim H
  [apply le_n
  |apply (trans_le ? (A n1))
    [assumption
    |unfold A.
     cut (pi_p (S n1) primeb (λp:nat.(p)\sup(log p n1))
          ≤pi_p (S n1) primeb (λp:nat.(p)\sup(log p (S n1))))
      [apply (bool_elim ? (primeb (S n1)));intro
        [rewrite > (true_to_pi_p_Sn ? ? ? H3).
         rewrite > times_n_SO in ⊢ (? % ?).
         rewrite > sym_times.
         apply le_times
          [apply lt_O_exp.apply lt_O_S
          |assumption
          ]
        |rewrite > (false_to_pi_p_Sn ? ? ? H3).
         assumption
        ]
      |apply le_pi_p.intros.
       apply le_exp
        [apply prime_to_lt_O.
         apply primeb_true_to_prime.
         assumption
        |apply le_log
          [apply prime_to_lt_SO.
           apply primeb_true_to_prime.
           assumption
          |apply le_S.apply le_n
          ]
        ]
      ]
    ]
  ]
qed.
 
theorem le_A_exp2: \forall n. O < n \to
A(n) \le (exp (S(S O)) ((S(S O)) * (S(S O)) * n)).
intros.
apply (trans_le ? (A (exp (S(S O)) (S(log (S(S O)) n)))))
  [apply monotonic_A.
   apply lt_to_le.
   apply lt_exp_log.
   apply le_n
  |apply (trans_le ? ((exp (S(S O)) ((S(S O))*(exp (S(S O)) (S(log (S(S O)) n)))))))
    [apply le_A_exp1
    |apply le_exp
      [apply lt_O_S
      |rewrite > assoc_times.apply le_times_r.
       change with ((S(S O))*((S(S O))\sup(log (S(S O)) n))≤(S(S O))*n).
       apply le_times_r.
       apply le_exp_log.
       assumption
      ]
    ]
  ]
qed.

(* example *)
theorem A_SO: A (S O) = S O.
reflexivity.
qed.

theorem A_SSO: A (S(S O)) = S (S O).
reflexivity.
qed.

theorem A_SSSO: A (S(S(S O))) = S(S(S(S(S(S O))))).
reflexivity.
qed.

theorem A_SSSSO: A (S(S(S(S O)))) = S(S(S(S(S(S(S(S(S(S(S(S O))))))))))).
reflexivity.
qed.

(* da spostare *)
theorem or_eq_eq_S: \forall n.\exists m. 
n = (S(S O))*m \lor n = S ((S(S O))*m).
intro.elim n
  [apply (ex_intro ? ? O).
   left.reflexivity
  |elim H.elim H1
    [apply (ex_intro ? ? a).
     right.apply eq_f.assumption
    |apply (ex_intro ? ? (S a)).
     left.rewrite > H2.
     apply sym_eq.
     apply times_SSO
    ]
  ]
qed.

(* a better result *)
theorem le_A_exp3: \forall n. S O < n \to
A(n) \le exp (pred n) (S(S O))*(exp (S(S O)) ((S(S O)) * n)).
intro.
apply (nat_elim1 n).
intros.
elim (or_eq_eq_S m).
elim H2
  [elim (le_to_or_lt_eq (S O) a)
    [rewrite > H3 in ⊢ (? % ?).
     apply (trans_le ? ((exp (S(S O)) ((S(S O)*a)))*A a))
      [apply le_A_exp
      |apply (trans_le ? (((S(S O)))\sup((S(S O))*a)*
         ((pred a)\sup((S(S O)))*((S(S O)))\sup((S(S O))*a))))
        [apply le_times_r.
         apply H
          [rewrite > H3.
           rewrite > times_n_SO in ⊢ (? % ?).
           rewrite > sym_times.
           apply lt_times_l1
            [apply lt_to_le.assumption
            |apply le_n
            ]
          |assumption
          ]
        |rewrite > sym_times.
         rewrite > assoc_times.
         rewrite < exp_plus_times.
         apply (trans_le ? 
          (pred a\sup((S(S O)))*(S(S O))\sup(S(S O))*(S(S O))\sup((S(S O))*m)))
          [rewrite > assoc_times.
           apply le_times_r.
           rewrite < exp_plus_times.
           apply le_exp
            [apply lt_O_S
            |rewrite < H3.
             simplify.
             rewrite < plus_n_O.
             apply le_S.apply le_S.
             apply le_n
            ]
          |apply le_times_l.
           rewrite > times_exp.
           apply monotonic_exp1.
           rewrite > H3.
           rewrite > sym_times.
           cases a
            [apply le_n
            |simplify.
             rewrite < plus_n_Sm.
             apply le_S.
             apply le_n
            ]
          ]
        ]
      ]
    |rewrite < H4 in H3.
     simplify in H3.
     rewrite > H3.
     simplify.
     apply le_S_S.apply le_S_S.apply le_O_n
    |apply not_lt_to_le.intro.
     apply (lt_to_not_le ? ? H1).
     rewrite > H3.
     apply (le_n_O_elim a)
      [apply le_S_S_to_le.assumption
      |apply le_O_n
      ]
    ]
  |elim (le_to_or_lt_eq O a (le_O_n ?))
    [apply (trans_le ? (A ((S(S O))*(S a))))
      [apply monotonic_A.
       rewrite > H3.
       rewrite > times_SSO.
       apply le_n_Sn
      |apply (trans_le ? ((exp (S(S O)) ((S(S O)*(S a))))*A (S a)))
        [apply le_A_exp
        |apply (trans_le ? (((S(S O)))\sup((S(S O))*S a)*
           (a\sup((S(S O)))*((S(S O)))\sup((S(S O))*(S a)))))
          [apply le_times_r.
           apply H
            [rewrite > H3.
             apply le_S_S.
             simplify.
             rewrite > plus_n_SO.
             apply le_plus_r.
             rewrite < plus_n_O.
             assumption
            |apply le_S_S.assumption
            ]
          |rewrite > sym_times.
           rewrite > assoc_times.
           rewrite < exp_plus_times.
           apply (trans_le ? 
            (a\sup((S(S O)))*(S(S O))\sup(S(S O))*(S(S O))\sup((S(S O))*m)))
            [rewrite > assoc_times.
             apply le_times_r.
             rewrite < exp_plus_times.
             apply le_exp
              [apply lt_O_S
              |rewrite > times_SSO.
               rewrite < H3.
               simplify.
               rewrite < plus_n_Sm.
               rewrite < plus_n_O.
               apply le_n
              ]
            |apply le_times_l.
             rewrite > times_exp.
             apply monotonic_exp1.
             rewrite > H3.
             rewrite > sym_times.
             apply le_n
            ]
          ]
        ]
      ]
    |rewrite < H4 in H3.simplify in H3.
     apply False_ind.
     apply (lt_to_not_le ? ? H1).
     rewrite > H3.
     apply le_n
    ]
  ]
qed.

theorem eq_sigma_pi_SO_n: \forall n.
sigma_p n (\lambda i.true) (\lambda i.S O) = n.
intro.elim n
  [reflexivity
  |rewrite > true_to_sigma_p_Sn
    [rewrite > H.reflexivity
    |reflexivity
    ]
  ]
qed.

theorem leA_prim: \forall n.
exp n (prim n) \le A n * pi_p (S n) primeb (λp:nat.p).
intro.
unfold prim.
rewrite < (exp_sigma_p (S n) n primeb).
unfold A.
rewrite < times_pi_p.
apply le_pi_p.
intros.
rewrite > sym_times.
change in ⊢ (? ? %) with (exp i (S (log i n))).
apply lt_to_le.
apply lt_exp_log.
apply prime_to_lt_SO.
apply primeb_true_to_prime.
assumption.
qed.


(* the inequalities *)
theorem le_exp_priml: \forall n. O < n \to
exp (S(S O)) ((S(S O))*n) \le exp ((S(S O))*n) (S(prim ((S(S O))*n))).
intros.
apply (trans_le ? ((((S(S O))*n*(B ((S(S O))*n))))))
  [apply le_exp_B.assumption
  |change in ⊢ (? ? %) with ((((S(S O))*n))*(((S(S O))*n))\sup (prim ((S(S O))*n))).
   apply le_times_r.
   apply (trans_le ? (A ((S(S O))*n)))
    [apply le_B_A
    |apply le_Al
    ]
  ]
qed.

theorem le_priml: \forall n. O < n \to
(S(S O))*n \le (S (log (S(S O)) ((S(S O))*n)))*S(prim ((S(S O))*n)).
intros.
rewrite < (eq_log_exp (S(S O))) in ⊢ (? % ?)
  [apply (trans_le ? ((log (S(S O)) (exp ((S(S O))*n) (S(prim ((S(S O))*n)))))))
    [apply le_log
      [apply le_n
      |apply le_exp_priml.assumption
      ]
    |rewrite > sym_times in ⊢ (? ? %). 
     apply log_exp1.
     apply le_n
    ]
  |apply le_n
  ]
qed.

theorem le_exp_primr: \forall n. S O < n \to
exp n (prim n) \le exp (pred n) ((S(S O))*(S(S O)))*(exp (S(S O)) ((S(S O))*(S(S O)) * n)).
intros.
apply (trans_le ? (exp (A n) (S(S O))))
  [change in ⊢ (? ? %) with ((A n)*((A n)*(S O))).
   rewrite < times_n_SO.
   apply leA_r2
  |apply (trans_le ? (exp (exp (pred n) (S(S O))*(exp (S(S O)) ((S(S O)) * n))) (S(S O))))
    [apply monotonic_exp1.
     apply le_A_exp3.
     assumption
    |rewrite < times_exp.
     rewrite > exp_exp_times.
     rewrite > exp_exp_times.
     rewrite > sym_times in ⊢ (? (? ? (? ? %)) ?).
     rewrite < assoc_times in ⊢ (? (? ? (? ? %)) ?).
     apply le_n
    ]
  ]
qed.

