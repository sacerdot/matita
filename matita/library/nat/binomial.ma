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
include "nat/factorial2.ma".

definition bc \def \lambda n,k. n!/(k!*(n-k)!).

theorem bc_n_n: \forall n. bc n n = S O.
intro.unfold bc.
rewrite < minus_n_n.
simplify in ⊢ (? ? (? ? (? ? %)) ?).
rewrite < times_n_SO.
apply div_n_n.
apply lt_O_fact.
qed.

theorem bc_n_O: \forall n. bc n O = S O.
intro.unfold bc.
rewrite < minus_n_O.
simplify in ⊢ (? ? (? ? %) ?).
rewrite < plus_n_O.
apply div_n_n.
apply lt_O_fact.
qed.

theorem fact_minus: \forall n,k. k < n \to 
(n-k)*(n - S k)! = (n - k)!.
intros 2.cases n
  [intro.apply False_ind.
   apply (lt_to_not_le ? ? H).
   apply le_O_n
  |intros.
   rewrite > minus_Sn_m.
   reflexivity.
   apply le_S_S_to_le.
   assumption
  ]
qed.

theorem bc2 : \forall n.
\forall k. k \leq n \to divides (k!*(n-k)!) n!.
intro;elim n
  [rewrite < (le_n_O_to_eq ? H);apply reflexive_divides
  |generalize in match H1;cases k
     [intro;simplify in ⊢ (? (? ? (? %)) ?);simplify in ⊢ (? (? % ?) ?);
      rewrite > sym_times;rewrite < times_n_SO;apply reflexive_divides
     |intro;elim (decidable_eq_nat n2 n1)
        [rewrite > H3;rewrite < minus_n_n;
         rewrite > times_n_SO in ⊢ (? ? %);apply reflexive_divides
        |lapply (H n2)
           [lapply (H (n1 - (S n2)))
              [change in ⊢ (? ? %) with ((S n1)*n1!);
               rewrite > (plus_minus_m_m n1 n2) in ⊢ (? ? (? (? %) ?))
                 [rewrite > sym_plus;
                  change in ⊢ (? ? (? % ?)) with ((S n2) + (n1 - n2));
                  rewrite > sym_times in \vdash (? ? %);
                  rewrite > distr_times_plus in ⊢ (? ? %);
                  simplify in ⊢ (? (? ? (? %)) ?);
                  apply divides_plus
                    [rewrite > sym_times;
                     change in ⊢ (? (? ? %) ?) with ((S n2)*n2!);
                     rewrite > sym_times in ⊢ (? (? ? %) ?);
                     rewrite < assoc_times;
                     apply divides_times
                       [rewrite > sym_times;assumption
                       |apply reflexive_divides]
                    |rewrite < fact_minus in ⊢ (? (? ? %) ?)
                       [rewrite > sym_times in ⊢ (? (? ? %) ?);
                        rewrite < assoc_times;
                        apply divides_times
                          [rewrite < eq_plus_minus_minus_minus in Hletin1;
                             [rewrite > sym_times;rewrite < minus_n_n in Hletin1;
                              rewrite < plus_n_O in Hletin1;assumption
                             |lapply (le_S_S_to_le ? ? H2);
                              elim (le_to_or_lt_eq ? ? Hletin2);
                                [assumption
                                |elim (H3 H4)]
                             |constructor 1]
                          |apply reflexive_divides]
                       |lapply (le_S_S_to_le ? ? H2);
                        elim (le_to_or_lt_eq ? ? Hletin2);
                          [assumption
                          |elim (H3 H4)]]]
                 |apply le_S_S_to_le;assumption]
              |apply le_minus_m;apply le_S_S_to_le;assumption]
           |apply le_S_S_to_le;assumption]]]]
qed.                      
    
theorem bc1: \forall n.\forall k. k < n \to bc (S n) (S k) = (bc n k) + (bc n (S k)). 
intros.unfold bc.
rewrite > (lt_to_lt_to_eq_div_div_times_times ? ? (S k)) in ⊢ (? ? ? (? % ?))
  [rewrite > sym_times in ⊢ (? ? ? (? (? ? %) ?)). 
   rewrite < assoc_times in ⊢ (? ? ? (? (? ? %) ?)).
   rewrite > (lt_to_lt_to_eq_div_div_times_times ? ? (n - k)) in ⊢ (? ? ? (? ? %))
    [rewrite > assoc_times in ⊢ (? ? ? (? ? (? ? %))).
     rewrite > sym_times in ⊢ (? ? ? (? ? (? ? (? ? %)))).
     rewrite > fact_minus
      [rewrite < eq_div_plus
        [rewrite < distr_times_plus.
         simplify in ⊢ (? ? ? (? (? ? %) ?)).
         rewrite > sym_plus in ⊢ (? ? ? (? (? ? (? %)) ?)).
         rewrite < plus_minus_m_m
          [rewrite > sym_times in ⊢ (? ? ? (? % ?)).
           reflexivity
          |apply lt_to_le.
           assumption
          ]
        |rewrite > (times_n_O O).
         apply lt_times;apply lt_O_fact
        |change in ⊢ (? (? % ?) ?) with ((S k)*k!);
         rewrite < sym_times in ⊢ (? ? %);
         rewrite > assoc_times;apply divides_times
           [apply reflexive_divides
           |apply bc2;apply le_S_S_to_le;constructor 2;assumption]
        |rewrite < fact_minus
           [rewrite > sym_times in ⊢ (? (? ? %) ?);rewrite < assoc_times;
            apply divides_times
              [apply bc2;assumption
              |apply reflexive_divides]
           |assumption]]
     |assumption]
  |apply lt_to_lt_O_minus;assumption
  |rewrite > (times_n_O O).
   apply lt_times;apply lt_O_fact]
|apply lt_O_S
|rewrite > (times_n_O O).
 apply lt_times;apply lt_O_fact]
qed.

theorem lt_O_bc: \forall n,m. m \le n \to O < bc n m.
intro.elim n
  [apply (le_n_O_elim ? H).
   simplify.apply le_n
  |elim (le_to_or_lt_eq ? ? H1)
    [generalize in match H2.cases m;intro
      [rewrite > bc_n_O.apply le_n
      |rewrite > bc1
        [apply (trans_le ? (bc n1 n2))
          [apply H.apply le_S_S_to_le.apply lt_to_le.assumption
          |apply le_plus_n_r
          ]
        |apply le_S_S_to_le.assumption
        ]
      ]
    |rewrite > H2.
     rewrite > bc_n_n.
     apply le_n
    ]
  ]
qed.

theorem exp_plus_sigma_p:\forall a,b,n.
exp (a+b) n = sigma_p (S n) (\lambda k.true) 
  (\lambda k.(bc n k)*(exp a (n-k))*(exp b k)).
intros.elim n
  [simplify.reflexivity
  |simplify in ⊢ (? ? % ?).
   rewrite > true_to_sigma_p_Sn
    [rewrite > H;rewrite > sym_times in ⊢ (? ? % ?);
     rewrite > distr_times_plus in ⊢ (? ? % ?);
     rewrite < minus_n_n in ⊢ (? ? ? (? (? (? ? (? ? %)) ?) ?));
     rewrite > sym_times in ⊢ (? ? (? % ?) ?);
     rewrite > sym_times in ⊢ (? ? (? ? %) ?);
     rewrite > distributive_times_plus_sigma_p in ⊢ (? ? (? % ?) ?);
     rewrite > distributive_times_plus_sigma_p in ⊢ (? ? (? ? %) ?);
     rewrite > true_to_sigma_p_Sn in ⊢ (? ? (? ? %) ?)
       [rewrite < assoc_plus;rewrite < sym_plus in ⊢ (? ? (? % ?) ?);
        rewrite > assoc_plus;
        apply eq_f2
          [rewrite > sym_times;rewrite > assoc_times;autobatch paramodulation
          |rewrite > (sigma_p_gi ? ? O);
            [rewrite < (eq_sigma_p_gh ? S pred n1 (S n1) (λx:nat.true)) in ⊢ (? ? (? (? ? %) ?) ?)
               [rewrite > (sigma_p_gi ? ? O) in ⊢ (? ? ? %);
                  [rewrite > assoc_plus;apply eq_f2
                     [autobatch paramodulation; 
                     |rewrite < sigma_p_plus_1;
                      rewrite < (eq_sigma_p_gh ? S pred n1 (S n1) (λx:nat.true)) in \vdash (? ? ? %);
                        [apply eq_sigma_p
                           [intros;reflexivity
                           |intros;rewrite > sym_times;rewrite > assoc_times;
                            rewrite > sym_times in ⊢ (? ? (? (? ? %) ?) ?);
                            rewrite > assoc_times;rewrite < assoc_times in ⊢ (? ? (? (? ? %) ?) ?);
                            rewrite > sym_times in ⊢ (? ? (? (? ? (? % ?)) ?) ?);
                            change in ⊢ (? ? (? (? ? (? % ?)) ?) ?) with (exp a (S (n1 - S x)));
                            rewrite < (minus_Sn_m ? ? H1);rewrite > minus_S_S;
                            rewrite > sym_times in \vdash (? ? (? ? %) ?);
                            rewrite > assoc_times; 
                            rewrite > sym_times in ⊢ (? ? (? ? (? ? %)) ?);
                            change in \vdash (? ? (? ? (? ? %)) ?) with (exp b (S x));
                            rewrite > assoc_times in \vdash (? ? (? ? %) ?);
                            rewrite > sym_times in \vdash (? ? (? % ?) ?);
                            rewrite > sym_times in \vdash (? ? (? ? %) ?);
                            rewrite > assoc_times in \vdash (? ? ? %);
                            rewrite > sym_times in \vdash (? ? ? %);
                            rewrite < distr_times_plus;
                            rewrite > sym_plus;rewrite < bc1;
                              [reflexivity|assumption]]
                        |intros;simplify;reflexivity
                        |intros;simplify;reflexivity
                        |intros;apply le_S_S;assumption
                        |intros;reflexivity
                        |intros 2;elim j
                            [simplify in H2;destruct H2
                            |simplify;reflexivity]
                        |intro;elim j
                            [simplify in H2;destruct H2
                            |simplify;apply le_S_S_to_le;assumption]]]
                  |apply le_S_S;apply le_O_n
                  |reflexivity]
               |intros;simplify;reflexivity
               |intros;simplify;reflexivity
               |intros;apply le_S_S;assumption
               |intros;reflexivity
               |intros 2;elim j
                  [simplify in H2;destruct H2
                  |simplify;reflexivity]
               |intro;elim j
                  [simplify in H2;destruct H2
                  |simplify;apply le_S_S_to_le;assumption]]
            |apply le_S_S;apply le_O_n
            |reflexivity]]
      |reflexivity]
   |reflexivity]]
qed.

theorem exp_S_sigma_p:\forall a,n.
exp (S a) n = sigma_p (S n) (\lambda k.true) (\lambda k.(bc n k)*(exp a (n-k))).
intros.
rewrite > plus_n_SO.
rewrite > exp_plus_sigma_p.
apply eq_sigma_p;intros
  [reflexivity
  |rewrite < exp_SO_n.
   rewrite < times_n_SO.
   reflexivity
  ]
qed.

theorem exp_Sn_SSO: \forall n. exp (S n) 2 = S((exp n 2) + 2*n).
intros.simplify.
rewrite < times_n_SO.
rewrite < plus_n_O.
rewrite < sym_times.simplify.
rewrite < assoc_plus.
rewrite < sym_plus.
reflexivity.
qed.

