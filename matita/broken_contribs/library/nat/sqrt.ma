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

include "nat/times.ma".
include "nat/compare.ma".
include "nat/log.ma".

definition sqrt \def
  \lambda n.max n (\lambda x.leb (x*x) n).

theorem eq_sqrt: \forall n. sqrt (n*n) = n.
intros.
unfold sqrt.apply max_spec_to_max.
unfold max_spec.split
  [split
    [cases n
      [apply le_n
      |rewrite > times_n_SO in ⊢ (? % ?).
       apply le_times_r.
       apply le_S_S.apply le_O_n
      ]
    |apply le_to_leb_true.apply le_n
    ]
  |intros.
   apply lt_to_leb_false.
   apply lt_times;assumption
  ]
qed.

theorem le_sqrt_to_le_times_l : \forall m,n.n \leq sqrt m \to n*n \leq m.
intros;apply (trans_le ? (sqrt m * sqrt m))
  [apply le_times;assumption
  |apply leb_true_to_le;apply (f_max_true (λx:nat.leb (x*x) m) m);
   apply (ex_intro ? ? O);split
     [apply le_O_n
     |simplify;reflexivity]]
qed.
 
theorem lt_sqrt_to_le_times_l : \forall m,n.n < sqrt m \to n*n < m.
intros;apply (trans_le ? (sqrt m * sqrt m))
  [apply (trans_le ? (S n * S n))
     [simplify in \vdash (? ? %);apply le_S_S;apply (trans_le ? (n * S n))
        [apply le_times_r;apply le_S;apply le_n
        |rewrite > sym_plus;rewrite > plus_n_O in \vdash (? % ?);
         apply le_plus_r;apply le_O_n]  
     |apply le_times;assumption]
  |apply le_sqrt_to_le_times_l;apply le_n]
qed.

theorem le_sqrt_to_le_times_r : \forall m,n.sqrt m < n \to m < n*n.
intros;apply not_le_to_lt;intro;
apply ((leb_false_to_not_le ? ? 
           (lt_max_to_false (\lambda x.leb (x*x) m) m n H ?))
         H1);
apply (trans_le ? ? ? ? H1);cases n
  [apply le_n
  |rewrite > times_n_SO in \vdash (? % ?);rewrite > sym_times;apply le_times
     [apply le_S_S;apply le_O_n
     |apply le_n]]
qed.
  
lemma le_sqrt_n_n : \forall n.sqrt n \leq n.
intro.unfold sqrt.apply le_max_n.
qed.

lemma leq_sqrt_n : \forall n. sqrt n * sqrt n \leq n.
intro;unfold sqrt;apply leb_true_to_le;apply f_max_true;apply (ex_intro ? ? O);
split
  [apply le_O_n
  |simplify;reflexivity]
qed.

alias num (instance 0) = "natural number".

lemma lt_sqrt_n : \forall n.1 < n \to sqrt n < n.
intros.
elim (le_to_or_lt_eq ? ? (le_sqrt_n_n n))
  [assumption
  |apply False_ind.
   apply (le_to_not_lt ? ? (leq_sqrt_n n)).
   rewrite > H1.
   rewrite > times_n_SO in ⊢ (? % ?).
   apply lt_times_r1
    [apply lt_to_le.assumption
    |assumption
    ]
  ]
qed.

lemma lt_sqrt: \forall n.n < (exp (S (sqrt n)) 2).
intro.
cases n
  [apply le_n
  |cases n1
    [simplify.apply lt_to_le.apply lt_to_le.apply le_n
    |apply not_le_to_lt.
     apply leb_false_to_not_le.
     rewrite > exp_SSO.
     apply (lt_max_to_false (\lambda x.(leb (x*x) (S(S n2)))) (S(S n2)))
      [apply le_n
      |apply lt_sqrt_n.
       apply le_S_S.apply lt_O_S.
      ]
    ]
  ]
qed.

lemma le_sqrt_n1: \forall n. n - 2*sqrt n \le exp (sqrt n) 2.
intros.
apply le_plus_to_minus.
apply le_S_S_to_le.
cut (S ((sqrt n)\sup 2+2*sqrt n) = (exp (S(sqrt n)) 2))
  [rewrite > Hcut.apply lt_sqrt
  |rewrite > exp_SSO.rewrite > exp_SSO.
   simplify.apply eq_f.
   rewrite < times_n_Sm.
   rewrite < plus_n_O.
   rewrite < assoc_plus in ⊢ (? ? ? %).
   rewrite > sym_plus.
   reflexivity
  ]
qed.

(* falso per n=2, m=7 e n=3, m =15 *)
lemma le_sqrt_nl: \forall n,m. 3 < n \to
m*(pred m)*n \le exp (sqrt ((exp m 2)*n)) 2.
intros.
rewrite > minus_n_O in ⊢ (? (? (? ? (? %)) ?) ?).
rewrite < eq_minus_S_pred.
rewrite > distr_times_minus.
rewrite < times_n_SO.
rewrite > sym_times.
rewrite > distr_times_minus.
rewrite > sym_times.
apply (trans_le ? (m*m*n -2*sqrt(m*m*n)))
  [apply monotonic_le_minus_r.
   apply (le_exp_to_le1 ? ? 2)
    [apply lt_O_S
    |rewrite < times_exp.
     apply (trans_le ? ((exp 2 2)*(m*m*n)))
      [apply le_times_r.
       rewrite > exp_SSO.
       apply leq_sqrt_n
      |rewrite < exp_SSO.
       rewrite < times_exp.
       rewrite < assoc_times.
       rewrite < sym_times in ⊢ (? (? % ?) ?).
       rewrite > assoc_times.
       rewrite > sym_times.
       apply le_times_l.
       rewrite > exp_SSO in ⊢ (? ? %).
       apply le_times_l.
       assumption
      ]
    ]
  |rewrite <exp_SSO. 
   apply le_sqrt_n1
  ]
qed.
       
lemma le_sqrt_log_n : \forall n,b. 2 < b \to sqrt n * log b n \leq n.
intros.
apply (trans_le ? ? ? ? (leq_sqrt_n ?));
apply le_times_r;unfold sqrt;
apply f_m_to_le_max
  [apply le_log_n_n;apply lt_to_le;assumption
  |apply le_to_leb_true;elim (le_to_or_lt_eq ? ? (le_O_n n))
     [apply (trans_le ? (exp b (log b n)))
        [elim (log b n)
           [apply le_O_n
           |simplify in \vdash (? ? %);
           elim (le_to_or_lt_eq ? ? (le_O_n n1))
              [elim (le_to_or_lt_eq ? ? H3)
                 [apply (trans_le ? (3*(n1*n1)));
                    [simplify in \vdash (? % ?);rewrite > sym_times in \vdash (? % ?);
                     simplify in \vdash (? % ?);
                     simplify;rewrite > sym_plus;
                     rewrite > plus_n_Sm;rewrite > sym_plus in \vdash (? (? % ?) ?);
                     rewrite > assoc_plus;apply le_plus_r;
                     rewrite < plus_n_Sm;
                     rewrite < plus_n_O;
                     apply lt_plus;rewrite > times_n_SO in \vdash (? % ?);
                     apply lt_times_r1;assumption;
                    |apply le_times
                       [assumption
                       |assumption]]
                 |rewrite < H4;apply le_times
                    [apply lt_to_le;assumption
                    |apply lt_to_le;simplify;rewrite < times_n_SO;assumption]]
             |rewrite < H3;simplify;rewrite < times_n_SO;do 2 apply lt_to_le;assumption]]
        |simplify;apply le_exp_log;assumption]
     |rewrite < H1;simplify;apply le_n]]
qed.

(* monotonicity *)
theorem monotonic_sqrt: monotonic nat le sqrt.
unfold.intros.
unfold sqrt in ⊢ (? ? (% ?)).
apply f_m_to_le_max
  [apply (trans_le ? ? ? ? H).
   apply le_sqrt_n_n
  |apply le_to_leb_true.
   apply (trans_le ? ? ? ? H). 
   apply leq_sqrt_n
  ]
qed.
   
   
