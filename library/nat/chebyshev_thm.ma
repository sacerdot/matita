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

include "nat/neper.ma".

definition C \def \lambda n.pi_p (S n) primeb 
  (\lambda p.match (leb (p*p) n) with
    [ true => p
    | false => S (n/p) ]).
    
theorem asdasd : \forall n. exp n (prim n) \leq (A n)*(C n).
intro;unfold prim;rewrite < exp_sigma_p;unfold A;unfold C;rewrite < times_pi_p;
apply le_pi_p;intros;
apply (bool_elim ? (leb (i*i) n));intro
    [change in \vdash (? ? (? ? %)) with i;
     rewrite > sym_times;change in \vdash (? ? %) with (exp i (S (log i n)));
     apply lt_to_le;apply lt_exp_log;apply prime_to_lt_SO;
     apply primeb_true_to_prime;assumption
    |change in \vdash (? ? (? ? %)) with (S (n/i));
     cut (log i n = S O)
       [rewrite > Hcut;rewrite < exp_n_SO;
        apply lt_to_le;rewrite > sym_times;apply lt_div_S;apply prime_to_lt_O;
        apply primeb_true_to_prime;assumption
       |apply antisymmetric_le
         [apply le_S_S_to_le;apply not_le_to_lt;intro;
          apply (leb_false_to_not_le ? ? H2);apply (trans_le ? (exp i (log i n)))
           [rewrite < exp_SSO;apply le_exp;
              [apply prime_to_lt_O;
               apply primeb_true_to_prime;assumption
              |assumption]
           |apply le_exp_log;apply (trans_le ? i)
              [apply prime_to_lt_O;apply primeb_true_to_prime;assumption
              |apply le_S_S_to_le;assumption]]
         |apply (trans_le ? (log i i))
           [rewrite > log_n_n;
              [apply le_n
              |apply prime_to_lt_SO;apply primeb_true_to_prime;assumption]
           |apply le_log
              [apply prime_to_lt_SO;apply primeb_true_to_prime;assumption
              |apply le_S_S_to_le;assumption]]]]]
qed.

definition theta_pi \def
  \lambda n.pi_p (S n) primeb (\lambda p.p). 

definition C1 \def
  \lambda n. pi_p (S n) (\lambda x. (primeb x) \land (leb (x*x) n)) (\lambda p.p).
  
definition C2 \def
  \lambda n. pi_p (S n) (\lambda x. (primeb x) \land (leb (S n) (x*x))) (\lambda p.S (n/p)).
  

theorem jj : \forall n.C n = C1 n * C2 n.
intro;unfold C;unfold C1;unfold C2;
cut (\forall m.pi_p (S n) primeb
(λp:nat
 .match leb (p*p) m in bool return λb:bool.nat with 
  [true⇒p|false⇒S (m/p)])
=pi_p (S n) (λx:nat.primeb x∧leb (x*x) m) (λp:nat.p)
 *pi_p (S n) (λx:nat.primeb x∧leb (S m) (x*x)) (λp:nat.S (m/p)))
  [apply Hcut;
  |intro;elim n 0
     [simplify;reflexivity
     |intro;apply (bool_elim ? (primeb (S n1)))
        [intros;rewrite > true_to_pi_p_Sn
           [apply (bool_elim ? (leb ((S n1)*(S n1)) m))
              [intro;rewrite > true_to_pi_p_Sn in \vdash (? ? ? (? % ?))
                 [rewrite > false_to_pi_p_Sn in \vdash (? ? ? (? ? %))
                    [rewrite > H1;rewrite < assoc_times;reflexivity
                    |rewrite > H;lapply (leb_true_to_le ? ? H2);
                     lapply (le_to_not_lt ? ? Hletin);
                     apply (bool_elim ? (leb (S m) (S n1 * S n1)))
                       [intro;apply False_ind;apply Hletin1;
                        apply leb_true_to_le;assumption
                       |intro;reflexivity]]
                 |rewrite > H2;rewrite > H;reflexivity]
              |intro;rewrite > false_to_pi_p_Sn in \vdash (? ? ? (? % ?))
                 [rewrite > true_to_pi_p_Sn in \vdash (? ? ? (? ? %))
                    [rewrite > H1;rewrite < assoc_times;
                     rewrite > sym_times in \vdash (? ? (? % ?) ?);
                     rewrite > assoc_times;reflexivity
                    |rewrite > H;
                     change in \vdash (? ? % ?) with (leb (S m) (S n1* S n1));
                     apply le_to_leb_true;apply not_le_to_lt;
                     apply leb_false_to_not_le;assumption]
                 |rewrite > H;rewrite > H2;reflexivity]]
           |assumption]
        |intros;rewrite > false_to_pi_p_Sn
           [rewrite > false_to_pi_p_Sn in \vdash (? ? ? (? % ?))
              [rewrite > false_to_pi_p_Sn in \vdash (? ? ? (? ? %))
                 [rewrite > H1;reflexivity
                 |rewrite > H;elim (leb (S m) (S n1*S n1));simplify;reflexivity]
              |rewrite > H;elim (leb (S n1*S n1) m);simplify;reflexivity]
           |assumption]]]]
qed.

theorem log_pi_p : \forall n,b,f,g.S O < b \to
  log b (pi_p n f g) \leq 
    (sigma_p n f (\lambda x.S O)) + (sigma_p n f (\lambda x.log b (g x))).
intros;elim n
  [simplify;rewrite < times_n_SO;apply (leb_elim b (S O))
    [intro;elim (lt_to_not_le ? ? H);assumption
    |intro;simplify;apply le_n]
  |apply (bool_elim ? (f n1))
    [intro;rewrite > true_to_pi_p_Sn
       [rewrite > true_to_sigma_p_Sn
          [rewrite > true_to_sigma_p_Sn
             [apply (trans_le ? (S ((log b (g n1)) + (log b (pi_p n1 f g)))))
                [apply log_times;assumption
                |rewrite > assoc_plus;
                 change in \vdash (? ? %) with (S (sigma_p n1 f (\lambda x.S O)+(log b (g n1)+sigma_p n1 f (\lambda x.log b (g x)))));
                 apply le_S_S;rewrite < assoc_plus;
                 rewrite > sym_plus in \vdash (? ? (? % ?));
                 rewrite > assoc_plus;apply le_plus;
                   [apply le_n]]]]]
     assumption
    |intro;rewrite > false_to_pi_p_Sn
       [rewrite > false_to_sigma_p_Sn
          [rewrite > false_to_sigma_p_Sn]]
     assumption]]
qed.

axiom daemon : False.
(*
lemma lt_log_to_lt : \forall b,m,n.S O < b \to log b m < log b n \to m < n.
intros;apply not_le_to_lt;intro;elim (le_to_not_lt ? ? (le_log ? ? ? H H2));
assumption.
qed.

theorem ababbs: \forall n,a,b.S O < b \to O < n \to n < exp b a \to log b n < a.
intros;unfold log;apply not_le_to_lt;intro;apply (lt_to_not_le ? ? H2);
elim (le_to_or_lt_eq ? ? H3)
  [apply lt_to_le;apply (lt_log_to_lt b ? ? H);rewrite > eq_log_exp;assumption
  |apply (trans_le ? (exp b (log b n)))
     [rewrite < H4;apply le_n
     |apply le_exp_log;assumption]]
qed.

theorem exp_exp_to_log : \forall b,n,k.S O < b \to
exp b k \leq n \to n < exp b (S k) \to log b n = k.
intros;unfold log;lapply (ababbs ? ? ? H ? H2)
  [apply (trans_le ? ? ? ? H1);apply lt_O_exp
  |unfold log in Hletin;lapply (le_to_leb_true ? ? H1);
   lapply (f_m_to_le_max (λx:nat.leb ((b)\sup(x)) n) n ? ? Hletin1)
     [
  elim (le_to_or_lt_eq ? ? (le_S_S_to_le ? ? Hletin))
     [unfold log in H3;
]]elim daemon.
qed.

theorem xxx_log : \forall a,b.S O < b \to O < a \to log b (b*a) = S (log b a).
intros 3;elim a
  [elim (not_le_Sn_O ? H1);
  |apply (inj_exp_r b)
     [assumption
     |*)

theorem le_log_C2_sigma_p : \forall n,b. S O < b \to
log b (C2 n) \leq 
(sigma_p (S n) (\lambda x.(primeb x) \land (leb (S n) (x*x))) (\lambda x.S O)) +
(prim n + (((sigma_p n (\lambda x.leb (S n) (x*x)) (\lambda i.prim i * S (n!/i)))
  *(S (log b 3)))/n!)).
intros;unfold C2;
apply (trans_le ? (sigma_p (S n) (λx:nat.primeb x∧leb (S n) (x*x)) (λx:nat.1)
+sigma_p (S n) (λx:nat.primeb x∧leb (S n) (x*x))
 (λi.log b (S (n/i)))))
  [apply log_pi_p;assumption
  |apply le_plus
     [apply le_n
     |apply (trans_le ? (sigma_p (S n) (λx:nat.primeb x∧leb (S n) (x*x)) (λi:nat.S (log b (n/i)))))
        [apply le_sigma_p;intros;cut (log b (b*(n/i)) = S (log b (n/i)))
           [rewrite < Hcut;apply le_log
              [assumption
              |elim H
                 [rewrite < times_SSO_n;change in \vdash (? % ?) with (S O + (n/i));
                  apply le_plus;
                    [apply le_times_to_le_div
                       [apply (prime_to_lt_O i (primeb_true_to_prime ? (andb_true_true ? ? H2)));
                       |rewrite < times_n_SO;apply le_S_S_to_le;assumption]
                    |apply le_n]
                 |apply (trans_le ? ? ? H4);apply le_times_l;apply le_S;apply le_n]]
           |rewrite > exp_n_SO in ⊢ (? ? (? ? (? % ?)) ?);
            rewrite > log_exp;
              [reflexivity
              |assumption
              |apply le_times_to_le_div; 
                 [apply (prime_to_lt_O i (primeb_true_to_prime ? (andb_true_true ? ? H2)));
                 |rewrite < times_n_SO;apply le_S_S_to_le;assumption]]]
        |change in ⊢ (? (? ? ? (λi:?.%)) ?) with ((S O) + (log b (n/i)));
         rewrite > (sigma_p_plus_1 ? (\lambda x.S O));
         apply le_plus
           [unfold prim;apply le_sigma_p1;intros;elim (leb (S n) (i*i));
              [rewrite > andb_sym;apply le_n
              |rewrite > andb_sym;apply le_O_n]
           |apply sigma_p_log_div;assumption]]]]
qed.
(* 
 
lemma le_prim_n_stima : \forall n,b. S O < b \to b \leq n \to
prim n \leq (S (((S (S (S (S O))))*(S (log b (pred n)))) + 
              ((S (S (S (S O))))*n)))/(log b n).
(* la stima del secondo addendo è ottenuta considerando che 
   logreale 2 è sempre <= 1 (si dimostra per casi: b = 2, b > 2) *)
intros;apply le_times_to_le_div;
  [apply lt_O_log;
     [apply (trans_le ? b)
        [apply lt_to_le;assumption
        |assumption]
     |assumption]
  |apply (trans_le ? (log b (exp n (prim n))))
     [rewrite > sym_times;apply log_exp2
        [assumption
        |apply (trans_le ? b ? ? H1);apply lt_to_le;assumption]
     |apply (trans_le ? (log b ((exp (pred n) (S (S (S (S O)))))
                               *(exp (S (S O)) ((S (S (S (S O))))*n))))) 
        [apply le_log
           [assumption
           |apply le_exp_primr;apply (trans_le ? ? ? H H1)]
        |apply (trans_le ? (S ((log b (exp (pred n) (S (S (S (S O)))))) +
                              (log b (exp (S (S O)) ((S (S (S (S O))))*n))))))
           [apply log_times;assumption
           |apply le_S_S;apply le_plus
              [apply log_exp1;assumption
              |cases H
                 [rewrite > times_n_SO in \vdash (? (? ? %) ?);
                  rewrite > log_exp
                    [rewrite < plus_n_O;apply le_n
                    |apply le_n
                    |apply le_n]
                 |apply (trans_le ? (((S (S (S (S O))))*n)*(S (log (S m) (S (S O))))))
                    [apply log_exp1;apply le_S;assumption
                    |rewrite > times_n_SO in \vdash (? ? %);
                     apply le_times_r;apply le_S_S;
                     rewrite > lt_to_log_O
                       [apply le_n
                       |apply lt_O_S
                       |apply le_S_S;assumption]]]]]]]]
qed.

theorem le_log_C2_stima : \forall n,b. S O < b \to b*b < n \to
log b (C2 n) \leq 
(*(sigma_p (S n) (\lambda x.(primeb x) \land (leb (S n) (x*x))) (\lambda x.S O)) +*)
((S (((S (S (S (S O))))*(S (log b (pred n)))) + 
              ((S (S (S (S O))))*n)))/(log b n)) +
(((S (((S (S (S (S O))))*(S (log b (pred n)))) + 
              ((S (S (S (S O))))*n)))/(log b n)) + 
 (((sigma_p n (\lambda x.leb (S n) (x*x)) 
              (\lambda i.((S (((S (S (S (S O))))*(S (log b (pred i)))) + 
              ((S (S (S (S O))))*i)))/(log b i))* S (n!/i)))
  *(S (log b (S (S (S O))))))/n!)).intros.
apply (trans_le ? ? ? (le_log_C2_sigma_p ? ? ?))
  [assumption
  |apply le_plus
     [apply (trans_le ? ? ? ? (le_prim_n_stima ? ? ? ?));
      [unfold prim;apply le_sigma_p1;intros;
       do 2 rewrite < times_n_SO;elim (primeb i)
        [elim (leb (S n) (i*i));simplify [apply le_n|apply le_O_n]
        |simplify;apply le_n]
      |assumption
      |apply (trans_le ? ? ? ? H1);apply le_S;apply le_times_n;
       apply lt_to_le;assumption]
   |apply le_plus
     [apply le_prim_n_stima;
       [assumption
       |apply (trans_le ? (b*b))
          [apply le_times_n;apply lt_to_le;assumption
          |apply lt_to_le;assumption]]
     |apply monotonic_div
        [apply lt_O_fact
        |apply le_times_l;apply le_sigma_p;intros;apply le_times_l;
         apply le_prim_n_stima
           [assumption
           |apply (le_exp_to_le1 ? ? (S (S O)));
              [apply le_S;apply le_n
              |do 2 rewrite > exp_SSO;apply (trans_le ? n)
                 [apply lt_to_le;assumption
                 |apply lt_to_le;apply leb_true_to_le;assumption]]]]]]]
qed.

lemma log_interval : \forall b,k,n. S O < b \to exp b k \leq n \to n < exp b (S k) \to
                       log b n = k.
intros 2.elim k
  [simplify in H2;rewrite < times_n_SO in H2;apply lt_to_log_O;assumption
  |cut (log b n1 < S (S n))
     [cut (n < log b n1)
        [apply antisymmetric_le
           [apply le_S_S_to_le;assumption
           |assumption]
        |apply (trans_le ? (log b (exp b (S n))))
           [rewrite > eq_log_exp
              [apply le_n
              |assumption]
           |apply le_log;assumption]]
     |apply le_S_S;apply (trans_le ? (log b (pred (exp b (S (S n))))))
        [apply le_log
           [assumption
           |apply le_S_S_to_le;apply (trans_le ? ? ? H3);
            rewrite > minus_n_O in \vdash (? ? (? (? %)));
            rewrite < (eq_minus_S_pred (exp b (S (S n))) O);
            rewrite > minus_n_O in \vdash (? % ?);
            apply minus_le_S_minus_S]
        |unfold log;apply f_false_to_le_max;
           [apply (ex_intro ? ? (S n));split
              [apply (trans_le ? (exp b (S n)));
                 [apply lt_to_le;apply lt_m_exp_nm;assumption
                 |rewrite > minus_n_O in ⊢ (? ? (? %));
                  rewrite < eq_minus_S_pred;apply le_plus_to_minus_r;
                  rewrite > sym_plus;
                  change in \vdash (? % ?) with (S (O + exp b (S n)));
                  apply lt_minus_to_plus;
                  change in ⊢ (? ? (? % ?)) with (b * (exp b (S n)));
                  rewrite > times_n_SO in \vdash (? ? (? ? %));
                  rewrite > sym_times in \vdash (? ? (? % ?));
                  rewrite < distributive_times_minus;unfold lt;
                  rewrite > times_n_SO in \vdash (? % ?);apply le_times
                    [apply lt_O_exp;apply (trans_le ? ? ? ? H1);
                     apply le_S;apply le_n
                    |apply le_plus_to_minus_r;simplify;assumption]]
              |apply le_to_leb_true;
               rewrite > minus_n_O in \vdash (? ? (? %));
               rewrite < eq_minus_S_pred;apply le_plus_to_minus_r;
               rewrite > sym_plus;change in \vdash (? % ?) with (S (exp b (S n)));
               apply lt_exp;
                 [assumption
                 |apply le_n]]
           |intros;apply lt_to_leb_false;unfold lt;
            rewrite > minus_n_O in \vdash (? (? (? %)) ?);
            rewrite < eq_minus_S_pred;rewrite < minus_Sn_m
              [rewrite > minus_S_S;rewrite < minus_n_O;apply le_exp;
                 [apply (trans_le ? ? ? ? H1);apply le_S;apply le_n
                 |assumption]
              |apply lt_O_exp;apply (trans_le ? ? ? ? H1);apply le_S;apply le_n]]]]]
qed.              

lemma log_strano : \forall b,i.S O < b \to S O < i \to
                  ((S (S (S (S O)))) * log b (pred i)) + (S (S (S (S (S O))))) \leq
                  (S (S (S O)))*i.
alias num (instance 0) = "natural number".
cut (\forall b,i,k.S O < b \to S O < i \to
            (exp b k) \leq i-1 \to i-1 < (exp b (S k)) \to
                  ((S (S (S (S O)))) * log b (pred i)) + (S (S (S (S (S O))))) \leq
                  (S (S (S O)))*i)
  [intros;apply (Hcut ? ? (log b (i-1)) H H1);
     [apply le_exp_log;rewrite > (minus_n_n 1) in \vdash (? % ?);
      apply lt_plus_to_lt_minus;
        [apply le_n
        |rewrite < eq_minus_plus_plus_minus
           [rewrite > sym_plus;rewrite > eq_minus_plus_plus_minus;
              [rewrite < minus_n_n;rewrite < plus_n_O;assumption
              |apply le_n]
           |apply lt_to_le;assumption]]
     |apply lt_exp_log;assumption]
  |intros;rewrite > minus_n_O in ⊢ (? (? (? ? (? ? (? %))) ?) ?);
   rewrite < eq_minus_S_pred;rewrite > (log_interval ? k)
     [apply (trans_le ? (3*(exp b k) + 3))
        [change in \vdash (? (? ? %) ?) with (2+3);
         rewrite < assoc_plus;apply le_plus_l;
         elim k
           [simplify;apply le_S;apply le_n
           |elim (decidable_eq_nat O n)
              [rewrite < H5;apply (trans_le ? (3*(exp 2 1)));
                 [simplify;apply le_n
                 |apply le_times_r;apply monotonic_exp1;assumption]
              |rewrite < times_n_Sm;apply (trans_le ? (3*(exp b n) + 4))
                 [rewrite > assoc_plus;rewrite > sym_plus;apply le_plus_l;
                  assumption
                 |rewrite < sym_plus;change in \vdash (? % ?) with (S (3 + (3*(exp b n))));
                  apply lt_minus_to_plus;
                  change in ⊢ (? ? (? (? ? %) ?)) with (b*(exp b n));
                  rewrite > sym_times in \vdash (? ? (? (? ? %) ?));
                  rewrite < assoc_times;
                  rewrite > times_n_SO in ⊢ (? ? (? ? (? ? %)));
                  rewrite < assoc_times;rewrite < distr_times_minus;
                  apply (trans_le ? (3*2*1))
                    [simplify;apply le_S;apply le_S;apply le_n
                    |apply le_times
                       [apply le_times_r;apply (trans_le ? (exp 2 n))
                          [rewrite > exp_n_SO in \vdash (? % ?);apply le_exp
                             [apply le_S;apply le_n
                             |generalize in match H5;cases n
                                [intro;elim H6;reflexivity
                                |intro;apply le_S_S;apply le_O_n]]
                          |apply monotonic_exp1;assumption]
                       |apply le_S_S_to_le;rewrite < minus_Sn_m;
                          [simplify;rewrite < minus_n_O;assumption
                          |apply lt_to_le;assumption]]]]]]
        |rewrite > times_n_SO in \vdash (? (? ? %) ?);
         rewrite < distr_times_plus;apply le_times_r;
         rewrite < plus_n_SO;apply (trans_le ? (S (i-1)))
           [apply le_S_S;assumption
           |rewrite < minus_Sn_m
              [simplify;rewrite < minus_n_O;apply le_n
              |apply lt_to_le;assumption]]]
     |assumption
     |assumption
     |assumption]]
qed.
                  
alias num (instance 0) = "natural number".
lemma le_sigma_p_lemma1 : \forall n,b. S O < b \to b*b < n \to
            (sigma_p n (\lambda x.leb (S n) (x*x)) 
              (\lambda i.((S (((S (S (S (S O))))*(S (log b (pred i)))) + 
              ((S (S (S (S O))))*i)))/(log b i))* S (n!/i)))
            \leq ((28 * n * n!)/(pred (log b n))).
intros.apply (trans_le ? (sigma_p n (\lambda x.leb (S n) (x*x)) (\lambda i. ((7*i)/(log b i))*(S (n!/i)))))
  [apply le_sigma_p;intros;cut (b \leq i)
     [cut (1 < i) [|apply (trans_le ? ? ? H Hcut)]
      apply le_times_l;apply monotonic_div
        [apply lt_O_log
           [generalize in match H3;cases i
              [simplify;intros;destruct H4
              |intro;apply le_S_S;apply le_O_n]
           |assumption]
        |rewrite > sym_times;simplify in ⊢ (? (? (? % ?)) ?);
         change in ⊢ (? % ?) with (1 + ((4 + (log b (pred i) * 4)) + 4*i));
         rewrite > assoc_plus;rewrite < assoc_plus;
         simplify in \vdash (? (? % ?) ?);rewrite < assoc_plus;
         apply (trans_le ? (3*i + 4*i))
           [apply le_minus_to_plus;rewrite > eq_minus_plus_plus_minus
              [rewrite < minus_n_n;rewrite < plus_n_O;
               rewrite > sym_plus;rewrite > sym_times;apply log_strano
                 [assumption
                 |lapply (leb_true_to_le ? ? H3);apply (trans_le ? ? ? H);
                  apply (le_exp_to_le1 ? ? 2);
                    [apply le_S_S;apply le_O_n
                    |apply lt_to_le;do 2 rewrite > exp_SSO;apply (trans_le ? ? ? H1);
                     apply lt_to_le;assumption]]
              |apply le_n]
           |rewrite > sym_times in \vdash (? (? % ?) ?);
            rewrite > sym_times in \vdash (? (? ? %) ?);
            rewrite < distr_times_plus;rewrite > sym_times;apply le_n]]
     |apply (le_exp_to_le1 ? ? 2);
        [apply le_S_S;apply le_O_n
        |apply lt_to_le;do 2 rewrite > exp_SSO;apply (trans_le ? ? ? H1);
         apply (trans_le ? ? ? ? (leb_true_to_le ? ? H3));apply le_S;
         apply le_n]]
  |apply (trans_le ? (sigma_p n (λx:nat.leb (S n) (x*x)) (λi:nat.7*i/log b i*((2*(n!))/i))))
     [apply le_sigma_p;intros;apply le_times_r;apply (trans_le ? (n!/i + n!/i))
        [change in \vdash (? % ?) with (1 + n!/i);apply le_plus_l;
         apply le_times_to_le_div
           [generalize in match H3;cases i;simplify;intro
              [destruct H4
              |apply le_S_S;apply le_O_n]
           |generalize in match H2;cases n;intro
              [elim (not_le_Sn_O ? H4)
              |change in \vdash (? ? %) with ((S n1)*(n1!));apply le_times
                 [apply lt_to_le;assumption
                 |apply lt_O_fact]]]
        |rewrite > plus_n_O in \vdash (? (? ? %) ?);
         change in \vdash (? % ?) with (2 * (n!/i));
         apply le_times_div_div_times;
         generalize in match H3;cases i;simplify;intro
           [destruct H4
           |apply le_S_S;apply le_O_n]]
     |apply (trans_le ? (sigma_p n (\lambda x:nat.leb (S n) (x*x)) (\lambda i.((14*(n!))/log b i))))
        [apply le_sigma_p;intros;
         cut (b \leq i)
           [|apply (le_exp_to_le1 ? ? 2);
              [apply le_S_S;apply le_O_n
              |apply lt_to_le;do 2 rewrite > exp_SSO;apply (trans_le ? ? ? H1);
               apply (trans_le ? ? ? ? (leb_true_to_le ? ? H3));apply le_S;
               apply le_n]]
         cut (1 < i)
           [|apply (trans_le ? ? ? H Hcut)]
         change in ⊢ (? ? (? % ?)) with ((7*2)*(n!));
         rewrite > assoc_times in \vdash (? ? (? % ?));
         apply (trans_le ? ? ? (le_times_div_div_times ? ? ? ?));
           [apply lt_to_le;assumption
           |rewrite > (eq_div_div_times ? ? 7)
              [rewrite > sym_times in ⊢ (? (? (? ? %) ?) ?);
               rewrite < assoc_times in \vdash (? (? % ?) ?);
               apply (trans_le ? ? ? (le_div_times_m ? ? ? ? ?))
                 [apply lt_O_log
                    [apply lt_to_le;assumption
                    |assumption]
                 |unfold lt;rewrite > times_n_SO in \vdash (? % ?);
                  apply le_times;
                    [apply le_S_S;apply le_O_n
                    |apply lt_to_le;assumption]
                 |apply le_n]
              |apply le_S_S;apply le_O_n
              |apply lt_to_le;assumption]]
        |apply (trans_le ? (sigma_p (S n) (\lambda x.leb (S n) (x*x))
                      (\lambda i.14*n!/log b i)))
           [apply (bool_elim ? (leb (S n) (n*n)));intro
              [rewrite > true_to_sigma_p_Sn
                 [rewrite > sym_plus;rewrite > plus_n_O in \vdash (? % ?);
                  apply le_plus_r;apply le_O_n
                 |assumption]
              |rewrite > false_to_sigma_p_Sn
                 [apply le_n
                 |assumption]]
           |apply (trans_le ? ? ? (le_sigma_p_div_log_div_pred_log ? ? ? ? ?));
              [assumption
              |apply lt_to_le;assumption
              |rewrite < assoc_times;
               rewrite > sym_times in ⊢ (? (? (? % ?) ?) ?);
               rewrite < assoc_times;apply le_n]]]]]
qed.

theorem le_log_C2_stima2 : \forall n,b. S O < b \to b*b < n \to
log b (C2 n) \leq 
(14*n/(log b n)) + 
 ((((28*n*n!)/pred (log b n))
  *(S (log b (S (S (S O))))))/n!).intros.
apply (trans_le ? ? ? (le_log_C2_stima ? ? H H1));
rewrite < assoc_plus in \vdash (? % ?);apply le_plus
  [rewrite > times_SSO_n in \vdash (? % ?);
   apply (trans_le ? ? ? (le_times_div_div_times ? ? ? ?))
     [apply lt_O_log
       [apply (trans_le ? (b*b))
          [rewrite > times_n_SO;apply le_times;apply lt_to_le;assumption
          |apply lt_to_le;assumption]
       |apply (trans_le ? (b*b))
          [rewrite > times_n_SO in \vdash (? % ?);apply le_times
             [apply le_n|apply lt_to_le;assumption]
          |apply lt_to_le;assumption]]
     |change in \vdash (? ? (? (? % ?) ?)) with (2*7);
      apply monotonic_div;
        [apply lt_O_log
          [apply (trans_le ? (b*b))
             [rewrite > times_n_SO;apply le_times;apply lt_to_le;assumption
             |apply lt_to_le;assumption]
          |apply (trans_le ? (b*b))
             [rewrite > times_n_SO in \vdash (? % ?);apply le_times
                [apply le_n|apply lt_to_le;assumption]
             |apply lt_to_le;assumption]]
        |rewrite > assoc_times;apply le_times_r;
         change in \vdash (? (? (? (? ? %) ?)) ?) with (1 + (log b (pred n)));
         rewrite > distr_times_plus;
         change in \vdash (? % ?) with (1 + (4*1+4*log b (pred n)+4*n));
         do 2 rewrite < assoc_plus;simplify in ⊢ (? (? (? % ?) ?) ?);
         change in ⊢ (? ? %) with ((3+4)*n);rewrite > sym_times in \vdash (? ? %);
         rewrite > distr_times_plus;
         rewrite > sym_times in \vdash (? ? (? % ?));
         rewrite > sym_times in \vdash (? ? (? ? %));
         apply le_plus_l;rewrite > sym_plus;apply log_strano
           [assumption
           |apply (trans_le ? ? ? H);apply (trans_le ? (b*b))
              [rewrite > times_n_SO in \vdash (? % ?);
               apply le_times_r;apply lt_to_le;assumption
              |apply lt_to_le;assumption]]]]
  |apply monotonic_div
     [apply lt_O_fact
     |apply le_times_l;apply (le_sigma_p_lemma1 ? ? H H1)]] 
qed.

theorem le_log_C2_stima3 : \forall n,b. S O < b \to b*b < n \to
log b (C2 n) \leq 
(14*n/(log b n)) + 
 ((28*n)*(S (log b (S (S (S O)))))/pred (log b n)).intros.
apply (trans_le ? ? ? (le_log_C2_stima2 ? ? H H1));apply le_plus_r;
(*apply (trans_le ? ((28*n)*(28*n*n!/pred (log b n)*S (log b 3)/(28*n*n!))))
  [*)
rewrite > (eq_div_div_times ? ? (28*n)) in \vdash (? % ?)
  [rewrite > sym_times in ⊢ (? (? (? ? %) ?) ?);
   rewrite < assoc_times;
   apply le_div_times_m;
     [apply (trans_le ? (pred (log b (b*b))))
        [rewrite < exp_SSO;rewrite > eq_log_exp;
           [apply le_n
           |assumption]
        |rewrite < exp_SSO;rewrite > eq_log_exp;
           [simplify;rewrite > minus_n_O in \vdash (? ? (? %));
            rewrite < eq_minus_S_pred;
            apply le_plus_to_minus_r;simplify;
            rewrite < (eq_log_exp b 2);
              [apply le_log
                 [assumption
                 |rewrite > exp_SSO;apply lt_to_le;assumption]
              |assumption]
           |assumption]]
     |unfold lt;rewrite > times_n_SO in \vdash (? % ?);apply le_times
        [rewrite > times_n_SO in \vdash (? % ?);apply le_times
           [apply le_S_S;apply le_O_n
           |apply (trans_le ? ? ? ? H1);apply le_S_S;
            rewrite > times_n_SO;apply le_times
              [apply le_O_n
              |apply lt_to_le;assumption]]
        |apply lt_O_fact]]
  |unfold lt;rewrite > times_n_SO in \vdash (? % ?);apply le_times
     [apply le_S_S;apply le_O_n
     |apply (trans_le ? ? ? ? H1);apply le_S_S;
      rewrite > times_n_SO;apply le_times
        [apply le_O_n
        |apply lt_to_le;assumption]]
  |apply lt_O_fact]
qed.

lemma le_prim_log1: \forall n,b. S O < b \to O < n \to 
                     (prim n)*(log b n) \leq
                     log b (A n) + log b (C1 n) + log b (C2 n) + 2.
intros.change in \vdash (? ? (? ? %)) with (1+1).
rewrite < assoc_plus;rewrite > assoc_plus in ⊢ (? ? (? (? % ?) ?)).
rewrite > assoc_plus in ⊢ (? ? (? % ?));
apply (trans_le ? (log b (A n) + (log b (C1 n * C2 n)) + 1));
  [apply (trans_le ? (log b (A n * (C1 n * C2 n))))
     [apply (trans_le ? (log b (exp n (prim n))))
        [apply log_exp2;assumption
        |apply le_log
           [assumption
           |rewrite < jj;apply asdasd]]
     |rewrite > sym_plus;simplify;apply log_times;assumption]
  |apply le_plus_l;apply le_plus_r;rewrite > sym_plus;simplify;apply log_times;
   assumption]
qed.

lemma le_log_A1 : \forall n,b. S O < b \to S O < n \to
                  log b (A n) \leq 2*(S (log b (pred n))) + (2*(pred n))*(S (log b 2)) + 1.
intros.apply (trans_le ? (log b ((exp (pred n) 2)*(exp 2 (2*(pred n))))))
  [apply le_log
     [assumption
     |simplify in ⊢ (? ? (? (? % ?) ?));apply le_A_exp4;assumption]
  |rewrite < sym_plus;apply (trans_le ? (1 + ((log b (exp (pred n) 2)) + (log b (exp 2 (2*(pred n)))))));
     [change in \vdash (? ? %) with (S (log b ((pred n)\sup(2))+log b ((2)\sup(2*(pred n)))));
      apply log_times;assumption
     |apply le_plus_r;apply le_plus;apply log_exp1;assumption]]
qed.

lemma le_theta_pi_A : \forall n.theta_pi n \leq A n.
intro.unfold theta_pi.unfold A.apply le_pi_p.intros.
rewrite > exp_n_SO in \vdash (? % ?).
cut (O < i)
  [apply le_exp
     [assumption
     |apply lt_O_log
        [apply (trans_le ? ? ? Hcut);apply le_S_S_to_le;assumption
        |apply le_S_S_to_le;assumption]]
  |apply prime_to_lt_O;apply primeb_true_to_prime;assumption]
qed.

definition sqrt \def
  \lambda n.max n (\lambda x.leb (x*x) n).
  
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
  
theorem eq_theta_pi_sqrt_C1 : \forall n. theta_pi (sqrt n) = C1 n.
intro;unfold theta_pi;unfold C1;rewrite > (false_to_eq_pi_p (S (sqrt n)) (S n))
  [generalize in match (le_sqrt_to_le_times_l n);elim (sqrt n)
     [simplify;reflexivity
     |apply (bool_elim ? (primeb (S n1)))
        [intro;rewrite > true_to_pi_p_Sn
           [rewrite > true_to_pi_p_Sn in \vdash (? ? ? %)
              [apply eq_f2
                 [reflexivity
                 |apply H;intros;apply H1;apply le_S;assumption]
              |apply (andb_elim (primeb (S n1)) (leb (S n1 * S n1) n));
               rewrite > H2;whd;apply le_to_leb_true;apply H1;apply le_n]
           |assumption]
        |intro;rewrite > false_to_pi_p_Sn
           [rewrite > false_to_pi_p_Sn in \vdash (? ? ? %)
              [apply H;intros;apply H1;apply le_S;assumption
              |apply (andb_elim (primeb (S n1)) (leb (S n1 * S n1) n));
               rewrite > H2;whd;reflexivity]
           |assumption]]]
  |apply le_S_S;unfold sqrt;apply le_max_n
  |intros;apply (andb_elim (primeb i) (leb (i*i) n));elim (primeb i);simplify
     [rewrite > lt_to_leb_false
        [reflexivity
        |apply le_sqrt_to_le_times_r;assumption]
     |reflexivity]]
qed.

lemma le_sqrt_n_n : \forall n.sqrt n \leq n.
intro.unfold sqrt.apply le_max_n.
qed.

lemma le_prim_log_stima: \forall n,b. S O < b \to b < sqrt n \to 
                     (prim n)*(log b n) \leq
                      2*S (log b (pred n))+2*(pred n)*S (log b 2)
                      +(2*S (log b (pred (sqrt n)))+2*(pred (sqrt n))*S (log b 2))
                      +(14*n/log b n+28*n*S (log b 3)/pred (log b n))
                      +4.
intros.cut (1 < n)
  [apply (trans_le ? ((2*(S (log b (pred n))) + (2*(pred n))*(S (log b 2)) + 1) + 
                     (2*(S (log b (pred (sqrt n)))) + (2*(pred (sqrt n)))*(S (log b 2)) + 1) +
                     ((14*n/(log b n)) + ((28*n)*(S (log b (S (S (S O)))))/pred (log b n))) + 2))
    [apply (trans_le ? ? ? (le_prim_log1 ? ? H ?))
       [apply lt_to_le;assumption
       |apply le_plus_l;apply le_plus
          [apply le_plus
             [apply le_log_A1;assumption
             |rewrite < eq_theta_pi_sqrt_C1;apply (trans_le ? (log b (A (sqrt n))))
                [apply le_log
                   [assumption
                   |apply le_theta_pi_A]
                |apply le_log_A1
                   [assumption
                   |apply (trans_le ? ? ? H);apply lt_to_le;assumption]]]
          |apply le_log_C2_stima3;
             [assumption
             |apply lt_sqrt_to_le_times_l;assumption]]]
    |rewrite > assoc_plus in ⊢ (? (? % ?) ?);
     rewrite > sym_plus in ⊢ (? (? (? ? %) ?) ?);
     rewrite > assoc_plus in \vdash (? % ?);
     rewrite > assoc_plus in ⊢ (? (? ? %) ?);
     rewrite > assoc_plus in ⊢ (? (? % ?) ?);
     rewrite > assoc_plus in \vdash (? % ?);
     rewrite < assoc_plus in ⊢ (? (? ? %) ?);
     rewrite > assoc_plus in ⊢ (? (? ? (? % ?)) ?);
     rewrite > sym_plus in ⊢ (? (? ? (? (? ? %) ?)) ?);
     rewrite < assoc_plus in ⊢ (? (? ? (? % ?)) ?);
     rewrite < assoc_plus in \vdash (? % ?);
     rewrite < assoc_plus in ⊢ (? (? % ?) ?);
     rewrite > assoc_plus in \vdash (? % ?);
     rewrite > sym_plus in ⊢ (? (? ? %) ?);
     rewrite > assoc_plus in ⊢ (? (? ? %) ?);
     rewrite > assoc_plus in ⊢ (? (? ? (? % ?)) ?);
     rewrite > assoc_plus in ⊢ (? (? ? %) ?);     
     rewrite > assoc_plus in ⊢ (? (? ? (? ? %)) ?);
     simplify in ⊢ (? (? ? (? ? (? ? %))) ?);
     rewrite < assoc_plus in ⊢ (? (? ? %) ?);
     rewrite < assoc_plus in ⊢ (? % ?);apply le_plus_l;
     rewrite > assoc_plus in \vdash (? % ?);
     rewrite > assoc_plus in ⊢ (? (? ? %) ?);
     rewrite > sym_plus in ⊢ (? (? ? (? ? %)) ?);
     rewrite < assoc_plus in ⊢ (? (? ? %) ?);
     rewrite < assoc_plus in \vdash (? % ?);apply le_plus_l;
     rewrite > assoc_plus in \vdash (? ? %);apply le_n]
  |apply (trans_le ? ? ? H);apply lt_to_le;apply (trans_le ? ? ? H1);
   apply le_sqrt_n_n]
qed.

lemma eq_div_div_div_times: \forall a,b,c. O < b \to O < c \to a/b/c = a/(b*c).
intros.rewrite > (div_mod a (b*c)) in \vdash (? ? % ?)
 [rewrite > (div_mod (a \mod (b*c)) b)
    [rewrite < assoc_plus;
     rewrite > sym_times in ⊢ (? ? (? (? (? (? (? ? %) ?) ?) ?) ?) ?);
     rewrite < assoc_times in ⊢ (? ? (? (? (? (? % ?) ?) ?) ?) ?);
     rewrite > sym_times in ⊢ (? ? (? (? (? (? % ?) ?) ?) ?) ?);
     rewrite > sym_times in ⊢ (? ? (? (? (? (? ? %) ?) ?) ?) ?);
     rewrite < distr_times_plus;rewrite < sym_times in ⊢ (? ? (? (? (? % ?) ?) ?) ?);
     rewrite > (div_plus_times b)
       [rewrite > (div_plus_times c)
          [reflexivity
          |apply lt_times_to_lt_div;rewrite > sym_times in \vdash (? ? %);
           apply lt_mod_m_m;unfold lt;rewrite > times_n_SO;apply le_times;assumption]
       |apply lt_mod_m_m;assumption]
    |assumption]
 |unfold lt;rewrite > times_n_SO;apply le_times;assumption]
qed.

lemma le_prim_stima: \forall n,b. S O < b \to b < sqrt n \to 
                     (prim n) \leq 
                      2*S (log b (pred n))/(log b n) + 2*(pred n)*S (log b 2)/(log b n)
                      +2*S (log b (pred (sqrt n)))/(log b n)+ 2*(pred (sqrt n))*S (log b 2)/(log b n)
                      + 14*n/(log b n * log b n) + 28*n*S (log b 3)/(pred (log b n) * log b n)
                      +4/(log b n) + 6.
intros;
cut (O < log b n) 
  [|apply lt_O_log;
        [apply lt_to_le;apply (trans_le ? ? ? H);apply (trans_le ? (sqrt n))
           [apply lt_to_le;assumption
           |apply le_sqrt_n_n;]
        |apply (trans_le ? (sqrt n))
           [apply lt_to_le;assumption
           |apply le_sqrt_n_n]]]
apply (trans_le ? ((2*S (log b (pred n))+2*(pred n)*S (log b 2)
                      +(2*S (log b (pred (sqrt n)))+2*(pred (sqrt n))*S (log b 2))
                      +(14*n/log b n+28*n*S (log b 3)/pred (log b n))
                      +4)/(log b n)))
  [apply le_times_to_le_div
     [assumption
     |rewrite > sym_times;apply le_prim_log_stima;assumption]
  |apply (trans_le ? ? ? (le_div_plus_S (2*S (log b (pred n))+2*(pred n)*S (log b 2)
+(2*S (log b (pred (sqrt n)))+2*(pred (sqrt n))*S (log b 2))
+(14*n/log b n+28*n*S (log b 3)/pred (log b n))) 4 (log b n) ?))
     [assumption
     |rewrite < plus_n_Sm;apply le_S_S;rewrite > assoc_plus in \vdash (? ? %);
      rewrite > sym_plus in \vdash (? ? (? ? %));
      rewrite < assoc_plus in \vdash (? ? %);
      apply le_plus_l;apply (trans_le ? ? ? (le_div_plus_S (2*S (log b (pred n))+2*(pred n)*S (log b 2)
+(2*S (log b (pred (sqrt n)))+2*(pred (sqrt n))*S (log b 2))) (14*n/log b n+28*n*S (log b 3)/pred (log b n)) (log b n) ?));
         [assumption
         |rewrite < plus_n_Sm in \vdash (? ? %);apply le_S_S;
          change in \vdash (? ? (? ? %)) with (1+3);
          rewrite < assoc_plus in \vdash (? ? %);
          rewrite > assoc_plus in ⊢ (? ? (? (? % ?) ?));
          rewrite > assoc_plus in ⊢ (? ? (? % ?));
          rewrite > sym_plus in \vdash (? ? %);rewrite < assoc_plus in \vdash (? ? %);
          rewrite > sym_plus in \vdash (? ? (? % ?));apply le_plus
            [apply (trans_le ? ? ? (le_div_plus_S (2*S (log b (pred n))+2*pred n*S (log b 2)) (2*S (log b (pred (sqrt n)))+2*pred (sqrt n)*S (log b 2)) (log b n) ?))
               [assumption
               |rewrite < plus_n_Sm;apply le_S_S;change in \vdash (? ? (? ? %)) with (1+1);
                rewrite < assoc_plus in \vdash (? ? %);rewrite > assoc_plus in ⊢ (? ? (? (? % ?) ?));
                rewrite > assoc_plus in ⊢ (? ? (? % ?));
                rewrite > sym_plus in \vdash (? ? %);
                rewrite < assoc_plus in \vdash (? ? %);
                rewrite > sym_plus in \vdash (? ? (? % ?));
                apply le_plus
                  [rewrite < plus_n_Sm;rewrite < plus_n_O;apply le_div_plus_S;
                   assumption
                  |rewrite < plus_n_Sm;rewrite < plus_n_O;apply le_div_plus_S;
                   assumption]]
            |rewrite < plus_n_Sm;rewrite < plus_n_O;apply (trans_le ? ? ? (le_div_plus_S ? ? ? ?));
               [assumption
               |apply le_S_S;apply le_plus
                  [rewrite > eq_div_div_div_times;
                     [apply le_n
                     |*:assumption]
                  |rewrite > eq_div_div_div_times
                     [apply le_n
                     |rewrite > minus_n_O in \vdash (? ? (? %));
                      rewrite < eq_minus_S_pred;apply lt_to_lt_O_minus;
                      apply (trans_le ? (log b (sqrt n * sqrt n)))
                        [elim daemon;
                        |apply le_log;
                           [assumption
                           |elim daemon]]
                     |assumption]]]]]]]
qed.

lemma leq_sqrt_n : \forall n. sqrt n * sqrt n \leq n.
intro;unfold sqrt;apply leb_true_to_le;apply f_max_true;apply (ex_intro ? ? O);
split
  [apply le_O_n
  |simplify;reflexivity]
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
    
(* Bertrand weak, lavori in corso
          
theorem bertrand_weak : \forall n. 9 \leq n \to prim n < prim (4*n).
intros.
apply (trans_le ? ? ? (le_S_S ? ? (le_prim_stima ? 2 ? ?)))
  [apply le_n
  |unfold sqrt;apply f_m_to_le_max
     [do 6 apply lt_to_le;assumption
     |apply le_to_leb_true;assumption]
  |cut (pred ((4*n)/(S (log 2 (4*n)))) \leq prim (4*n))
     [|apply le_S_S_to_le;rewrite < S_pred
       [apply le_times_to_le_div2
          [apply lt_O_S
          |change in \vdash (? % (? (? (? %)) (? (? ? %)))) with (2*2*n);
           rewrite > assoc_times in \vdash (? % (? (? (? %)) (? (? ? %))));
           rewrite > sym_times in \vdash (? ? %);
           apply le_priml;rewrite > (times_n_O O) in \vdash (? % ?);
           apply lt_times;
             [apply lt_O_S
             |apply (trans_le ? ? ? ? H);apply le_S_S;apply le_O_n]]
       |apply le_times_to_le_div;
          [apply lt_O_S
          |rewrite < times_n_SO;apply (trans_le ? (S (S (2 + (log 2 n)))))
             [apply le_S_S;apply (log_times 2 4 n);apply le_S_S;apply le_n
             |change in \vdash (? % ?) with (4 + log 2 n);
              rewrite > S_pred in \vdash (? ? (? ? %));
                [change in ⊢ (? ? (? ? %)) with (1 + pred n);
                 rewrite > distr_times_plus;apply le_plus_r;elim H
                   [simplify;do 3 apply le_S_S;apply le_O_n
                   |apply (trans_le ? (log 2 (2*n1)))
                      [apply le_log;
                         [apply le_S_S;apply le_n
                         |rewrite < times_SSO_n;
                          change in \vdash (? % ?) with (1 + n1);
                          apply le_plus_l;apply (trans_le ? ? ? ? H1);
                          apply lt_O_S]
                      |apply (trans_le ? (S (4*pred n1)))
                         [rewrite > exp_n_SO in ⊢ (? (? ? (? % ?)) ?);
                          rewrite > log_exp
                            [change in \vdash (? ? %) with (1 + (4*pred n1));
                             apply le_plus_r;
                             assumption
                            |apply le_S_S;apply le_n
                            |apply (trans_le ? ? ? ? H1);apply le_S_S;apply le_O_n]
                         |simplify in \vdash (? ? (? ? %));
                          rewrite > minus_n_O in \vdash (? (? (? ? (? %))) ?);
                          rewrite < eq_minus_S_pred;
                          rewrite > distr_times_minus;
                          change in \vdash (? % ?) with (1 + (4*n1 - 4));
                          rewrite > eq_plus_minus_minus_minus
                            [simplify;apply le_minus_m;
                            |apply lt_O_S
                            |rewrite > times_n_SO in \vdash (? % ?);
                             apply le_times_r;apply (trans_le ? ? ? ? H1);
                             apply lt_O_S]]]]
                |apply (trans_le ? ? ? ? H);apply lt_O_S]]]]]
  apply (trans_le ? ? ? ? Hcut);
*)
*)