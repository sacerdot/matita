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
                    [rewrite > H1;rewrite > H2;rewrite < assoc_times;reflexivity
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

(*
  
theorem le_log_C2_stima : \forall n,b. S O < b \to
log b (C2 n) \leq 
(sigma_p (S n) (\lambda x.(primeb x) \land (leb (S n) (x*x))) (\lambda x.S O)) +
(((S (((S (S (S (S O))))*(S (log b (pred n)))) + 
              ((S (S (S (S O))))*n)))/(log b n)) + 
 (((sigma_p n (\lambda x.leb (S n) (x*x)) 
              (\lambda i.((S (((S (S (S (S O))))*(S (log b (pred n)))) + 
              ((S (S (S (S O))))*n)))/(log b n))* S (n!/i)))
  *(S (log b 3)))/n!)).
elim daemon.
  
theorem le_log_C2_sigma_p : \forall n,b. S O < b \to
log b (C2 n) \leq 
(sigma_p (S n) (\lambda x.(primeb x) \land (leb (S n) (x*x))) (\lambda x.S O)) +
(sigma_p (S n) (\lambda x.(primeb x) \land (leb (S n) (x*x))) 
   (\lambda p.(sigma_p (n+p) (\lambda i.leb p i) 
       (\lambda i.S ((n+p)!/i*(S (log b 3)))))/(n+p)!)).
intros;unfold C2;
apply (trans_le ? (sigma_p (S n) (λx:nat.primeb x∧leb (S n) (x*x)) (λx:nat.1)
+sigma_p (S n) (λx:nat.primeb x∧leb (S n) (x*x))
 (λi.log b (S (n/i)))))
  [apply log_pi_p;assumption
  |apply le_plus
     [apply le_n
     |apply le_sigma_p;intros;cut (S (n/i) = (n+i)/i)
        [rewrite > Hcut;apply le_log_div_sigma_p 
           [assumption
           |apply prime_to_lt_O;apply primeb_true_to_prime;
            elim (and_true ? ? H2);assumption
           |apply le_plus_n
           |apply le_n]
        |lapply (prime_to_lt_O i (primeb_true_to_prime ? (andb_true_true ? ? H2))) as H3;
         apply (div_mod_spec_to_eq (n+i) i (S (n/i)) (n \mod i) ? ((n+i) \mod i))
           [constructor 1
              [apply lt_mod_m_m;assumption
              |simplify;rewrite > assoc_plus;rewrite < div_mod;
                 [apply sym_plus
                 |assumption]]
           |apply div_mod_spec_div_mod;assumption]]]]
qed.
*)

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
