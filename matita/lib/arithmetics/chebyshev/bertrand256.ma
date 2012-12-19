(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  This file is distributed under the terms of the 
    \   /  GNU General Public License Version 2        
     \ /      
      V_______________________________________________________________ *)

include "arithmetics/chebyshev/chebyshev_teta.ma".

(* include "nat/sqrt.ma".
include "nat/chebyshev_teta.ma".
include "nat/chebyshev.ma".
include "list/in.ma".
include "list/sort.ma".
include "nat/o.ma".
include "nat/sieve.ma". *)

(*
let rec list_divides l n \def
  match l with
  [ nil ⇒ false
  | cons (m:nat) (tl:list nat) ⇒ orb (divides_b m n) (list_divides tl n) ].

definition lprim : nat \to list nat \def
  \lambda n.let rec aux m acc \def
     match m with 
     [ O => acc
     | S m1 => match (list_divides acc (n-m1)) with
       [ true => aux m1 acc
       | false => aux m1 (n-m1::acc)]]
  in aux (pred n) [].
  
let rec checker l \def
    match l with
      [ nil => true
      | cons h1 t1 => match t1 with
         [ nil => true
         | cons h2 t2 => (andb (checker t1) (leb h1 (2*h2))) ]].

lemma checker_cons : \forall t,l.checker (t::l) = true \to checker l = true.
intros 2;simplify;intro;elim l in H ⊢ %
  [reflexivity
  |change in H1 with (andb (checker (a::l1)) (leb t (a+(a+O))) = true);
   apply (andb_true_true ? ? H1)]
qed.

theorem checker_sound : \forall l1,l2,l,x,y.l = l1@(x::y::l2) \to 
                        checker l = true \to x \leq 2*y.
intro;elim l1 0
  [simplify;intros 5;rewrite > H;simplify;intro;
   apply leb_true_to_le;apply (andb_true_true_r ? ? H1);
  |simplify;intros;rewrite > H1 in H2;lapply (checker_cons ? ? H2);
   apply (H l2 ? ? ? ? Hletin);reflexivity]
qed.
*)

definition bertrand ≝ λn. ∃p.n < p ∧ p \le 2*n ∧ (prime p).

definition not_bertrand ≝ λn.∀p.n < p → p ≤ 2*n → \not (prime p).

lemma min_prim : ∀n.∃p. n < p ∧ prime p ∧
                 ∀q.prime q → q < p → q ≤ n.
#n cases (le_to_or_lt_eq ?? (le_O_n n)) #Hn
  [%{(min (S (n!)) (S n) primeb)} %
    [%[@le_min_l
      |@primeb_true_to_prime @(f_min_true primeb)
       cases (ex_prime n Hn) #p * * #ltnp #lep #primep
       %{p} % 
        [% [@ltnp | whd >(plus_n_O p) >plus_n_Sm @le_plus //]
        |@prime_to_primeb_true //
        ]
      ]
    |#p #primep #ltp @not_lt_to_le % #ltnp 
     lapply (lt_min_to_false … ltnp ltp)
     >(prime_to_primeb_true ? primep) #H destruct (H)
    ]
  |%{2} % 
    [%[<Hn @lt_O_S | @primeb_true_to_prime //]
    |#p #primep #lt2 @False_ind @(absurd … lt2)
     @le_to_not_lt @prime_to_lt_SO //
    ]
  ]
qed.

theorem list_of_primes_to_bertrand: \forall n,pn,l.0 < n \to prime pn \to n <pn \to
list_of_primes pn l  \to
(\forall p. prime p \to p \le pn \to in_list nat p l) \to 
(\forall p. in_list nat p l \to 2 < p \to
\exists pp. in_list nat pp l \land pp < p \land p \le 2*pp) \to bertrand n.
intros.
elim (min_prim n).
apply (ex_intro ? ? a).
elim H6.clear H6.elim H7.clear H7.
split
  [split
    [assumption
    |elim (le_to_or_lt_eq ? ? (prime_to_lt_SO ? H9))
      [elim (H5 a)
        [elim H10.clear H10.elim H11.clear H11.
         apply (trans_le ? ? ? H12).
         apply le_times_r.
         apply H8
          [unfold in H3.
           elim (H3 a1 H10).
           assumption
          |assumption
          ]
        |apply H4
          [assumption
          |apply not_lt_to_le.intro. 
           apply (lt_to_not_le ? ? H2).
           apply H8;assumption
          ]
        |assumption
        ]
      |rewrite < H7.
       apply O_lt_const_to_le_times_const.
       assumption
      ]
    ]
  |assumption
  ]
qed.

let rec check_list l \def
  match l with
  [ nil \Rightarrow true
  | cons (hd:nat) tl \Rightarrow
    match tl with
     [ nil \Rightarrow eqb hd 2
     | cons hd1 tl1 \Rightarrow 
      (leb (S hd1) hd \land leb hd (2*hd1) \land check_list tl)
    ]
  ]
.

lemma check_list1: \forall n,m,l.(check_list (n::m::l)) = true \to 
m < n \land n \le 2*m \land (check_list (m::l)) = true \land ((check_list l) = true).
intros 3.
change in ⊢ (? ? % ?→?) with (leb (S m) n \land leb n (2*m) \land check_list (m::l)).
intro.
lapply (andb_true_true ? ? H) as H1.
lapply (andb_true_true_r ? ? H) as H2.clear H.
lapply (andb_true_true ? ? H1) as H3.
lapply (andb_true_true_r ? ? H1) as H4.clear H1.
split
  [split
    [split
      [apply leb_true_to_le.assumption
      |apply leb_true_to_le.assumption
      ]
    |assumption
    ]
  |generalize in match H2.
   cases l
    [intro.reflexivity
    |change in ⊢ (? ? % ?→?) with (leb (S n1) m \land leb m (2*n1) \land check_list (n1::l1)).
     intro.
     lapply (andb_true_true_r ? ? H) as H2.
     assumption
    ]
  ]
qed.
    
theorem check_list2: \forall l. check_list l = true \to
\forall p. in_list nat p l \to 2 < p \to
\exists pp. in_list nat pp l \land pp < p \land p \le 2*pp.
intro.elim l 2
  [intros.apply False_ind.apply (not_in_list_nil ? ? H1)
  |cases l1;intros
    [lapply (in_list_singleton_to_eq ? ? ? H2) as H4.
     apply False_ind.
     apply (lt_to_not_eq ? ? H3).
     apply sym_eq.apply eqb_true_to_eq.
     rewrite > H4.apply H1
    |elim (check_list1 ? ? ? H1).clear H1.
     elim H4.clear H4.
     elim H1.clear H1.
     elim (in_list_cons_case ? ? ? ? H2)
      [apply (ex_intro ? ? n).
       split
        [split
          [apply in_list_cons.apply in_list_head
          |rewrite > H1.assumption
          ]
        |rewrite > H1.assumption
        ]
      |elim (H H6 p H1 H3).clear H.
       apply (ex_intro ? ? a1). 
       elim H8.clear H8.
       elim H.clear H.
       split
        [split
          [apply in_list_cons.assumption
          |assumption
          ]
        |assumption
        ]
      ]
    ]
  ]
qed.

(* qualcosa che non va con gli S *)
lemma le_to_bertrand : \forall n.O < n \to n \leq exp 2 8 \to bertrand n.
intros.
apply (list_of_primes_to_bertrand ? (S(exp 2 8)) (sieve (S(exp 2 8))))
  [assumption
  |apply primeb_true_to_prime.reflexivity
  |apply (le_to_lt_to_lt ? ? ? H1).
   apply le_n
  |lapply (sieve_sound1 (S(exp 2 8))) as H
    [elim H.assumption
    |apply leb_true_to_le.reflexivity
    ]
  |intros.apply (sieve_sound2 ? ? H3 H2)
  |apply check_list2.
   reflexivity
  ]
qed.

lemma not_not_bertrand_to_bertrand1: \forall n.
\lnot (not_bertrand n) \to \forall x. n \le x \to x \le 2*n \to
(\forall p.x < p \to p \le 2*n \to \not (prime p))
\to \exists p.n < p \land p \le  x \land (prime p).
intros 4.elim H1
  [apply False_ind.apply H.assumption
  |apply (bool_elim ? (primeb (S n1)));intro
    [apply (ex_intro ? ? (S n1)).
     split
      [split
        [apply le_S_S.assumption
        |apply le_n
        ]
      |apply primeb_true_to_prime.assumption
      ]
    |elim H3
      [elim H7.clear H7.
       elim H8.clear H8.
       apply (ex_intro ? ? a). 
       split
        [split
          [assumption
          |apply le_S.assumption
          ]
        |assumption
        ]
      |apply lt_to_le.assumption
      |elim (le_to_or_lt_eq ? ? H7)
        [apply H5;assumption
        |rewrite < H9.
         apply primeb_false_to_not_prime.
         assumption
        ]
      ]
    ]
  ]
qed.
  
theorem not_not_bertrand_to_bertrand: \forall n.
\lnot (not_bertrand n) \to bertrand n.
unfold bertrand.intros.
apply (not_not_bertrand_to_bertrand1 ? ? (2*n))
  [assumption
  |apply le_times_n.apply le_n_Sn
  |apply le_n
  |intros.apply False_ind.
   apply (lt_to_not_le ? ? H1 H2)
  ]
qed.
  


definition k \def \lambda n,p. 
sigma_p (log p n) (λi:nat.true) (λi:nat.((n/(exp p (S i))\mod 2))).

theorem le_k: \forall n,p. k n p \le log p n.
intros.unfold k.elim (log p n)
  [apply le_n
  |rewrite > true_to_sigma_p_Sn 
    [rewrite > plus_n_SO.
     rewrite > sym_plus in ⊢ (? ? %).
     apply le_plus
      [apply le_S_S_to_le.
       apply lt_mod_m_m.
       apply lt_O_S
      |assumption
      ]
    |reflexivity
    ]
  ]
qed.

definition B1 \def
\lambda n. pi_p (S n) primeb (\lambda p.(exp p (k n p))).

theorem eq_B_B1: \forall n. B n = B1 n.
intros.unfold B.unfold B1.
apply eq_pi_p
  [intros.reflexivity
  |intros.unfold k.
   apply exp_sigma_p1
  ]
qed.

definition B_split1 \def \lambda n. 
pi_p (S n) primeb (\lambda p.(exp p (bool_to_nat (leb (k n p) 1)* (k n p)))).

definition B_split2 \def \lambda n. 
pi_p (S n) primeb (\lambda p.(exp p (bool_to_nat (leb 2 (k n p))* (k n p)))).

theorem eq_B1_times_B_split1_B_split2: \forall n. 
B1 n = B_split1 n * B_split2 n.
intro.unfold B1.unfold B_split1.unfold B_split2.
rewrite < times_pi_p.
apply eq_pi_p
  [intros.reflexivity
  |intros.apply (bool_elim ? (leb (k n x) 1));intro
    [rewrite > (lt_to_leb_false 2 (k n x))
      [simplify.rewrite < plus_n_O.
       rewrite < times_n_SO.reflexivity
      |apply le_S_S.apply leb_true_to_le.assumption
      ]
    |rewrite > (le_to_leb_true 2 (k n x))
      [simplify.rewrite < plus_n_O.
       rewrite < plus_n_O.reflexivity
      |apply not_le_to_lt.apply leb_false_to_not_le.assumption
      ]
    ]
  ]
qed.

lemma lt_div_to_times: \forall n,m,q. O < q \to n/q < m \to n < q*m.
intros.
cut (O < m) as H2
  [apply not_le_to_lt.
   intro.apply (lt_to_not_le ? ? H1).
   apply le_times_to_le_div;assumption
  |apply (ltn_to_ltO ? ? H1)
  ]
qed.

lemma lt_to_div_O:\forall n,m. n < m \to n / m = O.
intros.
apply (div_mod_spec_to_eq n m (n/m) (n \mod m) O n)
  [apply div_mod_spec_div_mod.
   apply (ltn_to_ltO ? ? H)
  |apply div_mod_spec_intro
    [assumption
    |reflexivity
    ]
  ]
qed.

(* the value of n could be smaller *) 
lemma k1: \forall n,p. 18 \le n \to p \le n \to 2*n/ 3 < p\to k (2*n) p = O.
intros.unfold k.
elim (log p (2*n))
  [reflexivity
  |rewrite > true_to_sigma_p_Sn
    [rewrite > H3.
     rewrite < plus_n_O.
     cases n1
      [rewrite < exp_n_SO.
       cut (2*n/p = 2) as H4
        [rewrite > H4.reflexivity
        |apply lt_to_le_times_to_lt_S_to_div
          [apply (ltn_to_ltO ? ? H2)
          |rewrite < sym_times.
           apply le_times_r.
           assumption
          |rewrite > sym_times in ⊢ (? ? %).
           apply lt_div_to_times
            [apply lt_O_S
            |assumption
            ]
          ]
        ]
      |cut (2*n/(p)\sup(S (S n2)) = O) as H4
        [rewrite > H4.reflexivity
        |apply lt_to_div_O.
         apply (le_to_lt_to_lt ? (exp ((2*n)/3) 2))
          [apply (le_times_to_le (exp 3 2))
            [apply leb_true_to_le.reflexivity
            |rewrite > sym_times in ⊢ (? ? %).
             rewrite > times_exp.
             apply (trans_le ? (exp n 2))
              [rewrite < assoc_times.
               rewrite > exp_SSO in ⊢ (? ? %).
               apply le_times_l.
               assumption
              |apply monotonic_exp1.
               apply (le_plus_to_le 3).
               change in ⊢ (? ? %) with ((S(2*n/3))*3).
               apply (trans_le ? (2*n))
                [simplify in ⊢ (? ? %).
                 rewrite < plus_n_O.
                 apply le_plus_l.
                 apply (trans_le ? 18 ? ? H).
                 apply leb_true_to_le.reflexivity
                |apply lt_to_le.
                 apply lt_div_S.
                 apply lt_O_S
                ]
              ]
            ]
          |apply (lt_to_le_to_lt ? (exp p 2))
            [apply lt_exp1
              [apply lt_O_S
              |assumption
              ]
            |apply le_exp
              [apply (ltn_to_ltO ? ? H2)
              |apply le_S_S.apply le_S_S.apply le_O_n
              ]
            ]
          ]
        ]
      ]
    |reflexivity
    ]
  ]
qed.
        
theorem le_B_split1_teta:\forall n.18 \le n \to not_bertrand n \to
B_split1 (2*n) \le teta (2 * n / 3).
intros. unfold B_split1.unfold teta.
apply (trans_le ? (pi_p (S (2*n)) primeb (λp:nat.(p)\sup(bool_to_nat (eqb (k (2*n) p) 1)))))
  [apply le_pi_p.intros.
   apply le_exp
    [apply prime_to_lt_O.apply primeb_true_to_prime.assumption
    |apply (bool_elim ? (leb (k (2*n) i) 1));intro
      [elim (le_to_or_lt_eq ? ? (leb_true_to_le ? ? H4))
        [lapply (le_S_S_to_le ? ? H5) as H6.
         apply (le_n_O_elim ? H6).
         rewrite < times_n_O.
         apply le_n
        |rewrite > (eq_to_eqb_true ? ? H5).
         rewrite > H5.apply le_n
        ]
      |apply le_O_n
      ]
    ]
  |apply (trans_le ? (pi_p (S (2*n/3)) primeb (λp:nat.(p)\sup(bool_to_nat (eqb (k (2*n) p) 1)))))
    [apply (eq_ind ? ? ? (le_n ?)).
     apply or_false_eq_SO_to_eq_pi_p
      [apply le_S_S.
       apply le_times_to_le_div2
        [apply lt_O_S
        |rewrite > sym_times in ⊢ (? ? %).
         apply le_times_n.
         apply leb_true_to_le.reflexivity
        ]
      |intros.
       unfold not_bertrand in H1.
       elim (decidable_le (S n) i)
        [left.
         apply not_prime_to_primeb_false.
         apply H1
          [assumption
          |apply le_S_S_to_le.assumption
          ]
        |right.
         rewrite > k1
          [reflexivity
          |assumption
          |apply le_S_S_to_le.
           apply not_le_to_lt.assumption
          |assumption
          ]
        ]
      ]
    |apply le_pi_p.intros.
     elim (eqb (k (2*n) i) 1)
      [rewrite < exp_n_SO.apply le_n
      |simplify.apply prime_to_lt_O.
       apply primeb_true_to_prime.
       assumption
      ]
    ]
  ]
qed.

theorem le_B_split2_exp: \forall n. exp 2 7 \le n \to
B_split2 (2*n) \le exp (2*n) (pred(sqrt(2*n)/2)).
intros.unfold B_split2.
cut (O < n)
  [apply (trans_le ? (pi_p (S (sqrt (2*n))) primeb
        (λp:nat.(p)\sup(bool_to_nat (leb 2 (k (2*n) p))*k (2*n) p))))
    [apply (eq_ind ? ? ? (le_n ?)).
     apply or_false_eq_SO_to_eq_pi_p
      [apply le_S_S.
       apply le_sqrt_n_n
      |intros.
       apply (bool_elim ? (leb 2 (k (2*n) i)));intro
        [apply False_ind.
         apply (lt_to_not_le ? ? H1).unfold sqrt.
         apply f_m_to_le_max
          [apply le_S_S_to_le.assumption
          |apply le_to_leb_true.
           rewrite < exp_SSO.
           apply not_lt_to_le.intro.
           apply (le_to_not_lt 2 (log i (2*n)))
            [apply (trans_le ? (k (2*n) i))
              [apply leb_true_to_le.assumption
              |apply le_k
              ]
            |apply le_S_S.unfold log.apply f_false_to_le_max
              [apply (ex_intro ? ? O).split
                [apply le_O_n
                |apply le_to_leb_true.simplify.
                 apply (trans_le ? n)
                  [assumption.
                  |apply le_plus_n_r
                  ]
                ]
              |intros.apply lt_to_leb_false.
               apply (lt_to_le_to_lt ? (exp i 2))
                [assumption
                |apply le_exp
                  [apply (ltn_to_ltO ? ? H1)
                  |assumption
                  ]
                ]
              ]
            ]
          ]
        |right.reflexivity
        ]
      ]
    |apply (trans_le ? (pi_p (S (sqrt (2*n))) primeb (λp:nat.2*n)))
      [apply le_pi_p.intros.
       apply (trans_le ? (exp i (log i (2*n))))
        [apply le_exp
          [apply prime_to_lt_O.
           apply primeb_true_to_prime.
           assumption
          |apply (bool_elim ? (leb 2 (k (2*n) i)));intro
            [simplify in ⊢ (? (? % ?) ?).
             rewrite > sym_times.
             rewrite < times_n_SO.
             apply le_k
            |apply le_O_n
            ]
          ]
        |apply le_exp_log.    
         rewrite > (times_n_O O) in ⊢ (? % ?).
         apply lt_times
          [apply lt_O_S
          |assumption
          ]
        ]
      |apply (trans_le ? (exp (2*n) (prim(sqrt (2*n)))))
        [unfold prim.
         apply (eq_ind ? ? ? (le_n ?)).
         apply exp_sigma_p
        |apply le_exp
          [rewrite > (times_n_O O) in ⊢ (? % ?).
           apply lt_times
            [apply lt_O_S
            |assumption
            ]
          |apply le_prim_n3.
           unfold sqrt.
           apply f_m_to_le_max
            [apply (trans_le ? (2*(exp 2 7)))
              [apply leb_true_to_le.reflexivity
              |apply le_times_r.assumption
              ]
            |apply le_to_leb_true.
             apply (trans_le ? (2*(exp 2 7)))
              [apply leb_true_to_le.reflexivity
              |apply le_times_r.assumption
              ]
            ]
          ]
        ]
      ]
    ]
  |apply (lt_to_le_to_lt ? ? ? ? H).
   apply leb_true_to_le.reflexivity
  ]
qed.
   
theorem not_bertrand_to_le_B: 
\forall n.exp 2 7 \le n \to not_bertrand n \to
B (2*n) \le (exp 2 (2*(2 * n / 3)))*(exp (2*n) (pred(sqrt(2*n)/2))).
intros.
rewrite > eq_B_B1.
rewrite > eq_B1_times_B_split1_B_split2.
apply le_times
  [apply (trans_le ? (teta ((2*n)/3)))
    [apply le_B_split1_teta
      [apply (trans_le ? ? ? ? H).
       apply leb_true_to_le.reflexivity
      |assumption
      ]
    |apply le_teta
    ]
  |apply le_B_split2_exp.
   assumption
  ]
qed.

(* 
theorem not_bertrand_to_le1: 
\forall n.18 \le n \to not_bertrand n \to
exp 2 (2*n) \le (exp 2 (2*(2 * n / 3)))*(exp (2*n) (S(sqrt(2*n)))).
*)

theorem le_times_div_m_m: \forall n,m. O < m \to n/m*m \le n.
intros.
rewrite > (div_mod n m) in ⊢ (? ? %)
  [apply le_plus_n_r
  |assumption
  ]
qed.

theorem not_bertrand_to_le1: 
\forall n.exp 2 7 \le n \to not_bertrand n \to
(exp 2 (2*n / 3)) \le (exp (2*n) (sqrt(2*n)/2)).
intros.
apply (le_times_to_le (exp 2 (2*(2 * n / 3))))
  [apply lt_O_exp.apply lt_O_S
  |rewrite < exp_plus_times.
   apply (trans_le ? (exp 2 (2*n)))
    [apply le_exp
      [apply lt_O_S
      |rewrite < sym_plus.
       change in ⊢ (? % ?) with (3*(2*n/3)).
       rewrite > sym_times.
       apply le_times_div_m_m.
       apply lt_O_S
      ]
    |apply (trans_le ? (2*n*B(2*n)))
      [apply le_exp_B.
       apply (trans_le ? ? ? ? H).
       apply leb_true_to_le.reflexivity
      |rewrite > S_pred in ⊢ (? ? (? ? (? ? %)))
        [rewrite > exp_S.
         rewrite < assoc_times.
         rewrite < sym_times in ⊢ (? ? (? % ?)).
         rewrite > assoc_times in ⊢ (? ? %).
         apply le_times_r.
         apply not_bertrand_to_le_B;assumption
        |apply le_times_to_le_div
          [apply lt_O_S
          |apply (trans_le ? (sqrt (exp 2 8)))
            [apply leb_true_to_le.reflexivity
            |apply monotonic_sqrt.
             change in ⊢ (? % ?) with (2*(exp 2 7)).
             apply le_times_r.
             assumption
            ]
          ]
        ]
      ]
    ]
  ]
qed.
       
theorem not_bertrand_to_le2: 
\forall n.exp 2 7 \le n \to not_bertrand n \to
2*n / 3 \le (sqrt(2*n)/2)*S(log 2 (2*n)).
intros.
rewrite < (eq_log_exp 2)
  [apply (trans_le ? (log 2 ((exp (2*n) (sqrt(2*n)/2)))))
    [apply le_log
      [apply le_n
      |apply not_bertrand_to_le1;assumption
      ]
    |apply log_exp1.
     apply le_n
    ]
  |apply le_n
  ]
qed.

theorem tech1: \forall a,b,c,d.O < b \to O < d \to
(a/b)*(c/d) \le (a*c)/(b*d).
intros.
apply le_times_to_le_div
  [rewrite > (times_n_O O).
   apply lt_times;assumption
  |rewrite > assoc_times.
   rewrite < assoc_times in ⊢ (? (? ? %) ?).
   rewrite < sym_times in ⊢ (? (? ? (? % ?)) ?).
   rewrite > assoc_times.
   rewrite < assoc_times.
   apply le_times;
   rewrite > sym_times;apply le_times_div_m_m;assumption
  ]
qed.

theorem tech: \forall n. 2*(S(log 2 (2*n))) \le sqrt (2*n) \to
(sqrt(2*n)/2)*S(log 2 (2*n)) \le 2*n / 4.
intros.
cut (4*(S(log 2 (2*n))) \le 2* sqrt(2*n))
  [rewrite > sym_times.
   apply le_times_to_le_div
    [apply lt_O_S
    |rewrite < assoc_times.
     apply (trans_le ? (2*sqrt(2*n)*(sqrt (2*n)/2)))
      [apply le_times_l.assumption
      |apply (trans_le ? ((2*sqrt(2*n)*(sqrt(2*n))/2)))
        [apply le_times_div_div_times.
         apply lt_O_S
        |rewrite > assoc_times.
         rewrite > sym_times.
         rewrite > lt_O_to_div_times.
         apply leq_sqrt_n.
         apply lt_O_S
        ]
      ]
    ]
  |change in ⊢ (? (? % ?) ?) with (2*2).
   rewrite > assoc_times.
   apply le_times_r.
   assumption
  ]
qed.

theorem lt_div_S_div: \forall n,m. O < m \to exp m 2 \le n \to 
n/(S m) < n/m.
intros.
apply lt_times_to_lt_div.
apply (lt_to_le_to_lt ? (S(n/m)*m))
  [apply lt_div_S.assumption
  |rewrite > sym_times in ⊢ (? ? %). simplify.
   rewrite > sym_times in ⊢ (? ? (? ? %)).
   apply le_plus_l.
   apply le_times_to_le_div
    [assumption
    |rewrite < exp_SSO.
     assumption
    ]
  ]
qed.

theorem exp_plus_SSO: \forall a,b. exp (a+b) 2 = (exp a 2) + 2*a*b + (exp b 2).
intros.
rewrite > exp_SSO.
rewrite > distr_times_plus.
rewrite > times_plus_l.
rewrite < exp_SSO.
rewrite > assoc_plus.
rewrite > assoc_plus.
apply eq_f.
rewrite > times_plus_l.
rewrite < exp_SSO.
rewrite < assoc_plus.
rewrite < sym_times.
rewrite > plus_n_O in ⊢ (? ? (? (? ? %) ?) ?).
rewrite > assoc_times.
apply eq_f2;reflexivity.
qed.

theorem tech3: \forall n. (exp 2 8) \le n \to 2*(S(log 2 (2*n))) \le sqrt (2*n).
intros.
lapply (le_log 2 ? ? (le_n ?) H) as H1.
rewrite > exp_n_SO in ⊢ (? (? ? (? (? ? (? % ?)))) ?).
rewrite > log_exp
  [rewrite > sym_plus.
   rewrite > plus_n_Sm.
   unfold sqrt.
   apply f_m_to_le_max
    [apply le_times_r.
     apply (trans_le ? (2*log 2 n))
      [rewrite < times_SSO_n.
       apply le_plus_r.
       apply (trans_le ? 8)
        [apply leb_true_to_le.reflexivity
        |rewrite < (eq_log_exp 2)
          [assumption
          |apply le_n
          ]
        ]
      |apply (trans_le ? ? ? ? (le_exp_log 2 ? ? )).
       apply le_times_SSO_n_exp_SSO_n.
       apply (lt_to_le_to_lt ? ? ? ? H).
       apply leb_true_to_le.reflexivity
      ]
    |apply le_to_leb_true.
     rewrite > assoc_times.
     apply le_times_r.
     rewrite > sym_times.
     rewrite > assoc_times.
     rewrite < exp_SSO.
     rewrite > exp_plus_SSO.
     rewrite > distr_times_plus.
     rewrite > distr_times_plus.
     rewrite > assoc_plus.
     apply (trans_le ? (4*exp (log 2 n) 2))
      [change in ⊢ (? ? (? % ?)) with (2*2).
       rewrite > assoc_times in ⊢ (? ? %).
       rewrite < times_SSO_n in ⊢ (? ? %).
       apply le_plus_r.
       rewrite < times_SSO_n in ⊢ (? ? %).
       apply le_plus
        [rewrite > sym_times in ⊢ (? (? ? %) ?).
         rewrite < assoc_times.
         rewrite < assoc_times.
         change in ⊢ (? (? % ?) ?) with 8.
         rewrite > exp_SSO.
         apply le_times_l.
         (* strange things here *)
         rewrite < (eq_log_exp 2)
          [assumption
          |apply le_n
          ]
        |apply (trans_le ? (log 2 n))
          [change in ⊢ (? % ?) with 8.
           rewrite < (eq_log_exp 2)
            [assumption
            |apply le_n
            ]
          |rewrite > exp_n_SO in ⊢ (? % ?).
           apply le_exp
            [apply lt_O_log
              [apply (lt_to_le_to_lt ? ? ? ? H).
               apply leb_true_to_le.reflexivity
              |apply (lt_to_le_to_lt ? ? ? ? H).
               apply leb_true_to_le.reflexivity
              ]
            |apply le_n_Sn
            ]
          ]
        ]
      |change in ⊢ (? (? % ?) ?) with (exp 2 2).
       apply (trans_le ? ? ? ? (le_exp_log 2 ? ?))
        [apply le_times_exp_n_SSO_exp_SSO_n
          [apply le_n
          |change in ⊢ (? % ?) with 8.
           rewrite < (eq_log_exp 2)
            [assumption
            |apply le_n
            ]
          ]
        |apply (lt_to_le_to_lt ? ? ? ? H).
         apply leb_true_to_le.reflexivity
        ]
      ]
    ]
  |apply le_n
  |apply (lt_to_le_to_lt ? ? ? ? H).
   apply leb_true_to_le.reflexivity
  ]
qed.
      
theorem le_to_bertrand2:
\forall n. (exp 2 8) \le n \to bertrand n.
intros.
apply not_not_bertrand_to_bertrand.unfold.intro.
absurd (2*n / 3 \le (sqrt(2*n)/2)*S(log 2 (2*n)))
  [apply not_bertrand_to_le2
    [apply (trans_le ? ? ? ? H). 
     apply le_exp
      [apply lt_O_S
      |apply le_n_Sn
      ]
    |assumption
    ]
  |apply lt_to_not_le.
   apply (le_to_lt_to_lt ? ? ? ? (lt_div_S_div ? ? ? ?))
    [apply tech.apply tech3.assumption
    |apply lt_O_S
    |apply (trans_le ? (2*exp 2 8))
      [apply leb_true_to_le.reflexivity
      |apply le_times_r.assumption
      ]
    ]
  ]
qed.

theorem bertrand_n :
\forall n. O < n \to bertrand n.
intros;elim (decidable_le n 256)
  [apply le_to_bertrand;assumption
  |apply le_to_bertrand2;apply lt_to_le;apply not_le_to_lt;apply H1]
qed.

(* test 
theorem mod_exp: eqb (mod (exp 2 8) 13) O = false.
reflexivity.
*)
