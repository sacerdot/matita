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

include "nat/sqrt.ma".
include "nat/chebyshev_teta.ma".
include "nat/chebyshev.ma".
include "list/in.ma".
include "list/sort.ma".
include "nat/o.ma".

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
  
let rec list_n_aux n k \def
    match n with
    [ O => nil nat
    | S n1 => k::list_n_aux n1 (S k) ].

definition list_n : nat \to list nat \def
  \lambda n.list_n_aux (pred n) 2.

let rec sieve_aux l1 l2 t on t \def
  match t with
  [ O => l1
  | S t1 => match l2 with
    [ nil => l1
    | cons n tl => sieve_aux (n::l1) (filter nat tl (\lambda x.notb (divides_b n x))) t1]].

definition sieve : nat \to list nat \def
  \lambda m.sieve_aux [] (list_n m) m.

lemma divides_to_prime_divides : \forall n,m.1 < m \to m < n \to m \divides n \to
 \exists p.p \leq m \land prime p \land p \divides n.
intros;apply (ex_intro ? ? (nth_prime (max_prime_factor m)));split
  [split
     [apply divides_to_le
        [apply lt_to_le;assumption
        |apply divides_max_prime_factor_n;assumption]
     |apply prime_nth_prime;]
  |apply (transitive_divides ? ? ? ? H2);apply divides_max_prime_factor_n;
   assumption]
qed.

definition sorted_lt \def sorted ? lt.
definition sorted_gt \def sorted ? gt.

lemma sieve_prime : \forall t,k,l2,l1.
  (\forall p.(in_list ? p l1 \to prime p \land p \leq k \land \forall x.in_list ? x l2 \to p < x) \land
             (prime p \to p \leq k \to (\forall x.in_list ? x l2 \to p < x) \to in_list ? p l1)) \to
  (\forall x.(in_list ? x l2 \to 2 \leq x \land x \leq k \land \forall p.in_list ? p l1 \to \lnot p \divides x) \land
             (2 \leq x \to x \leq k \to (\forall p.in_list ? p l1 \to \lnot p \divides x) \to
              in_list ? x l2)) \to
  length ? l2 \leq t \to
  sorted_gt l1 \to
  sorted_lt l2 \to
  sorted_gt (sieve_aux l1 l2 t) \land
  \forall p.(in_list ? p (sieve_aux l1 l2 t) \to prime p \land p \leq k) \land
            (prime p \to p \leq k \to in_list ? p (sieve_aux l1 l2 t)).
intro.elim t 0
  [intros;cut (l2 = [])
     [|generalize in match H2;elim l2
        [reflexivity
        |simplify in H6;elim (not_le_Sn_O ? H6)]]
   simplify;split
     [assumption
     |intro;elim (H p);split;intros
        [elim (H5 H7);assumption
        |apply (H6 H7 H8);rewrite > Hcut;intros;elim (not_in_list_nil ? ? H9)]]
  |intros 4;elim l2
     [simplify;split;
        [assumption
        |intro;elim (H1 p);split;intros
           [elim (H6 H8);assumption
           |apply (H7 H8 H9);intros;elim (not_in_list_nil ? ? H10)]]
     |simplify;elim (H k (filter ? l (\lambda x.notb (divides_b t1 x))) (t1::l1))
        [split;
           [assumption
           |intro;apply H8;]
        |split;intros
           [elim (in_list_cons_case ? ? ? ? H7);
              [rewrite > H8;split
                 [split
                    [unfold;intros;split
                       [elim (H3 t1);elim H9
                          [elim H11;assumption
                          |apply in_list_head]
                       |intros;elim (le_to_or_lt_eq ? ? (divides_to_le ? ? ? H9))
                          [elim (divides_to_prime_divides ? ? H10 H11 H9);elim H12;
                           elim H13;clear H13 H12;elim (H3 t1);elim H12
                             [clear H13 H12;elim (H18 ? ? H14);elim (H2 a);
                              apply H13
                                [assumption
                                |elim H17;apply (trans_le ? ? ? ? H20);
                                 apply (trans_le ? ? ? H15);
                                 apply lt_to_le;assumption
                                |intros;apply (trans_le ? (S m))
                                   [apply le_S_S;assumption
                                   |apply (trans_le ? ? ? H11);
                                    elim (in_list_cons_case ? ? ? ? H19)
                                      [rewrite > H20;apply le_n
                                      |apply lt_to_le;apply (sorted_to_minimum ? ? ? ? H6);assumption]]]
                             |apply in_list_head]
                          |elim (H3 t1);elim H11
                             [elim H13;apply lt_to_le;assumption
                             |apply in_list_head]
                          |assumption]]
                    |elim (H3 t1);elim H9
                       [elim H11;assumption
                       |apply in_list_head]]
                 |intros;elim (le_to_or_lt_eq t1 x)
                    [assumption
                    |rewrite > H10 in H9;lapply (in_list_filter_to_p_true ? ? ? H9);
                     lapply (divides_n_n x);
                     rewrite > (divides_to_divides_b_true ? ? ? Hletin1) in Hletin
                       [simplify in Hletin;destruct Hletin
                       |rewrite < H10;elim (H3 t1);elim H11
                          [elim H13;apply lt_to_le;assumption
                          |apply in_list_head]]
                    |apply lt_to_le;apply (sorted_to_minimum ? ? ? ? H6);apply (in_list_filter ? ? ? H9)]]
                 |elim (H2 p);elim (H9 H8);split
                    [assumption
                    |intros;apply H12;apply in_list_cons;apply (in_list_filter ? ? ? H13)]]
           |elim (decidable_eq_nat p t1)
              [rewrite > H10;apply in_list_head
              |apply in_list_cons;elim (H2 p);apply (H12 H7 H8);intros;
               apply (trans_le ? t1)
                 [elim (decidable_lt p t1)
                    [assumption
                    |lapply (not_lt_to_le ? ? H14);
                     lapply (decidable_divides t1 p)
                       [elim Hletin1
                          [elim H7;lapply (H17 ? H15)
                             [elim H10;symmetry;assumption
                             |elim (H3 t1);elim H18
                                [elim H20;assumption
                                |apply in_list_head]]
                          |elim (Not_lt_n_n p);apply H9;apply in_list_filter_r
                             [elim (H3 p);apply (in_list_tail ? ? t1)
                                [apply H17
                                   [apply prime_to_lt_SO;assumption
                                   |assumption
                                   |intros;elim H7;intro;lapply (H20 ? H21)
                                      [rewrite > Hletin2 in H18;elim (H11 H18);
                                       lapply (H23 t1)
                                         [elim (lt_to_not_le ? ? Hletin3 Hletin)
                                         |apply in_list_head]
                                      |apply prime_to_lt_SO;elim (H2 p1);elim (H22 H18);
                                       elim H24;assumption]]
                                |unfold;intro;apply H15;rewrite > H18;apply divides_n_n]
                             |rewrite > (not_divides_to_divides_b_false ? ? ? H15);
                                [reflexivity
                                |elim (H3 t1);elim H16
                                   [elim H18;apply lt_to_le;assumption
                                   |apply in_list_head]]]]
                       |elim (H3 t1);elim H15
                          [elim H17;apply lt_to_le;assumption
                          |apply in_list_head]]]
                 |elim (in_list_cons_case ? ? ? ? H13)
                    [rewrite > H14;apply le_n
                    |apply lt_to_le;apply (sorted_to_minimum ? ? ? ? H6);assumption]]]]
         |elim (H3 x);split;intros;
            [split 
               [elim H7
                  [assumption
                  |apply in_list_cons;apply (in_list_filter ? ? ? H9)]
               |intros;elim (in_list_cons_case ? ? ? ? H10)
                  [rewrite > H11;intro;lapply (in_list_filter_to_p_true ? ? ? H9);
                   rewrite > (divides_to_divides_b_true ? ? ? H12) in Hletin
                     [simplify in Hletin;destruct Hletin
                     |elim (H3 t1);elim H13
                        [elim H15;apply lt_to_le;assumption
                        |apply in_list_head]]
                  |elim H7
                     [apply H13;assumption
                     |apply in_list_cons;apply (in_list_filter ? ? ? H9)]]]
            |elim (in_list_cons_case ? ? ? ? (H8 ? ? ?))
               [elim (H11 x)
                  [rewrite > H12;apply in_list_head
                  |apply divides_n_n]
               |assumption
               |assumption
               |intros;apply H11;apply in_list_cons;assumption
               |apply in_list_filter_r;
                  [assumption
                  |lapply (H11 t1)
                     [rewrite > (not_divides_to_divides_b_false ? ? ? Hletin);
                        [reflexivity
                        |elim (H3 t1);elim H13
                           [elim H15;apply lt_to_le;assumption
                           |apply in_list_head]]
                     |apply in_list_head]]]]
         |apply (trans_le ? ? ? (le_length_filter ? ? ?));apply le_S_S_to_le;
          apply H4
         |apply sort_cons
            [assumption
            |intros;unfold;elim (H2 y);elim (H8 H7);
             apply H11;apply in_list_head]
         |generalize in match (sorted_cons_to_sorted ? ? ? ? H6);elim l
            [simplify;assumption
            |simplify;elim (notb (divides_b t1 t2));simplify
               [lapply (sorted_cons_to_sorted ? ? ? ? H8);lapply (H7 Hletin);
                apply (sort_cons ? ? ? ? Hletin1);intros;
                apply (sorted_to_minimum ? ? ? ? H8);apply (in_list_filter ? ? ? H9);
               |apply H7;apply (sorted_cons_to_sorted ? ? ? ? H8)]]]]]
qed.

lemma le_list_n_aux_k_k : \forall n,m,k.in_list ? n (list_n_aux m k) \to
                          k \leq n.
intros 2;elim m
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;elim (in_list_cons_case ? ? ? ? H1)
     [rewrite > H2;apply le_n
     |apply lt_to_le;apply H;assumption]]
qed.

lemma in_list_SSO_list_n : \forall n.2 \leq n \to in_list ? 2 (list_n n).
intros;elim H;simplify
  [apply in_list_head
  |generalize in match H2;elim H1;simplify;apply in_list_head]
qed.

lemma le_SSO_list_n : \forall m,n.in_list nat n (list_n m) \to 2 \leq n.
intros;unfold list_n in H;apply (le_list_n_aux_k_k ? ? ? H);
qed.

lemma le_list_n_aux : \forall n,m,k.in_list ? n (list_n_aux m k) \to n \leq k+m-1.
intros 2;elim m
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;elim (in_list_cons_case ? ? ? ? H1)
     [rewrite > H2;rewrite < plus_n_Sm;simplify;rewrite < minus_n_O;
      rewrite > plus_n_O in \vdash (? % ?);apply le_plus_r;apply le_O_n
     |rewrite < plus_n_Sm;apply (H (S k));assumption]]
qed.

lemma le_list_n : \forall n,m.in_list ? n (list_n m) \to n \leq m.
intros;unfold list_n in H;lapply (le_list_n_aux ? ? ? H);
simplify in Hletin;generalize in match H;generalize in match Hletin;elim m
   [simplify in H2;elim (not_in_list_nil ? ? H2)
   |simplify in H2;assumption]
qed.


lemma le_list_n_aux_r : \forall n,m.O < m \to \forall k.k \leq n \to n \leq k+m-1 \to in_list ? n (list_n_aux m k).
intros 3;elim H 0
  [intros;simplify;rewrite < plus_n_Sm in H2;simplify in H2;
   rewrite < plus_n_O in H2;rewrite < minus_n_O in H2;
   rewrite > (antisymmetric_le k n H1 H2);apply in_list_head
  |intros 5;simplify;generalize in match H2;elim H3
     [apply in_list_head
     |apply in_list_cons;apply H6
        [apply le_S_S;assumption
        |rewrite < plus_n_Sm in H7;apply H7]]]
qed.

lemma le_list_n_r : \forall n,m.S O < m \to 2 \leq n \to n \leq m \to in_list ? n (list_n m).
intros;unfold list_n;apply le_list_n_aux_r
  [elim H;simplify
     [apply lt_O_S
     |generalize in match H4;elim H3;
        [apply lt_O_S
        |simplify in H7;apply le_S;assumption]]
  |assumption
  |simplify;generalize in match H2;elim H;simplify;assumption]
qed.  

lemma le_length_list_n : \forall n. length ? (list_n n) \leq n.
intro;cut (\forall n,k.length ? (list_n_aux n k) \leq (S n))
  [elim n;simplify
     [apply le_n
     |apply Hcut]
  |intro;elim n1;simplify
     [apply le_O_n
     |apply le_S_S;apply H]]
qed.

lemma sorted_list_n_aux : \forall n,k.sorted_lt (list_n_aux n k).
intro.elim n 0
  [simplify;intro;apply sort_nil
  |intro;simplify;intros 2;apply sort_cons
     [apply H
     |intros;lapply (le_list_n_aux_k_k ? ? ? H1);assumption]]
qed.

definition list_of_primes \def \lambda n.\lambda l.
\forall p.in_list nat p l  \to prime p \land p \leq n.

lemma sieve_sound1 : \forall n.2 \leq n \to
sorted_gt (sieve n) \land list_of_primes n (sieve n).
intros;elim (sieve_prime n n (list_n n) [])
  [split
     [assumption
     |intro;unfold sieve in H3;elim (H2 p);elim (H3 H5);split;assumption]
  |split;intros
     [elim (not_in_list_nil ? ? H1)
     |lapply (lt_to_not_le ? ? (H3 2 ?))
        [apply in_list_SSO_list_n;assumption
        |elim Hletin;apply prime_to_lt_SO;assumption]]
  |split;intros
     [split
        [split
           [apply (le_SSO_list_n ? ? H1)
           |apply (le_list_n ? ? H1)]
        |intros;elim (not_in_list_nil ? ? H2)]
     |apply le_list_n_r;assumption]
  |apply le_length_list_n
  |apply sort_nil
  |elim n;simplify
     [apply sort_nil
     |elim n1;simplify
        [apply sort_nil
        |simplify;apply sort_cons
           [apply sorted_list_n_aux
           |intros;lapply (le_list_n_aux_k_k ? ? ? H3);
            assumption]]]]
qed.

lemma sieve_sorted : \forall n.sorted_gt (sieve n).
intros;elim (decidable_le 2 n)
  [elim (sieve_sound1 ? H);assumption
  |generalize in match (le_S_S_to_le ? ? (not_le_to_lt ? ? H));cases n
     [intro;simplify;apply sort_nil
     |intros;lapply (le_S_S_to_le ? ? H1);rewrite < (le_n_O_to_eq ? Hletin);
      simplify;apply sort_nil]]
qed.

lemma in_list_sieve_to_prime : \forall n,p.2 \leq n \to in_list ? p (sieve n) \to
                               prime p.
intros;elim (sieve_sound1 ? H);elim (H3 ? H1);assumption;
qed.

lemma in_list_sieve_to_leq : \forall n,p.2 \leq n \to in_list ? p (sieve n) \to
                             p \leq n.
intros;elim (sieve_sound1 ? H);elim (H3 ? H1);assumption;
qed.

lemma sieve_sound2 : \forall n,p.p \leq n \to prime p \to in_list ? p (sieve n).
intros;elim (sieve_prime n n (list_n n) [])
  [elim (H3 p);apply H5;assumption
  |split
     [intro;elim (not_in_list_nil ? ? H2)
     |intros;lapply (lt_to_not_le ? ? (H4 2 ?))
        [apply in_list_SSO_list_n;apply (trans_le ? ? ? ? H);
         apply prime_to_lt_SO;assumption
        |elim Hletin;apply prime_to_lt_SO;assumption]]
  |split;intros
     [split;intros
        [split
           [apply (le_SSO_list_n ? ? H2)
           |apply (le_list_n ? ? H2)]
        |elim (not_in_list_nil ? ? H3)]
     |apply le_list_n_r
        [apply (trans_le ? ? ? H2 H3)
        |assumption
        |assumption]]
  |apply le_length_list_n
  |apply sort_nil
  |elim n;simplify
     [apply sort_nil
     |elim n1;simplify
        [apply sort_nil
        |simplify;apply sort_cons
           [apply sorted_list_n_aux
           |intros;lapply (le_list_n_aux_k_k ? ? ? H4);
            assumption]]]]
qed.

let rec checker l \def
    match l with
      [ nil => true
      | cons h1 t1 => match t1 with
         [ nil => true
         | cons h2 t2 => (andb (checker t1) (leb h1 (2*h2))) ]].

lemma checker_cons : \forall t,l.checker (t::l) = true \to checker l = true.
intros 2;simplify;intro;generalize in match H;elim l
  [reflexivity
  |change in H2 with (andb (checker (t1::l1)) (leb t (t1+(t1+O))) = true);
   apply (andb_true_true ? ? H2)]
qed.

theorem checker_sound : \forall l1,l2,l,x,y.l = l1@(x::y::l2) \to 
                        checker l = true \to x \leq 2*y.
intro;elim l1 0
  [simplify;intros 5;rewrite > H;simplify;intro;
   apply leb_true_to_le;apply (andb_true_true_r ? ? H1);
  |simplify;intros;rewrite > H1 in H2;lapply (checker_cons ? ? H2);
   apply (H l2 ? ? ? ? Hletin);reflexivity]
qed.

definition bertrand \def \lambda n.
\exists p.n < p \land p \le 2*n \land (prime p).

definition not_bertrand \def \lambda n.
\forall p.n < p \to p \le 2*n \to \not (prime p).

(*
lemma list_of_primes_SO: \forall l.list_of_primes 1 l \to
l = [].
intro.cases l;intros
  [reflexivity
  |apply False_ind.unfold in H.
   absurd ((prime n) \land n \le 1)
    [apply H.
     apply in_list_head
    |intro.elim H1.
     elim H2.
     apply (lt_to_not_le ? ? H4 H3)
    ]
  ]
qed.
*)

lemma min_prim : \forall n.\exists p. n < p \land prime p \land
                 \forall q.prime q \to q < p \to q \leq n.
intro;elim (le_to_or_lt_eq ? ? (le_O_n n))
   [apply (ex_intro ? ? (min_aux (S (n!)) (S n) primeb));
    split
      [split
         [apply le_min_aux;
         |apply primeb_true_to_prime;apply f_min_aux_true;elim (ex_prime n);
            [apply (ex_intro ? ? a);elim H1;elim H2;split
               [split
                  [assumption
                  |rewrite > plus_n_O;apply le_plus
                     [assumption
                     |apply le_O_n]]
               |apply prime_to_primeb_true;assumption]
            |assumption]]
      |intros;apply not_lt_to_le;intro;lapply (lt_min_aux_to_false ? ? ? ? H3 H2);
       rewrite > (prime_to_primeb_true ? H1) in Hletin;destruct Hletin]
   |apply (ex_intro ? ? 2);split
      [split
         [rewrite < H;apply lt_O_S
         |apply primeb_true_to_prime;reflexivity]
      |intros;elim (lt_to_not_le ? ? H2);apply prime_to_lt_SO;assumption]]
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
       apply (ex_intro ? ? a). 
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

(*lemma pippo : \forall k,n.in_list ? (nth_prime (S k)) (sieve n) \to
              \exists l.sieve n = l@((nth_prime (S k))::(sieve (nth_prime k))).
intros;elim H;elim H1;clear H H1;apply (ex_intro ? ? a);
cut (a1 = sieve (nth_prime k))
  [rewrite < Hcut;assumption
  |lapply (sieve_sorted n);generalize in match H2*) 

(* old proof by Wilmer 
lemma le_to_bertrand : \forall n.O < n \to n \leq exp 2 8 \to bertrand n.
intros;
elim (min_prim n);apply (ex_intro ? ? a);elim H2;elim H3;clear H2 H3;
cut (a \leq 257)
  [|apply not_lt_to_le;intro;apply (le_to_not_lt ? ? H1);apply (H4 ? ? H2);
    apply primeb_true_to_prime;reflexivity]
split
   [split
      [assumption
      |elim (prime_to_nth_prime a H6);generalize in match H2;cases a1
         [simplify;intro;rewrite < H3;rewrite < plus_n_O;
          change in \vdash (? % ?) with (1+1);apply le_plus;assumption
         |intro;lapply (H4 (nth_prime n1))
            [apply (trans_le ? (2*(nth_prime n1)))
               [rewrite < H3;
                cut (\exists l1,l2.sieve 257 = l1@((nth_prime (S n1))::((nth_prime n1)::l2)))
                  [elim Hcut1;elim H7;clear Hcut1 H7;
                   apply (checker_sound a2 a3 (sieve 257))
                     [apply H8
                     |reflexivity]
                  |elim (sieve_sound2 257 (nth_prime (S n1)) ? ?)
                     [elim (sieve_sound2 257 (nth_prime n1) ? ?)
                        [elim H8;
                         cut (\forall p.in_list ? p (a3@(nth_prime n1::a4)) \to prime p)
                           [|rewrite < H9;intros;apply (in_list_sieve_to_prime 257 p ? H10);
                            apply leb_true_to_le;reflexivity]
                         apply (ex_intro ? ? a2);apply (ex_intro ? ? a4);
                         elim H7;clear H7 H8;
                         cut ((nth_prime n1)::a4 = a5)
                           [|generalize in match H10;
                             lapply (sieve_sorted 257);
                             generalize in match Hletin1;
                             rewrite > H9 in ⊢ (? %→? ? % ?→?);
                             generalize in match Hcut1;
                             generalize in match a2;
                             elim a3 0
                               [intro;elim l
                                  [change in H11 with (nth_prime n1::a4 = nth_prime (S n1)::a5);
                                   destruct H11;elim (eq_to_not_lt ? ? Hcut2);
                                   apply increasing_nth_prime
                                  |change in H12 with (nth_prime n1::a4 = t::(l1@(nth_prime (S n1)::a5)));
                                   destruct H12;
                                   change in H11 with (sorted_gt (nth_prime n1::l1@(nth_prime (S n1)::a5)));
                                   lapply (sorted_to_minimum ? ? ? H11 (nth_prime (S n1)))
                                     [unfold in Hletin2;elim (le_to_not_lt ? ? (lt_to_le ? ? Hletin2));
                                      apply increasing_nth_prime
                                     |apply (ex_intro ? ? l1);apply (ex_intro ? ? a5);reflexivity]]
                               |intros 5;elim l1
                                  [change in H12 with (t::(l@(nth_prime n1::a4)) = nth_prime (S n1)::a5);
                                   destruct H12;cut (l = [])
                                     [rewrite > Hcut2;reflexivity
                                     |change in H11 with (sorted_gt (nth_prime (S n1)::(l@(nth_prime n1::a4))));
                                      generalize in match H11;generalize in match H8;cases l;intros
                                        [reflexivity
                                        |lapply (sorted_cons_to_sorted ? ? ? H13);
                                         lapply (sorted_to_minimum ? ? ? H13 n2)
                                           [simplify in Hletin2;lapply (sorted_to_minimum ? ? ? Hletin2 (nth_prime n1))
                                              [unfold in Hletin3;unfold in Hletin4;
                                               elim (lt_nth_prime_to_not_prime ? ? Hletin4 Hletin3);
                                               apply H12;
                                               apply (ex_intro ? ? [nth_prime (S n1)]);
                                               apply (ex_intro ? ? (l2@(nth_prime n1::a4)));
                                               reflexivity
                                              |apply (ex_intro ? ? l2);apply (ex_intro ? ? a4);reflexivity]
                                           |simplify;apply in_list_head]]]
                                  |change in H13 with (t::(l@(nth_prime n1::a4)) = t1::(l2@(nth_prime (S n1)::a5)));
                                   destruct H13;apply (H7 l2 ? ? Hcut3)
                                     [intros;apply H8;simplify;apply in_list_cons;
                                      assumption
                                     |simplify in H12;
                                      apply (sorted_cons_to_sorted ? ? ? H12)]]]]
                         rewrite > Hcut2 in ⊢ (? ? ? (? ? ? (? ? ? %)));
                         apply H10
                        |apply (trans_le ? ? ? Hletin);apply lt_to_le;
                         apply (trans_le ? ? ? H5 Hcut)
                        |apply prime_nth_prime]
                     |rewrite > H3;assumption
                     |apply prime_nth_prime]]
               |apply le_times_r;assumption]
            |apply prime_nth_prime
            |rewrite < H3;apply increasing_nth_prime]]]
   |assumption]
qed. *)

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
  
(* not used
theorem divides_pi_p_to_divides: \forall p,n,b,g.prime p \to 
divides p (pi_p n b g) \to \exists i. (i < n \and (b i = true \and
divides p (g i))).
intros 2.elim n
  [simplify in H1.
   apply False_ind.
   apply (le_to_not_lt p 1)
    [apply divides_to_le
      [apply le_n
      |assumption
      ]
    |elim H.assumption
    ]
  |apply (bool_elim ? (b n1));intro
    [rewrite > (true_to_pi_p_Sn ? ? ? H3) in H2.
     elim (divides_times_to_divides ? ? ? H1 H2)
      [apply (ex_intro ? ? n1).
       split
        [apply le_n
        |split;assumption
        ]
      |elim (H ? ? H1 H4).
       elim H5.
       apply (ex_intro ? ? a).
       split
        [apply lt_to_le.apply le_S_S.assumption
        |assumption
        ]
      ]
    |rewrite > (false_to_pi_p_Sn ? ? ? H3) in H2.
     elim (H ? ? H1 H2).
     elim H4.
     apply (ex_intro ? ? a).
     split
      [apply lt_to_le.apply le_S_S.assumption
      |assumption
      ]
    ]
  ]
qed.
      
theorem divides_B: \forall n,p.prime p \to p \divides (B n) \to
p \le n \land \exists i.mod (n /(exp p (S i))) 2 \neq O.
intros.
unfold B in H1.
elim (divides_pi_p_to_divides ? ? ? ? H H1).
elim H2.clear H2.
elim H4.clear H4.
elim (divides_pi_p_to_divides ? ? ? ? H H5).clear H5.
elim H4.clear H4.
elim H6.clear H6.
cut (p = a)
  [split
    [rewrite > Hcut.apply le_S_S_to_le.assumption
    |apply (ex_intro ? ? a1).
     rewrite > Hcut.
     intro.
     change in H7:(? ? %) with (exp a ((n/(exp a (S a1))) \mod 2)).
     rewrite > H6 in H7.
     simplify in H7.
     absurd (p \le 1)
      [apply divides_to_le[apply lt_O_S|assumption]
      |apply lt_to_not_le.elim H.assumption
      ]
    ]
  |apply (divides_exp_to_eq ? ? ? H ? H7).
   apply primeb_true_to_prime.
   assumption
  ]
qed.
*)

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
intros.unfold B_split1.unfold teta.
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
(* weaker form 
       rewrite < distr_times_plus.
       apply le_times_r.
       apply (trans_le ? ((2*n + n)/3))
        [apply le_plus_div.apply lt_O_S
        |rewrite < sym_plus.
         change in ⊢ (? (? % ?) ?) with (3*n).
         rewrite < sym_times.
         rewrite > lt_O_to_div_times
          [apply le_n
          |apply lt_O_S
          ]
        ]
      ] *)
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
