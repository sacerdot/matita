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

include "nat/primes.ma".
include "list/sort.ma".

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
     [|elim l2 in H2 ⊢ %
        [reflexivity
        |simplify in H5;elim (not_le_Sn_O ? H5)]]
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
     |simplify;elim (H k (filter ? l (\lambda x.notb (divides_b a x))) (a::l1))
        [split;
           [assumption
           |intro;apply H8;]
        |split;intros
           [elim (in_list_cons_case ? ? ? ? H7);
              [rewrite > H8;split
                 [split
                    [unfold;intros;split
                       [elim (H3 a);elim H9
                          [elim H11;assumption
                          |apply in_list_head]
                       |intros;elim (le_to_or_lt_eq ? ? (divides_to_le ? ? ? H9))
                          [cut (1 < a) as Lt1a; [2: apply (trans_lt ??? H10 H11)]
                           letin a1 ≝ (smallest_factor a);
                           lapply (divides_smallest_factor_n a) as H14;
                            [2: apply (trans_lt ? (S O) ? ? Lt1a);
                                apply lt_O_S
                            | fold unfold a1 a1 in H14;
                              lapply (prime_smallest_factor_n a Lt1a) as H16;
                              fold unfold a1 a1 in H16;
                              cut (a1 ≤ m) as H15;
                              [2: generalize in match (leb_to_Prop a1 m);
                                  elim (leb a1 m); simplify in H12;
                                   [ assumption
                                   | elim (lt_smallest_factor_to_not_divides a m Lt1a H10 ? H9);
                                     apply (not_le_to_lt ?? H12)]
                              | clearbody a1;
                                elim (H3 a);elim H12
                                [clear H13 H12;elim (H18 ? ? H14);elim (H2 a1);
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
                                |apply in_list_head]]]
                          |elim (H3 a);elim H11
                             [elim H13;apply lt_to_le;assumption
                             |apply in_list_head]
                          |assumption]]
                    |elim (H3 a);elim H9
                       [elim H11;assumption
                       |apply in_list_head]]
                 |intros;elim (le_to_or_lt_eq a x)
                    [assumption
                    |rewrite > H10 in H9;lapply (in_list_filter_to_p_true ? ? ? H9);
                     lapply (divides_n_n x);
                     rewrite > (divides_to_divides_b_true ? ? ? Hletin1) in Hletin
                       [simplify in Hletin;destruct Hletin
                       |rewrite < H10;elim (H3 a);elim H11
                          [elim H13;apply lt_to_le;assumption
                          |apply in_list_head]]
                    |apply lt_to_le;apply (sorted_to_minimum ? ? ? ? H6);apply (in_list_filter ? ? ? H9)]]
                 |elim (H2 p);elim (H9 H8);split
                    [assumption
                    |intros;apply H12;apply in_list_cons;apply (in_list_filter ? ? ? H13)]]
           |elim (decidable_eq_nat p a)
              [rewrite > H10;apply in_list_head
              |apply in_list_cons;elim (H2 p);apply (H12 H7 H8);intros;
               apply (trans_le ? a)
                 [elim (decidable_lt p a)
                    [assumption
                    |lapply (not_lt_to_le ? ? H14);
                     lapply (decidable_divides a p)
                       [elim Hletin1
                          [elim H7;lapply (H17 ? H15)
                             [elim H10;symmetry;assumption
                             |elim (H3 a);elim H18
                                [elim H20;assumption
                                |apply in_list_head]]
                          |elim (Not_lt_n_n p);apply H9;apply in_list_filter_r
                             [elim (H3 p);apply (in_list_tail ? ? a)
                                [apply H17
                                   [apply prime_to_lt_SO;assumption
                                   |assumption
                                   |intros;elim H7;intro;lapply (H20 ? H21)
                                      [rewrite > Hletin2 in H18;elim (H11 H18);
                                       lapply (H23 a)
                                         [elim (lt_to_not_le ? ? Hletin3 Hletin)
                                         |apply in_list_head]
                                      |apply prime_to_lt_SO;elim (H2 p1);elim (H22 H18);
                                       elim H24;assumption]]
                                |unfold;intro;apply H15;rewrite > H18;apply divides_n_n]
                             |rewrite > (not_divides_to_divides_b_false ? ? ? H15);
                                [reflexivity
                                |elim (H3 a);elim H16
                                   [elim H18;apply lt_to_le;assumption
                                   |apply in_list_head]]]]
                       |elim (H3 a);elim H15
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
                     |elim (H3 a);elim H13
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
                  |lapply (H11 a)
                     [rewrite > (not_divides_to_divides_b_false ? ? ? Hletin);
                        [reflexivity
                        |elim (H3 a);elim H13
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
            |simplify;elim (notb (divides_b a a1));simplify
               [lapply (sorted_cons_to_sorted ? ? ? ? H8);lapply (H7 Hletin);
                apply (sort_cons ? ? ? ? Hletin1);intros;
                apply (sorted_to_minimum ? ? ? ? H8);apply (in_list_filter ? ? ? H9);
               |apply H7;apply (sorted_cons_to_sorted ? ? ? ? H8)]]]]]
qed.

definition list_of_primes \def \lambda n.\lambda l.
\forall p.in_list nat p l  \to prime p \land p \leq n.

lemma in_list_SSO_list_n : \forall n.2 \leq n \to in_list ? 2 (list_n n).
intros;elim H;simplify
  [apply in_list_head
  |elim H1 in H2 ⊢ %;simplify;apply in_list_head]
qed.

lemma le_list_n_aux_k_k : \forall n,m,k.in_list ? n (list_n_aux m k) \to
                          k \leq n.
intros 2;elim m
  [simplify in H;elim (not_in_list_nil ? ? H)
  |simplify in H1;elim (in_list_cons_case ? ? ? ? H1)
     [rewrite > H2;apply le_n
     |apply lt_to_le;apply H;assumption]]
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
simplify in Hletin;elim m in H Hletin ⊢ %
   [simplify in H;elim (not_in_list_nil ? ? H)
   |simplify in H;assumption]
qed.


lemma le_list_n_aux_r : \forall n,m.O < m \to \forall k.k \leq n \to n \leq k+m-1 \to in_list ? n (list_n_aux m k).
intros 3;elim H 0
  [intros;simplify;rewrite < plus_n_Sm in H2;simplify in H2;
   rewrite < plus_n_O in H2;rewrite < minus_n_O in H2;
   rewrite > (antisymmetric_le k n H1 H2);apply in_list_head
  |intros 5;simplify;elim H3 in H2 ⊢ %
     [apply in_list_head
     |apply in_list_cons;apply H5
        [apply le_S_S;assumption
        |rewrite < plus_n_Sm in H6;apply H6]]]
qed.

lemma le_list_n_r : \forall n,m.S O < m \to 2 \leq n \to n \leq m \to in_list ? n (list_n m).
intros;unfold list_n;apply le_list_n_aux_r
  [elim H;simplify
     [apply lt_O_S
     |elim H3 in H4 ⊢ %;
        [apply lt_O_S
        |simplify in H7;apply le_S;assumption]]
  |assumption
  |simplify;elim H in H2 ⊢ %;simplify;assumption]
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

