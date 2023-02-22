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

include "nat/map_iter_p.ma".
include "nat/totient.ma".

(*
lemma count_card: \forall p.\forall n.
p O = false \to count (S n) p = card n p.
intros.elim n
  [simplify.rewrite > H. reflexivity
  |simplify.
   rewrite < plus_n_O.
   apply eq_f.assumption
  ]
qed.

lemma count_card1: \forall p.\forall n.
p O = false \to p n = false \to count n p = card n p.
intros 3.apply (nat_case n)
  [intro.simplify.rewrite > H. reflexivity
  |intros.rewrite > (count_card ? ? H).
   simplify.rewrite > H1.reflexivity
  ]
qed.
 

( a reformulation of totient using card insted of count )

lemma totient_card: \forall n. 
totient n = card n (\lambda i.eqb (gcd i n) (S O)).
intro.apply (nat_case n)
  [reflexivity
  |intro.apply (nat_case m)
    [reflexivity
    |intro.apply count_card1
      [reflexivity
      |rewrite > gcd_n_n.reflexivity
      ]
    ]
  ]
qed.
*)

(*this obvious property is useful because simplify, sometimes,
  "simplifies too much", and doesn't allow to obtain this simple result.
 *)
theorem card_Sn: \forall n:nat. \forall p:nat \to bool.
card (S n) p = (bool_to_nat (p (S n))) + (card n p).
intros.
simplify.
reflexivity.
qed.

(* a reformulation of totient using card insted of sigma_p *)

theorem totient_card_aux: \forall n,m: nat.
m = n \to
sigma_p (S (S n)) (\lambda m:nat.eqb (gcd m (S (S n))) (S O)) (\lambda x:nat. (S O)) 
= card (S n) (\lambda m:nat.eqb (gcd m (S (S n))) (S O)).
intros.
rewrite < H in \vdash (? ? (? % ? ?) ?).
rewrite < H in \vdash (? ? ? (? % ?)).
elim (m)
[ rewrite > card_Sn.
  cut ((eqb (gcd (S O)(S (S n))) (S O) ) = true)
  [ rewrite > Hcut.
    simplify in \vdash (? ? ? %).
    rewrite > true_to_sigma_p_Sn
    [ rewrite > false_to_sigma_p_Sn in \vdash (? ? (? ? %) ?)
      [ simplify in \vdash (? ? % ?).
        reflexivity
      | rewrite > gcd_O_n.
        apply not_eq_to_eqb_false.
        apply not_eq_S.             
        unfold Not.
        intro.        
        cut ( (S n) \le O)
        [ apply (not_le_Sn_n n ?).
          apply (transitive_le (S n) O n ? ?);
          [ apply (Hcut1)
          | apply (le_O_n n)
          ]
        | rewrite > H1.
          apply le_n
        ]
      ]
    | assumption
    ]
  | apply eq_to_eqb_true.
    rewrite > gcd_SO_n.
    reflexivity   
  ]
| cut ((eqb (gcd (S (S n1)) (S (S n))) (S O))  = true 
    \lor (eqb (gcd (S (S n1)) (S (S n))) (S O))  = false)
  [ elim Hcut
    [ rewrite > card_Sn.
      rewrite > true_to_sigma_p_Sn
      [ rewrite > H2.
        simplify in \vdash (? ? ? (? % ?)).
        apply eq_f.
        assumption
      | assumption
      ]      
    | rewrite > card_Sn.
      rewrite > false_to_sigma_p_Sn
      [ rewrite > H2.
        simplify in \vdash (? ? ? (? % ?)).
        rewrite > sym_plus.
        rewrite < plus_n_O.
        assumption
      | assumption  
      ]
    ]
  | elim (eqb (gcd (S (S n1)) (S (S n))) (S O))
    [ left.
      reflexivity
    | right.
      reflexivity
    ]
  ]
]
qed.
  
lemma totient_card: \forall n.
totient n = card n (\lambda i.eqb (gcd i n) (S O)).
intros.
elim n
[ simplify.
  reflexivity
| elim n1
  [ simplify.
    reflexivity
  |
    (*unfold card.
    intros.*)
    (* here simplify creates problems: it seems it simplifies too much. I had to 
     * introduce the obvious theorem card_Sn.
     *)
    rewrite > card_Sn.
    rewrite > (gcd_n_n (S (S n2))).
    cut ((eqb (S (S n2)) (S O)) = false)
    [ rewrite > Hcut.
      simplify in \vdash (? ? ? (? % ?)).
      rewrite > sym_plus.
      rewrite < (plus_n_O).
      unfold totient.      
      apply (totient_card_aux n2 n2).
      reflexivity    
    | apply not_eq_to_eqb_false.
      apply not_eq_S.
      unfold Not.
      intro.
      cut ( (S n2) \le O)
        [ apply (not_le_Sn_n n2 ?).
          apply (transitive_le (S n2) O n2 ? ?);
          [ apply (Hcut)
          | apply (le_O_n n2)
          ]
        | rewrite > H2.
          apply le_n
        ]
    ]
  ]
]
qed.
  
theorem gcd_pi_p: \forall n,k. O < k \to k \le n \to
gcd n (pi_p (\lambda i.eqb (gcd i n) (S O)) k) = (S O).
intros 3.elim H
  [rewrite > pi_p_S.
   cut (eqb (gcd (S O) n) (S O) = true)
    [rewrite > Hcut.
     change with ((gcd n (S O)) = (S O)).
     apply (transitive_eq nat (gcd n (S O)) (gcd (S O) n) (S O) ? ?);
     [ apply (sym_eq nat (gcd (S O) n) (gcd n (S O)) ?).
       apply (symmetric_gcd (S O) n).
     | apply (gcd_SO_n n).
     ]
    |apply eq_to_eqb_true.
     apply (gcd_SO_n n)
    ]
  |rewrite > pi_p_S.
   apply eqb_elim
    [intro.
     change with 
       ((gcd n ((S n1)*(pi_p (\lambda i.eqb (gcd i n) (S O)) n1))) = (S O)).
     apply eq_gcd_times_SO
      [unfold.apply le_S.assumption
      |apply lt_O_pi_p.
      |rewrite > sym_gcd. assumption.
      |apply H2.
       apply (trans_le ? (S n1))[apply le_n_Sn|assumption]
      ]
    |intro.
     change with 
       (gcd n (pi_p (\lambda i.eqb (gcd i n) (S O)) n1) = (S O)).
     apply H2.
     apply (trans_le ? (S n1))[apply le_n_Sn|assumption]
    ]
  ]
qed.

theorem congruent_map_iter_p_times:\forall f:nat \to nat. \forall a,n:nat.
O < a \to
congruent
(map_iter_p n (\lambda i.eqb (gcd i a) (S O)) (\lambda x.f x) (S O) times)
(map_iter_p n (\lambda i.eqb (gcd i a) (S O)) 
 (\lambda x.f x \mod a) (S O) times) a.     
intros.
elim n
  [rewrite > map_iter_p_O.
   apply (congruent_n_n ? a)
  |apply (eqb_elim (gcd (S n1) a) (S O))
    [intro.
     rewrite > map_iter_p_S_true
      [rewrite > map_iter_p_S_true
        [apply congruent_times
          [assumption
          |apply congruent_n_mod_n.assumption
          |assumption
          ]
        |apply eq_to_eqb_true.assumption
        ]
      |apply eq_to_eqb_true.assumption
      ]
    |intro. 
     rewrite > map_iter_p_S_false
      [rewrite > map_iter_p_S_false
        [assumption
        |apply not_eq_to_eqb_false.assumption
        ]
      |apply not_eq_to_eqb_false.assumption
      ]
    ]
  ]
qed.

theorem permut_p_mod: \forall a,n. S O < n \to O < a \to gcd a n = (S O) \to
permut_p (\lambda x:nat.a*x \mod n) (\lambda i:nat.eqb (gcd i n) (S O)) n.
intros.
lapply (lt_S_to_lt ? ? H) as H3.
unfold permut_p.
simplify.
intros.
split
  [split
    [apply lt_to_le.
     apply lt_mod_m_m.
     assumption
    |rewrite > sym_gcd.
     rewrite > gcd_mod
      [apply eq_to_eqb_true.
       rewrite > sym_gcd.
       apply eq_gcd_times_SO
        [assumption
        |apply (gcd_SO_to_lt_O i n H).
         apply eqb_true_to_eq.
         assumption
        |rewrite > sym_gcd.assumption
        |rewrite > sym_gcd.apply eqb_true_to_eq.
         assumption
        ]
      |assumption
      ]
    ]
  |intros.
   lapply (gcd_SO_to_lt_n ? ? H H4 (eqb_true_to_eq ? ? H5)) as H9.
   lapply (gcd_SO_to_lt_n ? ? H H7 (eqb_true_to_eq ? ? H6)) as H10.
   lapply (gcd_SO_to_lt_O ? ? H (eqb_true_to_eq ? ? H5)) as H11.
   lapply (gcd_SO_to_lt_O ? ? H (eqb_true_to_eq ? ? H6)) as H12.
   unfold Not.intro.
   apply H8.
   apply (nat_compare_elim i j)
    [intro.
     absurd (j < n)
      [assumption
      |apply le_to_not_lt.
       apply (trans_le ? (j -i))
        [apply divides_to_le
          [(*fattorizzare*)
           apply (lt_plus_to_lt_l i).
           simplify.
           rewrite < (plus_minus_m_m)
            [assumption|apply lt_to_le.assumption]
          |apply (gcd_SO_to_divides_times_to_divides a)
            [assumption
            |rewrite > sym_gcd.assumption
            |apply mod_O_to_divides
              [assumption
              |rewrite > distr_times_minus.
               apply (divides_to_mod_O n (minus (times a j) (times a i)) ? ?);
               [ apply (H3).
               | apply (eq_mod_to_divides (times a j) (times a i) n ? ?);
                [ apply (H3).
                |apply (sym_eq nat (mod (times a i) n) (mod (times a j) n) ?).
                 apply (H13).
                ]
               ]
              ]
            ]
          ]
        | apply (le_minus_m j i).
        ]
      ]
    |intro.assumption
    |intro.
     absurd (i < n)
      [assumption
      |apply le_to_not_lt.
       apply (trans_le ? (i -j))
        [apply divides_to_le
          [(*fattorizzare*)
           apply (lt_plus_to_lt_l j).
           simplify.
           rewrite < (plus_minus_m_m)
            [assumption|apply lt_to_le.assumption]
          |apply (gcd_SO_to_divides_times_to_divides a)
            [assumption
            |rewrite > sym_gcd.assumption
            |apply mod_O_to_divides
              [assumption
              |rewrite > distr_times_minus.
               apply (divides_to_mod_O n (minus (times a i) (times a j)) ? ?);
               [apply (H3).
               | apply (eq_mod_to_divides (times a i) (times a j) n ? ?);
                 [apply (H3).
                 |apply (H13).
                 ]
               ]
              ]
            ]
          ]
        | apply (le_minus_m i j).
        ]
      ]
    ]
  ]
qed.

theorem congruent_exp_totient_SO: \forall n,a:nat. (S O) < n \to
gcd a n = (S O) \to congruent (exp a (totient n)) (S O) n. 
intros.
cut (O < a)
  [ apply divides_to_congruent
    [apply (trans_lt ? (S O)).apply lt_O_S. assumption
    |change with (O < exp a (totient n)).apply lt_O_exp.assumption
    |apply (gcd_SO_to_divides_times_to_divides (pi_p (\lambda i.eqb (gcd i n) (S O)) n))
      [apply (trans_lt ? (S O)).apply lt_O_S. assumption
      |apply gcd_pi_p
        [apply (trans_lt ? (S O)).apply lt_O_S. assumption
        |apply le_n
        ]
      |rewrite < sym_times.
       rewrite > times_minus_l.
       rewrite > (sym_times (S O)).
       rewrite < times_n_SO.
       rewrite > totient_card.
       rewrite > a_times_pi_p.
       apply congruent_to_divides
        [apply (trans_lt ? (S O)).apply lt_O_S. assumption
        | apply (transitive_congruent n ? 
                 (map_iter_p n (\lambda i.eqb (gcd i n) (S O)) (\lambda x.a*x \mod n) (S O) times))
          [apply (congruent_map_iter_p_times ? n n).
           apply (trans_lt ? (S O))
            [apply lt_O_S|assumption]
            |unfold pi_p.
             cut ( (map_iter_p n (\lambda i:nat.eqb (gcd i n) (S O)) (\lambda n:nat.n) (S O) times)
                 = (map_iter_p n (\lambda i:nat.eqb (gcd i n) (S O)) (\lambda x:nat.a*x\mod n) (S O) times))
              [rewrite < Hcut1.apply congruent_n_n
              |apply (eq_map_iter_p_permut ? ? ? ? ? (λm.m))
                [apply assoc_times
                |apply sym_times
                |apply (permut_p_mod ? ? H Hcut H1)
                |simplify.
                 apply not_eq_to_eqb_false.
                 unfold.intro.
                 apply (lt_to_not_eq (S O) n)
                  [assumption|apply sym_eq.assumption]
                ]
              ]
            ]
          ]
        ]
      ] 
    |elim (le_to_or_lt_eq O a (le_O_n a)) 
      [assumption
      |absurd (gcd a n = S O)
        [assumption
        |rewrite < H2.
         simplify.
         unfold.intro.
         apply (lt_to_not_eq (S O) n)
          [assumption|apply sym_eq.assumption] 
        ]
      ]     
    ]
qed.
