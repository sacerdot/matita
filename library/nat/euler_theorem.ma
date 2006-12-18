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

set "baseuri" "cic:/matita/nat/euler_theorem".

include "nat/iteration.ma".
include "nat/totient.ma".

(* da spostare *)
lemma le_to_le_to_eq: \forall n,m. n \le m \to m \le n \to n = m.
apply nat_elim2
  [intros.apply le_n_O_to_eq.assumption
  |intros.apply sym_eq.apply le_n_O_to_eq.assumption
  |intros.apply eq_f.apply H
    [apply le_S_S_to_le.assumption
    |apply le_S_S_to_le.assumption
    ]
  ]
qed.

lemma gcd_n_n: \forall n.gcd n n = n.
intro.elim n
  [reflexivity
  |apply le_to_le_to_eq
    [apply divides_to_le
      [apply lt_O_S
      |apply divides_gcd_n
      ]
    |apply divides_to_le
      [apply lt_O_gcd.apply lt_O_S
      |apply divides_d_gcd
        [apply divides_n_n|apply divides_n_n]
      ]
    ]
  ]
qed.


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

(* da spostare *)
lemma gcd_n_times_nm: \forall n,m. O < m \to gcd n (n*m) = n.
intro.apply (nat_case n)
  [intros.reflexivity
  |intros.
   apply le_to_le_to_eq
    [apply divides_to_le
      [apply lt_O_S|apply divides_gcd_n]
    |apply divides_to_le
      [apply lt_O_gcd.rewrite > (times_n_O O).
       apply lt_times[apply lt_O_S|assumption]
      |apply divides_d_gcd
        [apply (witness ? ? m1).reflexivity
        |apply divides_n_n
        ]
      ]
    ]
  ]
qed.

(* da spostare *)
lemma eq_gcd_SO_to_not_divides: \forall n,m. (S O) < n \to 
(gcd n m) = (S O) \to \lnot (divides n m).
intros.unfold.intro.
elim H2.
generalize in match H1.
rewrite > H3.
intro.
cut (O < n2)
  [elim (gcd_times_SO_to_gcd_SO n n n2 ? ? H4)
    [cut (gcd n (n*n2) = n)
      [apply (lt_to_not_eq (S O) n)
        [assumption|rewrite < H4.assumption]
      |apply gcd_n_times_nm.assumption
      ]
    |apply (trans_lt ? (S O))[apply le_n|assumption]
    |assumption
    ]
  |elim (le_to_or_lt_eq O n2 (le_O_n n2))
    [assumption
    |apply False_ind.
     apply (le_to_not_lt n (S O))
      [rewrite < H4.
       apply divides_to_le
        [rewrite > H4.apply lt_O_S
        |apply divides_d_gcd
          [apply (witness ? ? n2).reflexivity
          |apply divides_n_n
          ]
        ]
      |assumption
      ]
    ]
  ]
qed.

theorem gcd_Pi_P: \forall n,k. O < k \to k \le n \to
gcd n (Pi_P (\lambda i.eqb (gcd i n) (S O)) k) = (S O).
intros 3.elim H
  [rewrite > Pi_P_S.
   cut (eqb (gcd (S O) n) (S O) = true)
    [rewrite > Hcut.
     change with ((gcd n (S O)) = (S O)).auto
    |apply eq_to_eqb_true.auto
    ]
  |rewrite > Pi_P_S.
   apply eqb_elim
    [intro.
     change with 
       ((gcd n ((S n1)*(Pi_P (\lambda i.eqb (gcd i n) (S O)) n1))) = (S O)).
     apply eq_gcd_times_SO
      [unfold.apply le_S.assumption
      |apply lt_O_Pi_P.
      |rewrite > sym_gcd. assumption.
      |apply H2.
       apply (trans_le ? (S n1))[apply le_n_Sn|assumption]
      ]
    |intro.
     change with 
       (gcd n (Pi_P (\lambda i.eqb (gcd i n) (S O)) n1) = (S O)).
     apply H2.
     apply (trans_le ? (S n1))[apply le_n_Sn|assumption]
    ]
  ]
qed.

theorem congruent_map_iter_P_times:\forall f:nat \to nat. \forall a,n:nat.
O < a \to
congruent
(map_iter_P n (\lambda i.eqb (gcd i a) (S O)) (\lambda x.f x) (S O) times)
(map_iter_P n (\lambda i.eqb (gcd i a) (S O)) 
 (\lambda x.f x \mod a) (S O) times) a.     
intros.
elim n
  [rewrite > map_iter_P_O.
   apply (congruent_n_n ? a)
  |apply (eqb_elim (gcd (S n1) a) (S O))
    [intro.
     rewrite > map_iter_P_S_true
      [rewrite > map_iter_P_S_true
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
     rewrite > map_iter_P_S_false
      [rewrite > map_iter_P_S_false
        [assumption
        |apply not_eq_to_eqb_false.assumption
        ]
      |apply not_eq_to_eqb_false.assumption
      ]
    ]
  ]
qed.

theorem lt_S_to_lt: \forall n,m. S n < m \to n < m.
intros.
apply (trans_lt ? (S n))
  [apply le_n|assumption]
qed.

theorem gcd_SO_to_lt_O: \forall i,n. (S O) < n \to gcd i n = (S O) \to
O < i.
intros.
elim (le_to_or_lt_eq ? ? (le_O_n i))
  [assumption
  |absurd ((gcd i n) = (S O))
    [assumption
    |rewrite < H2.
     simplify.
     unfold.intro.
     apply (lt_to_not_eq (S O) n H).
     apply sym_eq.assumption
    ]
  ]
qed.

theorem gcd_SO_to_lt_n: \forall i,n. (S O) < n \to i \le n \to gcd i n = (S O) \to
i < n.
intros.
elim (le_to_or_lt_eq ? ? H1)
  [assumption
  |absurd ((gcd i n) = (S O))
    [assumption
    |rewrite > H3.
     rewrite > gcd_n_n.
     unfold.intro.
     apply (lt_to_not_eq (S O) n H).
     apply sym_eq.assumption
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
               auto
              ]
            ]
          ]
        |auto
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
               auto
              ]
            ]
          ]
        |auto
        ]
      ]
    ]
  ]
qed.

theorem congruent_exp_totient_SO: \forall n,a:nat. (S O) < n \to
gcd a n = (S O) \to congruent (exp a (totient n)) (S O) n. 
intros.
cut (O < a)
  [apply divides_to_congruent
    [apply (trans_lt ? (S O)).apply lt_O_S. assumption
    |change with (O < exp a (totient n)).apply lt_O_exp.assumption
    |apply (gcd_SO_to_divides_times_to_divides (Pi_P (\lambda i.eqb (gcd i n) (S O)) n))
      [apply (trans_lt ? (S O)).apply lt_O_S. assumption
      |apply gcd_Pi_P
        [apply (trans_lt ? (S O)).apply lt_O_S. assumption
        |apply le_n
        ]
      |rewrite < sym_times.
       rewrite > times_minus_l.
       rewrite > (sym_times (S O)).
       rewrite < times_n_SO.
       rewrite > totient_card.
       rewrite > a_times_Pi_P.
       apply congruent_to_divides
        [apply (trans_lt ? (S O)).apply lt_O_S. assumption
        | apply (transitive_congruent n ? 
                 (map_iter_P n (\lambda i.eqb (gcd i n) (S O)) (\lambda x.a*x \mod n) (S O) times))
          [apply (congruent_map_iter_P_times ? n n).
           apply (trans_lt ? (S O))
            [apply lt_O_S|assumption]
            |unfold Pi_P.
             cut ( (map_iter_P n (\lambda i:nat.eqb (gcd i n) (S O)) (\lambda n:nat.n) (S O) times)
                 = (map_iter_P n (\lambda i:nat.eqb (gcd i n) (S O)) (\lambda x:nat.a*x\mod n) (S O) times))
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
     