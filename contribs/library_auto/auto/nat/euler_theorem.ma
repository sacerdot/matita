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

set "baseuri" "cic:/matita/library_autobatch/nat/euler_theorem".

include "auto/nat/map_iter_p.ma".
include "auto/nat/totient.ma".

(* a reformulation of totient using card insted of count *)
lemma totient_card: \forall n. 
totient n = card n (\lambda i.eqb (gcd i n) (S O)).
intro.
apply (nat_case n)
[ reflexivity
| intro.
  apply (nat_case m)
  [ reflexivity
  | intro.
    apply count_card1;autobatch
    (*[ reflexivity
    | autobatch.rewrite > gcd_n_n.
      reflexivity
    ]*)
  ]
]
qed.

theorem gcd_pi_p: \forall n,k. O < k \to k \le n \to
gcd n (pi_p (\lambda i.eqb (gcd i n) (S O)) k) = (S O).
intros 3.
elim H
[ rewrite > pi_p_S.
  cut (eqb (gcd (S O) n) (S O) = true)
  [ rewrite > Hcut.
    autobatch
    (*change with ((gcd n (S O)) = (S O)).
    autobatch*)
  | autobatch
    (*apply eq_to_eqb_true.autobatch*)
  ]
| rewrite > pi_p_S.
  apply eqb_elim
  [ intro.
    change with 
     ((gcd n ((S n1)*(pi_p (\lambda i.eqb (gcd i n) (S O)) n1))) = (S O)).
    apply eq_gcd_times_SO
    [ autobatch
      (*unfold.
      apply le_S.
      assumption*)
    | apply lt_O_pi_p.
    | autobatch
      (*rewrite > sym_gcd. 
      assumption.*)
    | apply H2.
      autobatch
      (*apply (trans_le ? (S n1))
      [ apply le_n_Sn
      | assumption
      ]*)
    ]
  | intro.
    change with 
      (gcd n (pi_p (\lambda i.eqb (gcd i n) (S O)) n1) = (S O)).
    apply H2.
    autobatch
    (*apply (trans_le ? (S n1))
    [ apply le_n_Sn
    | assumption
    ]*)
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
[ autobatch
  (*rewrite > map_iter_p_O.
  apply (congruent_n_n ? a)*)
| apply (eqb_elim (gcd (S n1) a) (S O))
  [ intro.
    rewrite > map_iter_p_S_true
    [ rewrite > map_iter_p_S_true
      [ apply congruent_times
        [ assumption
        | autobatch
          (*apply congruent_n_mod_n.
          assumption*)
        | (*NB qui autobatch non chiude il goal*)
          assumption
        ]
      | autobatch
        (*apply eq_to_eqb_true.
        assumption*)
      ]
    | autobatch
      (*apply eq_to_eqb_true.
      assumption*)
    ]
  | intro. 
    rewrite > map_iter_p_S_false
    [ rewrite > map_iter_p_S_false
      [ (*BN qui autobatch non chiude il goal*)
        assumption
      | autobatch
        (*apply not_eq_to_eqb_false.
        assumption*)
      ]
    | autobatch
      (*apply not_eq_to_eqb_false.
      assumption*)
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
[ split
  [ autobatch
    (*apply lt_to_le.
    apply lt_mod_m_m.
    assumption*)
  | rewrite > sym_gcd.
    rewrite > gcd_mod
    [ apply eq_to_eqb_true.
      rewrite > sym_gcd.
      apply eq_gcd_times_SO
      [ assumption
      | apply (gcd_SO_to_lt_O i n H).
        autobatch
        (*apply eqb_true_to_eq.
        assumption*)
      | autobatch
        (*rewrite > sym_gcd.
        assumption*)
      | autobatch
        (*rewrite > sym_gcd.
        apply eqb_true_to_eq.
        assumption*)
      ]
    | assumption
   ]
  ]
| intros.
  lapply (gcd_SO_to_lt_n ? ? H H4 (eqb_true_to_eq ? ? H5)) as H9.
  lapply (gcd_SO_to_lt_n ? ? H H7 (eqb_true_to_eq ? ? H6)) as H10.
  lapply (gcd_SO_to_lt_O ? ? H (eqb_true_to_eq ? ? H5)) as H11.
  lapply (gcd_SO_to_lt_O ? ? H (eqb_true_to_eq ? ? H6)) as H12.
  unfold Not.
  intro.
  apply H8.
  apply (nat_compare_elim i j)
  [ intro.
    absurd (j < n)
    [ assumption
    | apply le_to_not_lt.
      apply (trans_le ? (j -i))
      [ apply divides_to_le
        [(*fattorizzare*)
          unfold lt.autobatch.
          (*apply (lt_plus_to_lt_l i).
          simplify.
          rewrite < (plus_minus_m_m)
          [ assumption
          | apply lt_to_le.
            assumption
          ]*)
        | apply (gcd_SO_to_divides_times_to_divides a)
          [ assumption
          | autobatch
            (*rewrite > sym_gcd.
            assumption*)
          | apply mod_O_to_divides
            [ assumption
            | rewrite > distr_times_minus.
              autobatch
            ]
          ]
        ]
      | autobatch
      ]
    ]
  | autobatch
    (*intro.
    assumption*)
  | intro.
    absurd (i < n)
    [ assumption
    | apply le_to_not_lt.
      apply (trans_le ? (i -j))
      [ apply divides_to_le
        [(*fattorizzare*)
          unfold lt.autobatch.
          (*apply (lt_plus_to_lt_l j).
          simplify.
          rewrite < (plus_minus_m_m)
          [ assumption
          | apply lt_to_le.
            assumption
          ]*)
        | apply (gcd_SO_to_divides_times_to_divides a)
          [ assumption
          | autobatch
            (*rewrite > sym_gcd.
            assumption*)
          | apply mod_O_to_divides
            [ assumption
            | rewrite > distr_times_minus.
              autobatch
            ]
          ]
        ]
      | autobatch
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
  [ autobatch
    (*apply (trans_lt ? (S O)).
    apply lt_O_S.
    assumption*)
  | autobatch
    (*change with (O < exp a (totient n)).
    apply lt_O_exp.
    assumption*)
  | apply (gcd_SO_to_divides_times_to_divides (pi_p (\lambda i.eqb (gcd i n) (S O)) n))
    [ autobatch
      (*apply (trans_lt ? (S O)).
      apply lt_O_S. 
      assumption*)
    | autobatch
      (*apply gcd_pi_p
      [ apply (trans_lt ? (S O)).
        apply lt_O_S. 
        assumption
      | apply le_n
      ]*)
    | rewrite < sym_times.
      rewrite > times_minus_l.
      rewrite > (sym_times (S O)).
      rewrite < times_n_SO.
      rewrite > totient_card.
      rewrite > a_times_pi_p.
      apply congruent_to_divides
      [ autobatch
        (*apply (trans_lt ? (S O)).
        apply lt_O_S. 
        assumption*)
      | apply (transitive_congruent n ? 
         (map_iter_p n (\lambda i.eqb (gcd i n) (S O)) (\lambda x.a*x \mod n) (S O) times))
        [ autobatch
          (*apply (congruent_map_iter_p_times ? n n).
          apply (trans_lt ? (S O))
          [ apply lt_O_S
          | assumption
          ]*)
        | unfold pi_p.
          cut ( (map_iter_p n (\lambda i:nat.eqb (gcd i n) (S O)) (\lambda n:nat.n) (S O) times)
             = (map_iter_p n (\lambda i:nat.eqb (gcd i n) (S O)) (\lambda x:nat.a*x\mod n) (S O) times))
          [ rewrite < Hcut1.
            apply congruent_n_n
          | apply (eq_map_iter_p_permut ? ? ? ? ? (λm.m))
            [ apply assoc_times
            | apply sym_times
            | apply (permut_p_mod ? ? H Hcut H1)
            | simplify.
              apply not_eq_to_eqb_false.
              unfold.
              intro.
              autobatch
              (*apply (lt_to_not_eq (S O) n)
              [ assumption
              | apply sym_eq.
                assumption
              ]*)
            ]
          ]
        ]
      ]
    ]
  ] 
| elim (le_to_or_lt_eq O a (le_O_n a));autobatch
  (*[ assumption
  | autobatch.absurd (gcd a n = S O)
    [ assumption
    | rewrite < H2.
      simplify.
      unfold.intro.
      apply (lt_to_not_eq (S O) n)
      [ assumption
      | apply sym_eq.
        assumption
      ] 
    ]
  ]*)     
]       
qed.  
     