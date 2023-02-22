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

set "baseuri" "cic:/matita/library_autobatch/nat/totient".

include "auto/nat/count.ma".
include "auto/nat/chinese_reminder.ma".

definition totient : nat \to nat \def
\lambda n. count n (\lambda m. eqb (gcd m n) (S O)).

theorem totient3: totient (S(S(S O))) = (S(S O)).
reflexivity.
qed.

theorem totient6: totient (S(S(S(S(S(S O)))))) = (S(S O)).
reflexivity.
qed.

theorem totient_times: \forall n,m:nat. (gcd m n) = (S O) \to
totient (n*m) = (totient n)*(totient m).
intro.
apply (nat_case n)
[ intros.
  autobatch
  (*simplify.
  reflexivity*)
| intros 2.
  apply (nat_case m1)
  [ rewrite < sym_times.
    rewrite < (sym_times (totient O)).
    simplify.
    intro.
    reflexivity
  | intros.
    unfold totient.     
    apply (count_times m m2 ? ? ? 
      (\lambda b,a. cr_pair (S m) (S m2) a b) 
      (\lambda x. x \mod (S m)) (\lambda x. x \mod (S m2)))
    [ intros.
      unfold cr_pair.
      apply (le_to_lt_to_lt ? (pred ((S m)*(S m2))))
      [ unfold min.
        apply le_min_aux_r
      | autobatch
        (*unfold lt.
        apply (nat_case ((S m)*(S m2)))
        [ apply le_n
        | intro.
          apply le_n
        ]*)
      ]
    | intros.
      generalize in match (mod_cr_pair (S m) (S m2) a b H1 H2 H).
      intro.
      elim H3.
      apply H4
    | intros.
      generalize in match (mod_cr_pair (S m) (S m2) a b H1 H2 H).
      intro.      
      elim H3.
      apply H5
    | intros.
      generalize in match (mod_cr_pair (S m) (S m2) a b H1 H2 H).
      intro.
      elim H3.
      apply eqb_elim
      [ intro.
        rewrite > eq_to_eqb_true
        [ rewrite > eq_to_eqb_true
          [ reflexivity
          | rewrite < H4.
            rewrite > sym_gcd.
            rewrite > gcd_mod
            [ apply (gcd_times_SO_to_gcd_SO ? ? (S m2))
              [ autobatch
                (*unfold lt.
                apply le_S_S.
                apply le_O_n*)
              | autobatch
                (*unfold lt.
                apply le_S_S.
                apply le_O_n*)
              | assumption
              ]
            | autobatch
              (*unfold lt.
              apply le_S_S.
              apply le_O_n*)
            ]
          ]           
        | rewrite < H5.
          rewrite > sym_gcd.
          rewrite > gcd_mod
          [ apply (gcd_times_SO_to_gcd_SO ? ? (S m))
            [ autobatch
              (*unfold lt.
              apply le_S_S.
              apply le_O_n*)
            | autobatch
              (*unfold lt.
              apply le_S_S.
              apply le_O_n*)
            | autobatch
              (*rewrite > sym_times.
              assumption*)
            ]
          | autobatch
            (*unfold lt.
            apply le_S_S.
            apply le_O_n*)
          ]
        ]
      | intro.
        apply eqb_elim
        [ intro.
          apply eqb_elim
          [ intro.
            apply False_ind.
            apply H6.
            apply eq_gcd_times_SO
            [ autobatch
              (*unfold lt.
              apply le_S_S.
              apply le_O_n*)
            | autobatch
              (*unfold lt.
              apply le_S_S.
              apply le_O_n*)
            | rewrite < gcd_mod
              [ autobatch
                (*rewrite > H4.
                rewrite > sym_gcd.
                assumption*)
              | autobatch
                (*unfold lt.
                apply le_S_S.
                apply le_O_n*)
              ]
            | rewrite < gcd_mod
              [ autobatch
                (*rewrite > H5.
                rewrite > sym_gcd.
                assumption*)
              | autobatch
                (*unfold lt.
                apply le_S_S.
                apply le_O_n*)
              ]
            ]
          | intro.
            reflexivity
          ]
        | intro.
          reflexivity
        ]
      ]
    ]
  ]
]
qed.