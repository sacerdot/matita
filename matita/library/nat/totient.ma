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

include "nat/chinese_reminder.ma".
include "nat/iteration2.ma".

(*a new definition of totient, which uses sigma_p instead of sigma *)
(*there's a little difference between this definition and the classic one:
  the classic definition of totient is:
   
    phi (n) is the number of naturals i (less or equal than n) so then gcd (i,n) = 1.
   (so this definition considers the values i=1,2,...,n)
  
  sigma_p doesn't work on the value n (but the first value it works on is (pred n))
  but works also on 0. That's not a problem, in fact
   - if n <> 1, gcd (n,0) <>1 and gcd (n,n) = n <> 1. 
   - if n = 1, then Phi(n) = 1, and (totient n), as defined below, returns 1. 
   
 *)
definition totient : nat \to nat \def
\lambda n.sigma_p n (\lambda m. eqb (gcd m n) (S O)) (\lambda m.S O).

lemma totient1: totient (S(S(S(S(S(S O)))))) = ?.
[|simplify.
                                
theorem totient_times: \forall n,m:nat. (gcd m n) = (S O) \to
totient (n*m) = (totient n)*(totient m).
intros.
unfold totient.
apply (nat_case1 n)
[ apply (nat_case1 m)
  [ intros.
    simplify.
    reflexivity
  | intros.
    simplify.
    reflexivity
  ]
| apply (nat_case1 m)
  [ intros.
    change in \vdash (? ? ? (? ? %)) with (O).
    rewrite > (sym_times (S m1) O).
    rewrite > sym_times in \vdash (? ? ? %).
    simplify.
    reflexivity  
  | intros.
    rewrite > H2 in H.
    rewrite > H1 in H.    
    apply (sigma_p_times m2 m1 ? ? ? 
            (\lambda b,a. cr_pair (S m2) (S m1) a b) 
            (\lambda x. x \mod (S m2)) (\lambda x. x \mod (S m1)))
   [intros.unfold cr_pair.
        apply (le_to_lt_to_lt ? (pred ((S m2)*(S m1))))
          [unfold min.
           apply transitive_le;
            [2: apply le_min_aux_r | skip | apply le_n]
          |unfold lt.
           apply (nat_case ((S m2)*(S m1)))
            [apply le_n|intro.apply le_n]
          ]
       |intros.
        generalize in match (mod_cr_pair (S m2) (S m1) a b H3 H4 H).
        intro.elim H5.
        apply H6
       |intros.
        generalize in match (mod_cr_pair (S m2) (S m1) a b H3 H4 H).
        intro.elim H5.
        apply H7
       |intros.
        generalize in match (mod_cr_pair (S m2) (S m1) a b H3 H4 H).
        intro.elim H5.
        apply eqb_elim
          [intro.
           rewrite > eq_to_eqb_true
             [rewrite > eq_to_eqb_true
               [reflexivity
               |rewrite < H6.
                rewrite > sym_gcd.
                rewrite > gcd_mod
                  [apply (gcd_times_SO_to_gcd_SO ? ? (S m1))
                    [unfold lt.apply le_S_S.apply le_O_n
                    |unfold lt.apply le_S_S.apply le_O_n
                    |assumption
                    ]
                  |unfold lt.apply le_S_S.apply le_O_n
                  ]
               ]           
            |rewrite < H7.
             rewrite > sym_gcd.
             rewrite > gcd_mod
               [apply (gcd_times_SO_to_gcd_SO ? ? (S m2))
                  [unfold lt.apply le_S_S.apply le_O_n
                  |unfold lt.apply le_S_S.apply le_O_n
                  |rewrite > sym_times.assumption
                  ]
               |unfold lt.apply le_S_S.apply le_O_n
               ]
            ]
          |intro.
           apply eqb_elim
           [intro.apply eqb_elim
              [intro.apply False_ind.
               apply H8.
               apply eq_gcd_times_SO
                 [unfold lt.apply le_S_S.apply le_O_n.
                 |unfold lt.apply le_S_S.apply le_O_n.
                 |rewrite < gcd_mod
                    [rewrite > H6.
                     rewrite > sym_gcd.assumption
                    |unfold lt.apply le_S_S.apply le_O_n
                    ]
                 |rewrite < gcd_mod
                    [rewrite > H7.
                     rewrite > sym_gcd.assumption
                    |unfold lt.apply le_S_S.apply le_O_n
                    ]
                 ]
              |intro.reflexivity
              ]
           |intro.reflexivity
           ]
         ]
       ]
     ]
   ]
qed.
