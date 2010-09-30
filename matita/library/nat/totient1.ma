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

include "nat/totient.ma".
include "nat/iteration2.ma".
include "nat/gcd_properties1.ma".

(* This file contains the proof of the following theorem about Euler's totient
 * function:
 
   The sum of the applications of Phi function over the divisor of a natural
   number n is equal to n
 *)

(*simple auxiliary properties*)   
theorem lt_O_to_divides_to_lt_O_div:
\forall a,b:nat.
O \lt b \to a \divides b \to O \lt (b/a).
intros.
apply (O_lt_times_to_O_lt ? a).
rewrite > (divides_to_div a b); 
  assumption.
qed.

(*tha main theorem*) 
theorem sigma_p_Sn_divides_b_totient_n: \forall n. O \lt n \to sigma_p (S n) (\lambda d.divides_b d n) totient = n.
intros. 
unfold totient.
apply (trans_eq ? ? 
(sigma_p (S n) (\lambda d:nat.divides_b d n)
(\lambda d:nat.sigma_p (S n) (\lambda m:nat.andb (leb (S m) d) (eqb (gcd m d) (S O))) (\lambda m:nat.S O))))
[ apply eq_sigma_p1
  [ intros.
    reflexivity
  | intros.
    apply sym_eq.
    apply (trans_eq ? ? 
     (sigma_p x (\lambda m:nat.leb (S m) x\land eqb (gcd m x) (S O)) (\lambda m:nat.S O)))
    [ apply false_to_eq_sigma_p
      [ apply lt_to_le.          
        assumption
      | intros.
        rewrite > lt_to_leb_false
        [ reflexivity
        | apply le_S_S.
          assumption
        ]
      ]
    | apply eq_sigma_p
      [ intros.
        rewrite > le_to_leb_true
        [ reflexivity
        | assumption
        ]
      | intros.
        reflexivity
      ]
    ]
  ]
| apply (trans_eq ? ? (sigma_p n (\lambda x.true) (\lambda x.S O)))
  [ apply sym_eq.
    apply (sigma_p_knm
     (\lambda x. (S O))
     (\lambda i,j.j*(n/i))
     (\lambda p. n / (gcd p n))
     (\lambda p. p / (gcd p n))
    );intros
    [ cut (O \lt (gcd x n))
      [split
      [ split
        [ split
          [ split
            [ apply divides_to_divides_b_true
              [ apply (O_lt_times_to_O_lt ? (gcd x n)).
                rewrite > (divides_to_div (gcd x n) n)
                [ assumption
                | apply (divides_gcd_m)
                ]
              | rewrite > sym_gcd.
                apply (divides_times_to_divides_div_gcd).
                apply (witness n (x * n) x).
                apply (symmetric_times x n)
              ]
            | apply (true_to_true_to_andb_true)
              [ apply (le_to_leb_true).
                change with (x/(gcd x n) \lt n/(gcd x n)).
                apply (lt_times_n_to_lt (gcd x n) ? ?)
                [ assumption
                | rewrite > (divides_to_div (gcd x n) x)
                  [ rewrite > (divides_to_div (gcd x n) n)
                    [ assumption
                    | apply divides_gcd_m
                    ]
                  | apply divides_gcd_n
                  ]
                ]
              | apply eq_to_eqb_true.
                rewrite > (eq_gcd_div_div_div_gcd x n (gcd x n))
                [ apply (div_n_n (gcd x n) Hcut)
                | assumption
                | apply divides_gcd_n
                | apply divides_gcd_m                  
                ]
              ]
            ] 
          | apply (inj_times_l1 (n/(gcd x n)))
            [ apply lt_O_to_divides_to_lt_O_div
              [ assumption
              | apply divides_gcd_m 
              ]
            | rewrite > associative_times.
              rewrite > (divides_to_div (n/(gcd x n)) n)
              [ rewrite > sym_times.
                rewrite > (divides_to_eq_times_div_div_times x)
                [ apply (inj_times_l1 (gcd x n) Hcut).
                  rewrite > (divides_to_div (gcd x n) (x * n))
                  [ rewrite > assoc_times.
                    rewrite > (divides_to_div (gcd x n) x)
                    [ apply sym_times
                    | apply divides_gcd_n
                    ]
                  | apply (trans_divides ? x)
                    [ apply divides_gcd_n
                    | apply (witness ? ? n).
                      reflexivity
                    ]
                  ]
                | assumption
                | apply divides_gcd_m
                ]              
              | apply (witness ? ? (gcd x n)).
                rewrite > divides_to_div
                [ reflexivity
                | apply divides_gcd_m                
                ]                
              ]
            ]  
          ]
        | apply (le_to_lt_to_lt ? n)
          [ apply le_div.
            assumption
          | change with ((S n) \le (S n)).
            apply le_n 
          ]
        ]
      | apply (le_to_lt_to_lt ? x)
        [ apply le_div.
          assumption   
        | apply (trans_lt ? n ?)
          [ assumption
          | change with ((S n) \le (S n)).
            apply le_n
          ]
        ]
      ]
    | apply (divides_to_lt_O ? n)
      [ assumption
      | apply divides_gcd_m
      ]
    ]  
    | cut (i \divides n)
      [ cut (j \lt i)
        [ cut ((gcd j i) = (S O) )
          [ cut ((gcd (j*(n/i)) n) = n/i)
            [ split
              [ split
                [ split
                  [ reflexivity
                  | rewrite > Hcut3.
                    apply (div_div);
                      assumption
                  ]               
                | rewrite > Hcut3.
                  rewrite < divides_to_eq_times_div_div_times
                  [ rewrite > div_n_n  
                    [ apply sym_eq.
                      apply times_n_SO.
                    | apply lt_O_to_divides_to_lt_O_div;
                        assumption
                    ]
                  | apply lt_O_to_divides_to_lt_O_div; 
                      assumption
                  | apply divides_n_n
                  ]
                ]
              | rewrite < (divides_to_div i n) in \vdash (? ? %)
                [ rewrite > sym_times.
                  apply (lt_times_r1)
                  [ apply lt_O_to_divides_to_lt_O_div;
                      assumption
                  | assumption
                  ]
                | assumption
                ]               
              ]
            | rewrite < (divides_to_div i n) in \vdash (? ? (? ? %) ?)
              [ rewrite > (sym_times j).
                rewrite > times_n_SO in \vdash (? ? ? %).
                rewrite < Hcut2.
                apply eq_gcd_times_times_times_gcd                
              | assumption
              ]
            ]
          | apply eqb_true_to_eq.
            apply (andb_true_true_r (leb (S j) i)).            
            assumption            
          ]
        | change with ((S j) \le i).
          cut((leb (S j) i) = true)
          [ change with(
            match (true) with
            [ true  \Rightarrow ((S j) \leq i) 
            | false \Rightarrow ((S j) \nleq i)]
            ).
            rewrite < Hcut1.
            apply (leb_to_Prop)
          | apply (andb_true_true (leb (S j) i) (eqb (gcd j i) (S O))).            
            assumption
          ]
        ]
        | apply (divides_b_true_to_divides).
          assumption
      ]
    ]
  | apply (sigma_p_true).
  ]
]
qed.  
    
   
