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

set "baseuri" "cic:/matita/nat/totient1".

include "nat/totient.ma".
include "nat/iteration2.ma".
include "nat/propr_div_mod_lt_le_totient1_aux.ma".
include "nat/gcd_properties1.ma".

(* This file contains the proof of the following theorem about Euler's totient
 * function:
 
   The sum of the applications of Phi function over the divisor of a natural
   number n is equal to n
 *)
  
(*two easy properties of gcd, directly obtainable from the more general theorem 
  eq_gcd_times_times_eqv_times_gcd*)

theorem gcd_bTIMESd_aTIMESd_eq_d_to_gcd_a_b_eq_SO:\forall a,b,d:nat.
O \lt d \to O \lt b \to gcd (b*d) (a*d) = d \to (gcd a b) = (S O).
intros.
apply (inj_times_r1 d)
[ assumption
| rewrite < (times_n_SO d).
  rewrite < (eq_gcd_times_times_eqv_times_gcd a b d).
  rewrite > sym_gcd.
  rewrite > (sym_times d a).
  rewrite > (sym_times d b).
  assumption
]
qed.

theorem gcd_SO_to_gcd_times: \forall a,b,c:nat.
O \lt c \to (gcd a b) = (S O) \to (gcd (a*c) (b*c)) = c.
intros.
rewrite > (sym_times a c).
rewrite > (sym_times b c).
rewrite > (eq_gcd_times_times_eqv_times_gcd a b c).
rewrite > H1.
apply sym_eq.
apply times_n_SO.
qed.


(* The proofs of the 6 sub-goals activated after the application of the theorem 
   eq_sigma_p_gh in the proof of the main theorem
 *)
 


(* 2nd*)
theorem sum_divisor_totient1_aux2: \forall i,n:nat.
(S O) \lt n \to i<n*n \to 
  (i/n) \divides (pred n) \to
  (i \mod n) \lt (i/n) \to
  (gcd (i \mod n) (i/n)) = (S O) \to
     gcd (pred n) ((i\mod n)* (pred n)/(i/n)) = (pred n) / (i/n).             
intros.
cut (O \lt (pred n))
[ cut(O \lt (i/n))
  [ rewrite < (NdivM_times_M_to_N (pred n) (i/n)) in \vdash (? ? (? % ?) ?)
    [ rewrite > (sym_times ((pred n)/(i/n)) (i/n)).
      cut ((i \mod n)*(pred n)/(i/n) = (i \mod n) * ((pred n) / (i/n)))
      [ rewrite > Hcut2.
        apply (gcd_SO_to_gcd_times (i/n) (i \mod n) ((pred n)/(i/n)))
        [ apply (lt_O_a_lt_O_b_a_divides_b_to_lt_O_aDIVb (i/n) (pred n));
            assumption
        | rewrite > sym_gcd.
          assumption            
        ]
      | apply sym_eq.
        apply (separazioneFattoriSuDivisione (i \mod n) (pred n) (i/n));
          assumption.
      ]           
    | assumption
    | assumption
    ]
  | apply (divides_to_lt_O (i/n) (pred n));
      assumption
  ]        
| apply n_gt_Uno_to_O_lt_pred_n.
  assumption.
]
qed.


(*3rd*)
theorem aux_S_i_mod_n_le_i_div_n: \forall i,n:nat.
i < n*n \to (divides_b (i/n) (pred n) \land
            (leb (S(i\mod n)) (i/n) \land
            eqb (gcd (i\mod n) (i/n)) (S O))) =true         
         \to
         (S (i\mod n)) \le (i/n).
intros.         
cut (leb (S (i \mod n)) (i/n) = true)
[ change with (
  match (true) with
  [ true  \Rightarrow (S (i \mod n)) \leq (i/n) 
  | false \Rightarrow (S (i \mod n)) \nleq (i/n)]
  ).
  rewrite < Hcut.  
  apply (leb_to_Prop (S(i \mod n)) (i/n))
| apply (andb_true_true (leb (S(i\mod n)) (i/n)) (divides_b (i/n) (pred n))  ).
  apply (andb_true_true ((leb (S(i\mod n)) (i/n)) \land (divides_b (i/n) (pred n)))
    (eqb (gcd (i\mod n) (i/n)) (S O))
  ).
  rewrite > andb_sym in \vdash (? ? (? % ?) ?).
  rewrite < (andb_assoc) in \vdash (? ? % ?).
  assumption
]
qed.


(*the following theorem is just a particular case of the theorem
  divides_times, prooved in primes.ma
 *)
theorem a_divides_b_to_a_divides_b_times_c: \forall a,b,c:nat.
a \divides b \to a \divides (b*c).
intros.
rewrite > (times_n_SO a).
apply (divides_times).
assumption.
apply divides_SO_n.
qed.

theorem sum_divisor_totient1_aux_3: \forall i,n:nat.
i < n*n \to 
  (divides_b (i/n) (pred n)
\land (leb (S(i\mod n)) (i/n)
\land eqb (gcd (i\mod n) (i/n)) (S O)))
       =true
   \to i\mod n*pred n/(i/n)<(pred n).
intros.
apply (lt_to_le_to_lt ((i \mod n)*(pred n) / (i/n)) 
                ((i/n)*(pred n) / (i/n))
                 (pred n))               
[ apply (lt_times_n_to_lt (i/n) ((i\mod n)*(pred n)/(i/n)) ((i/n)*(pred n)/(i/n)))    
  [ apply (Sa_le_b_to_O_lt_b (i \mod n) (i/n)).
    apply (aux_S_i_mod_n_le_i_div_n i n);
      assumption.  
  | rewrite > (NdivM_times_M_to_N )
    [ rewrite > (NdivM_times_M_to_N ) in \vdash (? ? %)
      [ apply (monotonic_lt_times_variant (pred n)) 
        [ apply (nat_case1 n)
          [ intros.
            rewrite > H2 in H:(? ? %).
            change in H:(? ? %) with (O).
            change in H:(%) with ((S i) \le O).
            apply False_ind.
            apply (not_le_Sn_O i H)  
          | intro.
            elim m
            [ rewrite > H2 in H1:(%).
              rewrite > H2 in H:(%).
              simplify in H.
              cut (i = O)
              [ rewrite > Hcut in H1:(%).
                simplify in H1.  
                apply False_ind.  
                apply (not_eq_true_false H1)
              | change in H:(%) with((S i) \le (S O)).
                cut (i \le O )
                [ apply (nat_case1 i)
                  [ intros.
                    reflexivity
                  | intros.
                    rewrite > H3 in Hcut:(%).
                    apply False_ind.
                    apply (not_le_Sn_O m1 Hcut)
                  ]
                | apply (le_S_S_to_le i O).
                  assumption
                ]
              ]
            | change with ((S O) \le (S n1)).
              apply (le_S_S O n1).
              apply (le_O_n n1)
            ]
          ]
        | change with ((S (i\mod n)) \le (i/n)).          
          apply (aux_S_i_mod_n_le_i_div_n i n);
            assumption    
        ]
      | apply (Sa_le_b_to_O_lt_b (i \mod n) (i/n)).
        apply (aux_S_i_mod_n_le_i_div_n i n);
          assumption
      | rewrite > (times_n_SO (i/n)) in \vdash (? % ?).
        apply (divides_times).
        apply divides_n_n.  
        apply divides_SO_n    
      ]
    | apply (Sa_le_b_to_O_lt_b (i \mod n) (i/n)).
      apply (aux_S_i_mod_n_le_i_div_n i n);
        assumption
    | rewrite > (times_n_SO (i/n)).
      rewrite > (sym_times (i \mod n) (pred n)).
      apply (divides_times)
      [ apply divides_b_true_to_divides.
        apply (andb_true_true (divides_b (i/n) (pred n)) (leb (S (i\mod n)) (i/n))). 
        apply (andb_true_true 
            ((divides_b (i/n) (pred n)) \land (leb (S (i\mod n)) (i/n)))  
            (eqb (gcd (i\mod n) (i/n)) (S O))).
        rewrite < (andb_assoc) in \vdash (? ? % ?).
        assumption
      | apply divides_SO_n
      ]
    ]
  ]
| rewrite > (sym_times).
  rewrite > (div_times_ltO )  
  [ apply (le_n (pred n)).
    
  | apply (Sa_le_b_to_O_lt_b (i \mod n) (i/n)).
    apply (aux_S_i_mod_n_le_i_div_n i n);
      assumption.
  ]    
]qed.


(*4th*)
theorem sum_divisor_totient1_aux_4: \forall j,n:nat.
j \lt (pred n) \to (S O) \lt n \to
((divides_b ((pred n/gcd (pred n) j*n+j/gcd (pred n) j)/n) (pred n))
 \land ((leb (S ((pred n/gcd (pred n) j*n+j/gcd (pred n) j)\mod n))
        ((pred n/gcd (pred n) j*n+j/gcd (pred n) j)/n))
        \land (eqb
              (gcd ((pred n/gcd (pred n) j*n+j/gcd (pred n) j)\mod n)
               ((pred n/gcd (pred n) j*n+j/gcd (pred n) j)/n)) (S O))))
=true.
intros.
cut (O \lt (pred n))
[ cut ( O \lt (gcd (pred n) j))
  [ cut (j/(gcd (pred n) j) \lt n)
    [ cut (((pred n/gcd (pred n) j*n+j/gcd (pred n) j)/n) = pred n/gcd (pred n) j)
      [ cut (((pred n/gcd (pred n) j*n+j/gcd (pred n) j) \mod n) = j/gcd (pred n) j)
        [ rewrite > Hcut3.
          rewrite > Hcut4.
          apply andb_t_t_t
          [ apply divides_to_divides_b_true
            [ apply (lt_times_n_to_lt  (gcd (pred n) j) O (pred n/gcd (pred n) j))
              [ assumption
              | rewrite > (sym_times O (gcd (pred n) j)).
                rewrite < (times_n_O (gcd (pred n) j)).
                rewrite > (NdivM_times_M_to_N (pred n) (gcd (pred n) j))
                [ assumption
                | assumption
                | apply (divides_gcd_n (pred n))
                ]
              ]
            | apply (witness (pred n/(gcd (pred n) j))  (pred n) (gcd (pred n) j)).
              rewrite > (NdivM_times_M_to_N (pred n) (gcd (pred n) j))
              [ reflexivity
              | assumption
              | apply (divides_gcd_n (pred n))
              ]
            ]
          | apply (le_to_leb_true).
            apply lt_S_to_le.
            apply cic:/matita/algebra/finite_groups/lt_S_S.con.
            apply (lt_times_n_to_lt (gcd (pred n) j) ? ?)
            [ assumption
            | rewrite > (NdivM_times_M_to_N j (gcd (pred n) j))
              [ rewrite > (NdivM_times_M_to_N (pred n) (gcd (pred n) j))
                [ assumption
                | assumption
                | apply divides_gcd_n
                ]
              | assumption
              | rewrite > sym_gcd.
                apply divides_gcd_n
              ]
            ]
          | apply cic:/matita/nat/compare/eq_to_eqb_true.con.
            apply (gcd_bTIMESd_aTIMESd_eq_d_to_gcd_a_b_eq_SO ? ? (gcd (pred n) j))
            [ assumption
            | apply (lt_times_n_to_lt (gcd (pred n) j) ? ?)
              [ assumption
              | simplify.
                rewrite > NdivM_times_M_to_N
                [ assumption
                | assumption
                | apply divides_gcd_n
                ]
              ]
            | rewrite > NdivM_times_M_to_N
              [ rewrite > (NdivM_times_M_to_N j (gcd (pred n) j))
                [ reflexivity            
                | assumption
                | rewrite > sym_gcd.
                  apply divides_gcd_n
                ]            
              | assumption
              | apply divides_gcd_n
              ]
            ]
          ]
        | apply (mod_plus_times).
          assumption
        ]
      | apply (div_plus_times).
        assumption
      ]
    | apply (lt_times_n_to_lt (gcd (pred n) j) ? ?)
      [ assumption
      | rewrite > NdivM_times_M_to_N
        [ apply (lt_to_le_to_lt j (pred n) ?)
          [ assumption
          | apply (lt_to_le).
            apply (lt_to_le_to_lt ? n ?)
            [ change with ((S (pred n)) \le n).
              rewrite < (S_pred n)
              [ apply le_n
              | apply (trans_lt ? (S O)  ?)
                [ change with ((S O) \le (S O)).
                  apply (le_n (S O))
                | assumption
                ]                
              ]
            | rewrite > (times_n_SO n) in \vdash (? % ?).
              apply (le_times n)
              [ apply (le_n n)
              | change with (O \lt (gcd (pred n) j)).
                assumption
              ]
            ]
          ]
        | assumption
        | rewrite > sym_gcd.
          apply (divides_gcd_n)
        ]
      ]
    ]
  | rewrite > sym_gcd.
    apply (lt_O_gcd).
    assumption
  ]
| apply n_gt_Uno_to_O_lt_pred_n.
  assumption
]
qed.




(*5th*)
theorem sum_divisor_totient1_aux5: \forall a,b,c:nat.
O \lt c \to O \lt b \to a \lt c \to b \divides a \to b \divides c \to
a / b * c / (c/b) = a.
intros.
elim H3.
elim H4.
cut (O \lt n)
[ rewrite > H6 in \vdash (? ? (? ? %) ?).
  rewrite > sym_times in \vdash (? ? (? ? %) ?).
  rewrite > (div_times_ltO n b)
  [ cut (n \divides c)
    [ cut (a/b * c /n = a/b * (c/n))
      [ rewrite > Hcut2.
        cut (c/n = b)
        [ rewrite > Hcut3.
          apply (NdivM_times_M_to_N a b);
            assumption
        | rewrite > H6.
          apply (div_times_ltO b n).
          assumption
        ]
      | elim Hcut1.
        rewrite > H7.
        rewrite < assoc_times in \vdash (? ? (? % ?) ?).
        rewrite > (sym_times ((a/b)*n) n1).
        rewrite < (assoc_times n1 (a/b) n).
        rewrite > (div_times_ltO (n1*(a/b)) n)
        [ rewrite > (sym_times n n1).
          rewrite > (div_times_ltO n1 n)
          [ rewrite > (sym_times (a/b) n1).
            reflexivity
          | assumption
          ]
        | assumption
        ]
      ]
    | apply (witness n c b).
      rewrite > (sym_times n b).
      assumption
    ]
  | assumption
  ]
| apply (nat_case1 n)
  [ intros.
    rewrite > H7 in H6.
    rewrite > sym_times in H6.
    simplify in H6.
    rewrite > H6 in H.
    apply False_ind.
    change in H with ((S O) \le O).
    apply (not_le_Sn_O O H)
  | intros.
    apply (lt_O_S m)
  ]
]
qed.

  


(*6th*)
theorem sum_divisor_totient1_aux_6: \forall j,n:nat.
j \lt (pred n) \to (S O) \lt n \to ((pred n)/(gcd (pred n) j))*n+j/(gcd (pred n) j)<n*n.
intros.
apply (nat_case1 n)
[ intros.
  rewrite > H2 in H.
  apply False_ind.
  apply (not_le_Sn_O j H)
| intros.
  rewrite < (pred_Sn m).
  rewrite < (times_n_Sm (S m) m).
  rewrite > (sym_plus (S m) ((S m) * m)).
  apply le_to_lt_to_plus_lt
  [ rewrite > (sym_times (S m) m).
    apply le_times_l.
    apply (lt_to_divides_to_div_le)
    [ apply (nat_case1 m)
      [ intros.
        rewrite > H3 in H2.
        rewrite > H2 in H1.
        apply False_ind.
        apply (le_to_not_lt (S O) (S O))
        [ apply le_n
        | assumption
        ]
      | intros.
        rewrite > sym_gcd in \vdash (? ? %).
        apply (lt_O_gcd j (S m1)).
        apply (lt_O_S m1)       
      ]
    | apply divides_gcd_n
    ]
  | apply (le_to_lt_to_lt (j / (gcd m j)) j (S m))
    [
      apply lt_to_divides_to_div_le
      [ apply (nat_case1 m)
        [ intros.
          rewrite > H3 in H2.
          rewrite > H2 in H1.
          apply False_ind.
          apply (le_to_not_lt (S O) (S O))
          [ apply le_n
          | assumption
          ]
        | intros.
          rewrite > sym_gcd in \vdash (? ? %).
          apply (lt_O_gcd j (S m1)).
          apply (lt_O_S m1)
        ]
      | rewrite > sym_gcd in \vdash (? % ?).
        apply divides_gcd_n
      ]
    | rewrite > H2 in H.
      rewrite < (pred_Sn m) in H.
      apply (trans_lt j m (S m))
      [ assumption.
      | change with ((S m) \le (S m)).
        apply (le_n (S m)) 
      ]
    ]
  ]
]
qed.



    
(* The main theorem, adding the hypotesis n > 1 (the cases n= 0
   and n = 1 are dealed as particular cases in theorem 
   sum_divisor_totiet)
 *)        
theorem sum_divisor_totient1: \forall n. (S O) \lt n \to sigma_p n (\lambda d.divides_b d (pred n)) totient = (pred n).
intros. 
unfold totient.
apply (trans_eq ? ? 
(sigma_p n (\lambda d:nat.divides_b d (pred n))
(\lambda d:nat.sigma_p n (\lambda m:nat.andb (leb (S m) d) (eqb (gcd m d) (S O))) (\lambda m:nat.S O))))
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
  | rewrite < (sigma_p2' n n 
               (\lambda d:nat.divides_b d (pred n))
               (\lambda d,m:nat.leb (S m) d\land eqb (gcd m d) (S O))
               (\lambda x,y.(S O))).   
    apply (trans_eq ? ? (sigma_p (pred n) (\lambda x.true) (\lambda x.S O)))
    [ apply (eq_sigma_p_gh
      (\lambda x:nat. (S O))
      (\lambda i:nat. (((i \mod n)*(pred n)) / (i / n) )  )    
      (\lambda j:nat. (((pred n)/(gcd (pred n) j))*n + (j / (gcd (pred n) j))) )
      (n*n)
      (pred n)
      (\lambda x:nat. 
        divides_b (x/n) (pred n) 
        \land (leb (S (x \mod n)) (x/n)
        \land eqb (gcd (x \mod n) (x/n)) (S O)))
      (\lambda x:nat.true)
      )    
      [ intros.
        reflexivity
      | intros.
        cut ((i/n) \divides (pred n))
        [ cut ((i \mod n ) \lt (i/n))
          [ cut ((gcd (i \mod n) (i / n)) = (S O)) 
            [ cut ((gcd (pred n) ((i \mod n)*(pred n)/ (i/n)) = (pred n) / (i/n)))
              [ rewrite > Hcut3.
                cut ((i \mod n) * (pred n)/(i/n)/((pred n)/(i/n)) = (i \mod n))
                [ rewrite > Hcut4.
                  cut ((pred n)/ ((pred n)/(i/n)) = (i/n))
                  [ rewrite > Hcut5.
                    apply sym_eq.
                    apply div_mod.
                    apply (trans_lt O (S O) n)
                    [ apply (lt_O_S O)
                    | assumption
                    ]
                  | elim Hcut.
                    rewrite > H3 in \vdash (? ? (? ? (? % ?)) ?).
                    rewrite > sym_times in \vdash (? ? (? ? (? % ?)) ?).
                    rewrite > (div_times_ltO n2 (i/n))
                    [ rewrite > H3.
                      apply div_times_ltO.
                      apply (divides_to_lt_O n2 (pred n))
                      [ apply (n_gt_Uno_to_O_lt_pred_n n).
                        assumption
                      | apply (witness n2 (pred n) (i/n)).
                        rewrite > sym_times.
                        assumption
                      ]
                    | apply (divides_to_lt_O (i/n) (pred n))
                      [ apply (n_gt_Uno_to_O_lt_pred_n n).
                        assumption
                      | apply (witness (i/n) (pred n) n2).
                        assumption                                
                      ]
                    ]
                  ]
                | elim Hcut.
                  cut (( i \mod n * (pred n)/(i/n)) = ( i\mod n * ((pred n)/(i/n))))
                  [ rewrite > Hcut4.
                    rewrite > H3.
                    rewrite < (sym_times n2 (i/n)).
                    rewrite > (div_times_ltO n2 (i/n))
                    [ rewrite > (div_times_ltO (i \mod n) n2)
                      [ reflexivity                     
                      | apply (divides_to_lt_O n2 (pred n))
                        [ apply (n_gt_Uno_to_O_lt_pred_n n).
                          assumption                      
                        | apply (witness n2 (pred n) (i/n)).
                          rewrite > sym_times.
                          assumption
                        ]
                      ]
                    | apply (divides_to_lt_O (i/n) (pred n))
                      [ apply (n_gt_Uno_to_O_lt_pred_n n).
                        assumption
                      | assumption
                      ]
                    ]
                  | apply (sym_eq).
                    apply (separazioneFattoriSuDivisione (i \mod n) (pred n) (i/n))
                    [ apply (n_gt_Uno_to_O_lt_pred_n n).
                      assumption
                    | assumption       
                    ]
                  ]
                ]
              | apply (sum_divisor_totient1_aux2);
                assumption
              ]
            | apply (eqb_true_to_eq (gcd (i \mod n) (i/n)) (S O)).    
              apply (andb_true_true 
              (eqb (gcd (i\mod n) (i/n)) (S O))
              (leb (S (i\mod n)) (i/n))
              ).
              apply (andb_true_true          
               ((eqb (gcd (i\mod n) (i/n)) (S O)) 
                \land 
                (leb (S (i\mod n)) (i/n)))
                     (divides_b (i/n) (pred n))
              ).
              rewrite > andb_sym.
              rewrite > andb_sym in \vdash (? ? (? ? %) ?).
              assumption
            ]
          | change with (S (i \mod n) \le (i/n)).
            cut (leb (S (i \mod n)) (i/n) = true)
            [ change with (
                match (true) with
                [ true  \Rightarrow (S (i \mod n)) \leq (i/n) 
                | false \Rightarrow (S (i \mod n)) \nleq (i/n)]
              ).
              rewrite < Hcut1.  
              apply (leb_to_Prop (S(i \mod n)) (i/n))
            | apply (andb_true_true (leb (S(i\mod n)) (i/n)) (divides_b (i/n) (pred n))  ).
              apply (andb_true_true ((leb (S(i\mod n)) (i/n)) \land (divides_b (i/n) (pred n)))
                (eqb (gcd (i\mod n) (i/n)) (S O))
              ).
              rewrite > andb_sym in \vdash (? ? (? % ?) ?).
              rewrite < (andb_assoc) in \vdash (? ? % ?).
              assumption
            ]
          ]
        | apply (divides_b_true_to_divides ).                   
          apply (andb_true_true (divides_b (i/n) (pred n))
                          (leb (S (i\mod n)) (i/n))).
          apply (andb_true_true ( (divides_b (i/n) (pred n)) \land  (leb (S (i\mod n)) (i/n)) )
            (eqb (gcd (i\mod n) (i/n)) (S O))
          ).
          rewrite < andb_assoc.
          assumption.
        ]
      | intros.
        apply (sum_divisor_totient1_aux_3);
          assumption.        
      | intros.
        apply (sum_divisor_totient1_aux_4);
          assumption.
      | intros.
        cut (j/(gcd (pred n) j) \lt n)
        [ rewrite > (div_plus_times n (pred n/gcd (pred n) j) (j/gcd (pred n) j))
          [ rewrite > (mod_plus_times n (pred n/gcd (pred n) j) (j/gcd (pred n) j))
            [ apply (sum_divisor_totient1_aux5 j (gcd (pred n) j) (pred n))
              [ apply (n_gt_Uno_to_O_lt_pred_n n).
                assumption
              | rewrite > sym_gcd.
                apply lt_O_gcd.  
                apply (n_gt_Uno_to_O_lt_pred_n n).
                assumption
              | assumption
              | apply divides_gcd_m
              | rewrite > sym_gcd.
                apply divides_gcd_m
              ]
            | assumption
            ]
          | assumption
          ]
        | apply (le_to_lt_to_lt (j/gcd (pred n) j) j n)
          [ apply (lt_to_divides_to_div_le)
            [ rewrite > sym_gcd.
              apply lt_O_gcd.
              apply (n_gt_Uno_to_O_lt_pred_n n).
              assumption
            | apply divides_gcd_m
            ]
          | apply (lt_to_le_to_lt j (pred n) n)
            [ assumption
            | apply le_pred_n
            ]
          ]
        ]
      | intros.
        apply (sum_divisor_totient1_aux_6);
          assumption.
      ]
    | apply (sigma_p_true).
    ]
  ]
qed.


(*there's a little difference between the following definition of the
  theorem, and the abstract definition given before.
  in fact (sigma_p n f p) works on (pred n), and not on n, as first element.
  that's why in the definition of the theorem the summary is set equal to 
  (pred n).
 *)
theorem sum_divisor_totient: \forall n.
sigma_p n (\lambda d.divides_b d (pred n)) totient = (pred n).
intros.
apply (nat_case1 n)
[ intros.
  simplify.
  reflexivity
| intros.
  apply (nat_case1 m)
  [ intros.
    simplify.
    reflexivity
  | intros.
    rewrite < H1.
    rewrite < H.
    rewrite > (pred_Sn m).
    rewrite < H.
    apply( sum_divisor_totient1).
    rewrite > H.
    rewrite > H1.
    apply cic:/matita/algebra/finite_groups/lt_S_S.con.
    apply lt_O_S
  ]
]
qed.


















