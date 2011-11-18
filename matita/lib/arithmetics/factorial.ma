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

include "arithmetics/exp.ma".

let rec fact n ≝
  match n with 
  [ O ⇒ 1
  | S m ⇒ fact m * S m].

interpretation "factorial" 'fact n = (fact n).

theorem le_1_fact : ∀n. 1 ≤ n!.
#n (elim n) normalize /2/ 
qed.

theorem le_2_fact : ∀n. 1 < n → 2 ≤ n!.
#n (cases n)
  [#abs @False_ind /2/
  |#m normalize #le2 @(le_times 1 ? 2) //
  ]
qed.

theorem le_n_fact_n: ∀n. n ≤ n!.
#n (elim n) normalize //
#n #Hind @(transitive_le ? (1*(S n))) // @le_times //
qed.

theorem lt_n_fact_n: ∀n. 2 < n → n < n!.
#n (cases n) 
  [#H @False_ind /2/ 
  |#m #lt2 normalize @(lt_to_le_to_lt ? (2*(S m))) //
   @le_times // @le_2_fact /2/ 
qed.

(* approximations *)

theorem fact_to_exp1: ∀n.O<n →
 (2*n)! ≤ (2^(pred (2*n))) * n! * n!.
#n #posn (cut (∀i.2*(S i) = S(S(2*i)))) [//] #H (elim posn) //
#n #posn #Hind @(transitive_le ? ((2*n)!*(2*(S n))*(2*(S n))))
  [>H normalize @le_times //
  |cut (pred (2*(S n)) = S(S(pred(2*n))))
    [>S_pred // @(le_times 1 ? 1) //] #H1
   cut (2^(pred (2*(S n))) = 2^(pred(2*n))*2*2) 
    [>H1 >H1 //] #H2 >H2
   @(transitive_le ? ((2^(pred (2*n))) * n! * n! *(2*(S n))*(2*(S n))))
    [@le_times[@le_times //]//
    (* we generalize to hide the computational content *)
    |normalize {match ((S n)!)} generalize {match (S n)}
     #Sn generalize {match 2} #two //
    ]
  ]
qed.  

theorem fact_to_exp: ∀n.
 (2*n)! ≤ (2^(pred (2*n))) * n! * n!.
#n (cases n) [normalize // |#n @fact_to_exp1 //]
qed.

theorem exp_to_fact1: ∀n.O < n →
  2^(2*n)*n!*n! < (S(2*n))!.
#n #posn (elim posn) [normalize //]
#n #posn #Hind (cut (∀i.2*(S i) = S(S(2*i)))) [//] #H
cut (2^(2*(S n)) = 2^(2*n)*2*2) [>H //] #H1 >H1
@(le_to_lt_to_lt ? (2^(2*n)*n!*n!*(2*(S n))*(2*(S n))))
  [normalize {match ((S n)!)} generalize {match (S n)} #Sn
   generalize {match 2} #two //
  |cut ((S(2*(S n)))! = (S(2*n))!*(S(S(2*n)))*(S(S(S(2*n)))))
   [>H //] #H2 >H2 @lt_to_le_to_lt_times
     [@lt_to_le_to_lt_times //|>H // | //]
  ]
qed.
     
(* a slightly better result 
theorem fact3: \forall n.O < n \to
(exp 2 (2*n))*(exp (fact n) 2) \le 2*n*fact (2*n).
intros.
elim H
  [simplify.apply le_n
  |rewrite > times_SSO.
   rewrite > factS.
   rewrite < times_exp.
   change in ⊢ (? (? % ?) ?) with ((S(S O))*((S(S O))*(exp (S(S O)) ((S(S O))*n1)))).
   rewrite > assoc_times.
   rewrite > assoc_times in ⊢ (? (? ? %) ?).
   rewrite < assoc_times in ⊢ (? (? ? (? ? %)) ?).
   rewrite < sym_times in ⊢ (? (? ? (? ? (? % ?))) ?).
   rewrite > assoc_times in ⊢ (? (? ? (? ? %)) ?).
   apply (trans_le ? (((S(S O))*((S(S O))*((S n1)\sup((S(S O)))*((S(S O))*n1*((S(S O))*n1)!))))))
    [apply le_times_r.
     apply le_times_r.
     apply le_times_r.
     assumption
    |rewrite > factS.
     rewrite > factS.
     rewrite < times_SSO.
     rewrite > assoc_times in ⊢ (? ? %). 
     apply le_times_r.
     rewrite < assoc_times.
     change in ⊢ (? (? (? ? %) ?) ?) with ((S n1)*((S n1)*(S O))).
     rewrite < assoc_times in ⊢ (? (? % ?) ?).
     rewrite < times_n_SO.
     rewrite > sym_times in ⊢ (? (? (? % ?) ?) ?).
     rewrite < assoc_times in ⊢ (? ? %).
     rewrite < assoc_times in ⊢ (? ? (? % ?)).
     apply le_times_r.
     apply le_times_l.
     apply le_S.apply le_n
    ]
  ]
qed.

theorem le_fact_10: fact (2*5) \le (exp 2 ((2*5)-2))*(fact 5)*(fact 5).
simplify in \vdash (? (? %) ?).
rewrite > factS in \vdash (? % ?).
rewrite > factS in \vdash (? % ?).rewrite < assoc_times in \vdash(? % ?).
rewrite > factS in \vdash (? % ?).rewrite < assoc_times in \vdash (? % ?).
rewrite > factS in \vdash (? % ?).rewrite < assoc_times in \vdash (? % ?).
rewrite > factS in \vdash (? % ?).rewrite < assoc_times in \vdash (? % ?).
apply le_times_l.
apply leb_true_to_le.reflexivity.
qed.

theorem ab_times_cd: \forall a,b,c,d.(a*b)*(c*d)=(a*c)*(b*d).
intros.
rewrite > assoc_times.
rewrite > assoc_times.
apply eq_f.
rewrite < assoc_times.
rewrite < assoc_times.
rewrite > sym_times in \vdash (? ? (? % ?) ?).
reflexivity.
qed.

(* an even better result *)
theorem lt_SSSSO_to_fact: \forall n.4<n \to
fact (2*n) \le (exp 2 ((2*n)-2))*(fact n)*(fact n).
intros.elim H
  [apply le_fact_10
  |rewrite > times_SSO.
   change in \vdash (? ? (? (? (? ? %) ?) ?)) with (2*n1 - O);
   rewrite < minus_n_O.
   rewrite > factS.
   rewrite > factS.
   rewrite < assoc_times.
   rewrite > factS.
   apply (trans_le ? ((2*(S n1))*(2*(S n1))*(fact (2*n1))))
    [apply le_times_l.
     rewrite > times_SSO.
     apply le_times_r.
     apply le_n_Sn
    |apply (trans_le ? (2*S n1*(2*S n1)*(2\sup(2*n1-2)*n1!*n1!)))
      [apply le_times_r.assumption
      |rewrite > assoc_times.
       rewrite > ab_times_cd in \vdash (? (? ? %) ?).
       rewrite < assoc_times.
       apply le_times_l.
       rewrite < assoc_times in \vdash (? (? ? %) ?).
       rewrite > ab_times_cd.
       apply le_times_l.
       rewrite < exp_S.
       rewrite < exp_S.
       apply le_exp
        [apply lt_O_S
        |rewrite > eq_minus_S_pred.
         rewrite < S_pred
          [rewrite > eq_minus_S_pred.
           rewrite < S_pred
            [rewrite < minus_n_O.
             apply le_n
            |elim H1;simplify
              [apply lt_O_S
              |apply lt_O_S
              ]
            ]
          |elim H1;simplify
            [apply lt_O_S
            |rewrite < plus_n_Sm.
             rewrite < minus_n_O.
             apply lt_O_S
            ]
          ]
        ]
      ]
    ]
  ]
qed. *)
