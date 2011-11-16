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

include "arithmetics/sigma_pi.ma".
include "arithmetics/primes.ma".

(* binomial coefficient *)
definition bc ≝ λn,k. n!/(k!*(n-k)!).

lemma bceq :∀n,k. bc n k = n!/(k!*(n-k)!).
// qed.

theorem bc_n_n: ∀n. bc n n = 1.
#n >bceq <minus_n_n <times_n_1 @div_n_n //
qed.

theorem bc_n_O: ∀n. bc n O = 1.
#n >bceq <minus_n_O /2/
qed.

theorem fact_minus: ∀n,k. k < n → 
  (n - S k)!*(n-k) = (n - k)!.
#n #k (cases n)
  [#ltO @False_ind /2/
  |#l #ltl >(minus_Sn_m k) [// |@le_S_S_to_le //]
  ]
qed.

theorem bc2 : ∀n.
∀k. k ≤n → k!*(n-k)! ∣ n!.
#n (elim n) 
  [#k #lek0 <(le_n_O_to_eq ? lek0) //
  |#m #Hind #k (cases k) normalize //
     #c #lec cases (le_to_or_lt_eq … (le_S_S_to_le …lec))
    [#ltcm 
     cut (m-(m-(S c)) = S c) [@plus_to_minus @plus_minus_m_m //] #eqSc     
     lapply (Hind c (le_S_S_to_le … lec)) #Hc
     lapply (Hind (m - (S c)) ?) [@le_plus_to_minus //] >eqSc #Hmc
     >(plus_minus_m_m m c) in ⊢ (??(??(?%))) [|@le_S_S_to_le //]
     >commutative_plus >(distributive_times_plus ? (S c))
     @divides_plus
      [>associative_times >(commutative_times (S c))
       <associative_times @divides_times //
      |<(fact_minus …ltcm) in ⊢ (?(??%)?) 
       <associative_times @divides_times //
       >commutative_times @Hmc
      ]
    |#eqcm >eqcm <minus_n_n <times_n_1 // 
    ]
  ]
qed.
           
theorem bc1: ∀n.∀k. k < n → 
  bc (S n) (S k) = (bc n k) + (bc n (S k)).
#n #k #ltkn > bceq >(bceq n) >(bceq n (S k))
>(div_times_times ?? (S k)) in ⊢ (???(?%?)) 
  [|>(times_n_O 0) @lt_times // | //]
>associative_times in ⊢ (???(?(??%)?))
>commutative_times in ⊢ (???(?(??(??%))?))
<associative_times in ⊢ (???(?(??%)?))
>(div_times_times ?? (n - k)) in ⊢ (???(??%))  
  [|>(times_n_O 0) @lt_times // 
   |@(le_plus_to_le_r k ??) <plus_minus_m_m /2/]
>associative_times in ⊢ (???(??(??%)))
>fact_minus // <plus_div 
  [<distributive_times_plus
   >commutative_plus in ⊢ (???%) <plus_n_Sm <plus_minus_m_m [|/2/] @refl
  |<fact_minus // <associative_times @divides_times // @(bc2 n (S k)) //
  |>associative_times >(commutative_times (S k))
   <associative_times @divides_times // @bc2 /2/
  |>(times_n_O 0) @lt_times [@(le_1_fact (S k)) | //]
  ]
qed.

theorem lt_O_bc: ∀n,m. m ≤ n → O < bc n m.
#n (elim n) 
  [#m #lemO @(le_n_O_elim ? lemO) //
  |-n #n #Hind #m (cases m) //
   #m #lemn cases(le_to_or_lt_eq … (le_S_S_to_le …lemn)) //
   #ltmn >bc1 // >(plus_O_n 0) @lt_plus @Hind /2/
  ]
qed. 

(*
theorem binomial_law:∀a,b,n.
  (a+b)^n = Σ_{k < S n}((bc n k)*(a^(n-k))*(b^k)).
#a #b #n (elim n) //
-n #n #Hind normalize in ⊢ (? ? % ?).
>bigop_Strue // >Hind >distributive_times_plus 
<(minus_n_n (S n)) <commutative_times <(commutative_times b)
(* hint??? *)
>(bigop_distr ???? natDop ? a) >(bigop_distr ???? natDop ? b)
>bigop_Strue in ⊢ (??(??%)?) // <associative_plus 
<commutative_plus in ⊢ (??(? % ?) ?) >associative_plus @eq_f2
  [<minus_n_n >bc_n_n >bc_n_n normalize //
  |>bigop_0 >associative_plus >commutative_plus in ⊢ (??(??%)?) 
   <associative_plus >bigop_0 // @eq_f2 
    [>(bigop_op n ??? natACop) @same_bigop //
     #i #ltin #_ <associative_times >(commutative_times b)
     >(associative_times ?? b) <(distributive_times_plus_r (b^(S i)))
     @eq_f2 // <associative_times >(commutative_times a) 
     >associative_times cut(∀n.a*a^n = a^(S n)) [#n @commutative_times] #H
     >H <minus_Sn_m // <(distributive_times_plus_r (a^(n-i)))
     @eq_f2 // @sym_eq >commutative_plus @bc1 //
    |>bc_n_O >bc_n_O normalize //
    ]
  ]
qed.
     
theorem exp_S_sigma_p:∀a,n.
(S a)^n = Σ_{k < S n}((bc n k)*a^(n-k)).
#a #n cut (S a = a + 1) // #H >H
>binomial_law @same_bigop //
qed.

(*
theorem exp_Sn_SSO: \forall n. exp (S n) 2 = S((exp n 2) + 2*n).
intros.simplify.
rewrite < times_n_SO.
rewrite < plus_n_O.
rewrite < sym_times.simplify.
rewrite < assoc_plus.
rewrite < sym_plus.
reflexivity.
qed. *)
*)