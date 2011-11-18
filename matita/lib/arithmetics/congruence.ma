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

include "arithmetics/primes.ma".

(* successor mod n *)
definition S_mod: nat → nat → nat ≝
λn,m:nat. (S m) \mod n.

definition congruent: nat → nat → nat → Prop ≝
λn,m,p:nat. mod n p = mod m p.

interpretation "congruent" 'congruent n m p = (congruent n m p).

notation "hvbox(n break ≅_{p} m)"
  non associative with precedence 45
  for @{ 'congruent $n $m $p }.
  
theorem congruent_n_n: ∀n,p:nat.n ≅_{p} n .
// qed.

theorem transitive_congruent: 
  ∀p.transitive nat (λn,m.congruent n m p).
/2/ qed.

theorem le_to_mod: ∀n,m:nat. n < m → n = n \mod m.
#n #m #ltnm @(div_mod_spec_to_eq2 n m O n (n/m) (n \mod m))
% // @lt_mod_m_m @(ltn_to_ltO … ltnm) 
qed.

theorem mod_mod : ∀n,p:nat. O<p → n \mod p = (n \mod p) \mod p.
#n #p #posp >(div_mod (n \mod p) p) {⊢ (? ? % ?) }
>(eq_div_O ? p) // @lt_mod_m_m //
qed.

theorem mod_times_mod : ∀n,m,p:nat. O<p → O<m → 
  n \mod p = (n \mod (m*p)) \mod p.
#n #m #p #posp #posm
@(div_mod_spec_to_eq2 n p (n/p) (n \mod p) 
(n/(m*p)*m + (n \mod (m*p)/p))) 
  [@div_mod_spec_div_mod //
  |% [@lt_mod_m_m //] >distributive_times_plus_r
   >associative_plus <div_mod >associative_times <div_mod //
  ]
qed.

theorem congruent_n_mod_n : ∀n,p:nat. O < p →
 n ≅_{p} (n \mod p).
/2/ qed.

theorem congruent_n_mod_times : ∀n,m,p:nat. O < p → O < m → 
  n ≅_{p} (n \mod (m*p)).
/2/ qed.

theorem eq_times_plus_to_congruent: ∀n,m,p,r:nat. O< p → 
  n = r*p+m → n ≅_{p} m .
#n #m #p #r #posp #eqn
@(div_mod_spec_to_eq2 n p (div n p) (mod n p) (r +(div m p)) (mod m p))
  [@div_mod_spec_div_mod //
  |% [@lt_mod_m_m //] >distributive_times_plus_r
   >associative_plus <div_mod //
  ]
qed.

theorem divides_to_congruent: ∀n,m,p:nat. O < p → m ≤ n → 
  p ∣(n - m) → n ≅_{p} m .
#n #m #p #posp #lemn * #l #eqpl 
@(eq_times_plus_to_congruent … l posp) /2/
qed.

theorem congruent_to_divides: ∀n,m,p:nat.O < p → 
  n ≅_{p} m → p ∣ (n - m).
#n #m #p #posp #congnm @(quotient ? ? ((n / p)-(m / p)))
>commutative_times >(div_mod n p) {⊢ (??%?)}
>(div_mod m p) {⊢ (??%?)} <(commutative_plus (m \mod p))
<congnm <(minus_plus ? (n \mod p)) <minus_plus_m_m //
qed.

theorem mod_times: ∀n,m,p:nat. O < p → 
  n*m ≅_{p} (n \mod p)*(m \mod p).
#n #m #p #posp @(eq_times_plus_to_congruent ?? p 
  ((n / p)*p*(m / p) + (n / p)*(m \mod p) + (n \mod p)*(m / p))) //
@(trans_eq ?? (((n/p)*p+(n \mod p))*((m/p)*p+(m \mod p))))
  [@eq_f2 //
  |@(trans_eq ? ? (((n/p)*p)*((m/p)*p) + (n/p)*p*(m \mod p) +
    (n \mod p)*((m / p)*p) + (n \mod p)*(m \mod p))) //
   >distributive_times_plus >distributive_times_plus_r 
   >distributive_times_plus_r <associative_plus @eq_f2 //
  ]
qed.

theorem congruent_times: ∀n,m,n1,m1,p. O < p → 
  n ≅_{p} n1 → m ≅_{p} m1 → n*m ≅_{p} n1*m1 .
#n #m #n1 #m1 #p #posp #congn #congm
@(transitive_congruent … (mod_times n m p posp))
>congn >congm @sym_eq @mod_times //
qed.

(*
theorem congruent_pi: \forall f:nat \to nat. \forall n,m,p:nat.O < p \to
congruent (pi n f m) (pi n (\lambda m. mod (f m) p) m) p.
intros.
elim n. simplify.
apply congruent_n_mod_n.assumption.
simplify.
apply congruent_times.
assumption.
apply congruent_n_mod_n.assumption.
assumption.
qed. *)
