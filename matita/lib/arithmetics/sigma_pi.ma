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
include "arithmetics/bigops.ma".

(* Sigma e Pi *)

notation "∑_{ ident i < n | p } f"
  with precedence 80
for @{'bigop $n plus 0 (λ${ident i}. $p) (λ${ident i}. $f)}.

notation "∑_{ ident i < n } f"
  with precedence 80
for @{'bigop $n plus 0 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "∑_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) plus 0 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "∑_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) plus 0 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
 
notation "∏_{ ident i < n | p} f"
  with precedence 80
for @{'bigop $n times 1 (λ${ident i}.$p) (λ${ident i}. $f)}.
 
notation "∏_{ ident i < n } f"
  with precedence 80
for @{'bigop $n times 1 (λ${ident i}.true) (λ${ident i}. $f)}.

notation "∏_{ ident j ∈ [a,b[ } f"
  with precedence 80
for @{'bigop ($b-$a) times 1 (λ${ident j}.((λ${ident j}.true) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.
  
notation "∏_{ ident j ∈ [a,b[ | p } f"
  with precedence 80
for @{'bigop ($b-$a) times 1 (λ${ident j}.((λ${ident j}.$p) (${ident j}+$a)))
  (λ${ident j}.((λ${ident j}.$f)(${ident j}+$a)))}.

(* instances of associative and commutative operations *)

definition plusA ≝ mk_Aop nat 0 plus (λa.refl ? a) (λn.sym_eq ??? (plus_n_O n)) 
   (λa,b,c.sym_eq ??? (associative_plus a b c)).
   
definition plusAC ≝ mk_ACop nat 0 plusA commutative_plus.

definition timesA ≝ mk_Aop nat 1 times 
   (λa.sym_eq ??? (plus_n_O a)) (λn.sym_eq ??? (times_n_1 n)) 
   (λa,b,c.sym_eq ??? (associative_times a b c)).
   
definition timesAC ≝ mk_ACop nat 1 timesA commutative_times.

definition natD ≝ mk_Dop nat 0 plusAC times (λn.(sym_eq ??? (times_n_O n))) 
   distributive_times_plus.
   
(********************************************************)

theorem sigma_const: ∀n:nat. ∑_{i<n} 1 = n.
#n elim n // #n1 >bigop_Strue //
qed.

(* monotonicity; these roperty should be expressed at a more
genral level *)

theorem le_pi: 
∀n.∀p:nat → bool.∀g1,g2:nat → nat. 
  (∀i.i<n → p i = true → g1 i ≤ g2 i ) → 
  ∏_{i < n | p i} (g1 i) ≤ ∏_{i < n | p i} (g2 i).
#n #p #g1 #g2 elim n 
  [#_ @le_n
  |#n1 #Hind #Hle cases (true_or_false (p n1)) #Hcase
    [ >bigop_Strue // >bigop_Strue // @le_times
      [@Hle // |@Hind #i #lti #Hpi @Hle [@lt_to_le @le_S_S @lti|@Hpi]]
    |>bigop_Sfalse // >bigop_Sfalse // @Hind
     #i #lti #Hpi @Hle [@lt_to_le @le_S_S @lti|@Hpi]
    ]
  ]
qed.
    
theorem exp_sigma: ∀n,a,p. 
  ∏_{i < n | p i} a = exp a (∑_{i < n | p i} 1).
#n #a #p elim n // #n1 cases (true_or_false (p n1)) #Hcase
  [>bigop_Strue // >bigop_Strue // |>bigop_Sfalse // >bigop_Sfalse //] 
qed.

theorem times_pi: ∀n,p,f,g. 
  ∏_{i<n|p i}(f i*g i) = ∏_{i<n|p i}(f i) * ∏_{i<n|p i}(g i). 
#n #p #f #g elim n // #n1 cases (true_or_false (p n1)) #Hcase #Hind
  [>bigop_Strue // >bigop_Strue // >bigop_Strue //
  |>bigop_Sfalse // >bigop_Sfalse // >bigop_Sfalse //
  ]
qed.

theorem pi_1: ∀n,p. 
  ∏_{i < n | p i} 1 = 1.
#n #p elim n // #n1 #Hind cases (true_or_false (p n1)) #Hc 
  [>bigop_Strue >Hind // |>bigop_Sfalse // ]
qed.

theorem exp_pi: ∀n,m,p,f. 
  ∏_{i < n | p i}(exp (f i) m) = exp (∏_{i < n | p i}(f i)) m.
#n #m #p #f elim m
  [@pi_1
  |#m1 #Hind >times_pi >Hind %
  ]
qed.
