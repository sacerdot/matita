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

(*
theorem true_to_pi_p_Sn: ∀n,p,g.
  p n = true \to pi_p (S n) p g = (g n)*(pi_p n p g).
intros.
unfold pi_p.
apply true_to_iter_p_gen_Sn.
assumption.
qed.
   
theorem false_to_pi_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to nat.
p n = false \to pi_p (S n) p g = pi_p n p g.
intros.
unfold pi_p.
apply false_to_iter_p_gen_Sn.
assumption.
qed.  

theorem eq_pi_p: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to nat.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to g1 x = g2 x) \to
pi_p n p1 g1 = pi_p n p2 g2.
intros.
unfold pi_p.
apply eq_iter_p_gen;
assumption.
qed.

theorem eq_pi_p1: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to nat.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to p1 x = true \to g1 x = g2 x) \to
pi_p n p1 g1 = pi_p n p2 g2.
intros.
unfold pi_p.
apply eq_iter_p_gen1;
assumption.
qed.

theorem pi_p_false: 
\forall g: nat \to nat.\forall n.pi_p n (\lambda x.false) g = S O.
intros.
unfold pi_p.
apply iter_p_gen_false.
qed.

theorem pi_p_times: \forall n,k:nat.\forall p:nat \to bool.
\forall g: nat \to nat.
pi_p (k+n) p g 
= pi_p k (\lambda x.p (x+n)) (\lambda x.g (x+n)) * pi_p n p g.
intros.
unfold pi_p.
apply (iter_p_gen_plusA nat n k p g (S O) times)
[ apply sym_times.
| intros.
  apply sym_eq.
  apply times_n_SO
| apply associative_times
]
qed.

theorem false_to_eq_pi_p: \forall n,m:nat.n \le m \to
\forall p:nat \to bool.
\forall g: nat \to nat. (\forall i:nat. n \le i \to i < m \to
p i = false) \to pi_p m p g = pi_p n p g.
intros.
unfold pi_p.
apply (false_to_eq_iter_p_gen);
assumption.
qed.

theorem or_false_eq_SO_to_eq_pi_p: 
\forall n,m:nat.\forall p:nat \to bool.
\forall g: nat \to nat.
n \le m \to (\forall i:nat. n \le i \to i < m \to p i = false \lor g i = S O)
\to pi_p m p g = pi_p n p g.
intros.
unfold pi_p.
apply or_false_eq_baseA_to_eq_iter_p_gen
  [intros.simplify.rewrite < plus_n_O.reflexivity
  |assumption
  |assumption
  ]
qed.

theorem pi_p2 : 
\forall n,m:nat.
\forall p1,p2:nat \to bool.
\forall g: nat \to nat \to nat.
pi_p (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (mod x m))) 
  (\lambda x.g (div x m) (mod x m)) =
pi_p n p1 
  (\lambda x.pi_p m p2 (g x)).
intros.
unfold pi_p.
apply (iter_p_gen2 n m p1 p2 nat g (S O) times)
[ apply sym_times
| apply associative_times
| intros.
  apply sym_eq.
  apply times_n_SO
]
qed.

theorem pi_p2' : 
\forall n,m:nat.
\forall p1:nat \to bool.
\forall p2:nat \to nat \to bool.
\forall g: nat \to nat \to nat.
pi_p (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (div x m) (mod x  m))) 
  (\lambda x.g (div x m) (mod x m)) =
pi_p n p1 
  (\lambda x.pi_p m (p2 x) (g x)).
intros.
unfold pi_p.
apply (iter_p_gen2' n m p1 p2 nat g (S O) times)
[ apply sym_times
| apply associative_times
| intros.
  apply sym_eq.
  apply times_n_SO
]
qed.

lemma pi_p_gi: \forall g: nat \to nat.
\forall n,i.\forall p:nat \to bool.i < n \to p i = true \to 
pi_p n p g = g i * pi_p n (\lambda x. andb (p x) (notb (eqb x i))) g.
intros.
unfold pi_p.
apply (iter_p_gen_gi)
[ apply sym_times
| apply associative_times
| intros.
  apply sym_eq.
  apply times_n_SO
| assumption
| assumption
]
qed.

theorem eq_pi_p_gh: 
\forall g,h,h1: nat \to nat.\forall n,n1.
\forall p1,p2:nat \to bool.
(\forall i. i < n \to p1 i = true \to p2 (h i) = true) \to
(\forall i. i < n \to p1 i = true \to h1 (h i) = i) \to 
(\forall i. i < n \to p1 i = true \to h i < n1) \to 
(\forall j. j < n1 \to p2 j = true \to p1 (h1 j) = true) \to
(\forall j. j < n1 \to p2 j = true \to h (h1 j) = j) \to 
(\forall j. j < n1 \to p2 j = true \to h1 j < n) \to 
pi_p n p1 (\lambda x.g(h x)) = pi_p n1 p2 g.
intros.
unfold pi_p.
apply (eq_iter_p_gen_gh nat (S O) times ? ? ? g h h1 n n1 p1 p2)
[ apply sym_times
| apply associative_times
| intros.
  apply sym_eq.
  apply times_n_SO
| assumption
| assumption
| assumption
| assumption
| assumption
| assumption
]
qed.
     
theorem exp_sigma_p: \forall n,a,p. 
pi_p n p (\lambda x.a) = (exp a (sigma_p n p (\lambda x.S O))).
intros.
elim n
  [reflexivity
  |apply (bool_elim ? (p n1))
    [intro.
     rewrite > true_to_pi_p_Sn
      [rewrite > true_to_sigma_p_Sn
        [simplify.
         rewrite > H.
         reflexivity.
        |assumption
        ]
      |assumption
      ]
    |intro.
     rewrite > false_to_pi_p_Sn
      [rewrite > false_to_sigma_p_Sn
        [simplify.assumption
        |assumption
        ]
      |assumption
      ]
    ]
  ]
qed.

theorem exp_sigma_p1: \forall n,a,p,f. 
pi_p n p (\lambda x.(exp a (f x))) = (exp a (sigma_p n p f)).
intros.
elim n
  [reflexivity
  |apply (bool_elim ? (p n1))
    [intro.
     rewrite > true_to_pi_p_Sn
      [rewrite > true_to_sigma_p_Sn
        [simplify.
         rewrite > H.
         rewrite > exp_plus_times.
         reflexivity.
        |assumption
        ]
      |assumption
      ]
    |intro.
     rewrite > false_to_pi_p_Sn
      [rewrite > false_to_sigma_p_Sn
        [simplify.assumption
        |assumption
        ]
      |assumption
      ]
    ]
  ]
qed.

theorem times_pi_p: \forall n,p,f,g. 
pi_p n p (\lambda x.f x*g x) = pi_p n p f * pi_p n p  g. 
intros.
elim n
  [simplify.reflexivity
  |apply (bool_elim ? (p n1))
    [intro.
     rewrite > true_to_pi_p_Sn
      [rewrite > true_to_pi_p_Sn
        [rewrite > true_to_pi_p_Sn
          [rewrite > H.autobatch
          |assumption
          ]
        |assumption
        ]
      |assumption
      ]
    |intro.
     rewrite > false_to_pi_p_Sn
      [rewrite > false_to_pi_p_Sn
        [rewrite > false_to_pi_p_Sn;assumption
        |assumption
        ]
      |assumption
      ]
    ]
  ]
qed.


theorem exp_times_pi_p: \forall n,m,k,p,f. 
pi_p n p (\lambda x.exp k (m*(f x))) = 
exp (pi_p n p (\lambda x.exp k (f x))) m.
intros.
apply (trans_eq ? ? (pi_p n p (\lambda x.(exp (exp k (f x)) m))))
  [apply eq_pi_p;intros
    [reflexivity
    |apply sym_eq.rewrite > sym_times.
     apply exp_exp_times
    ]
  |apply exp_pi_p
  ]
qed.


theorem pi_p_knm:
\forall g: nat \to nat.
\forall h2:nat \to nat \to nat.
\forall h11,h12:nat \to nat. 
\forall k,n,m.
\forall p1,p21:nat \to bool.
\forall p22:nat \to nat \to bool.
(\forall x. x < k \to p1 x = true \to 
p21 (h11 x) = true ∧ p22 (h11 x) (h12 x) = true
\land h2 (h11 x) (h12 x) = x 
\land (h11 x) < n \land (h12 x) < m) \to
(\forall i,j. i < n \to j < m \to p21 i = true \to p22 i j = true \to 
p1 (h2 i j) = true \land 
h11 (h2 i j) = i \land h12 (h2 i j) = j
\land h2 i j < k) →
(*
Pi z < k | p1 z. g z = 
Pi x < n | p21 x. Pi y < m | p22 x y.g (h2 x y).
*)
pi_p k p1 g =
pi_p n p21 (\lambda x:nat.pi_p m (p22 x) (\lambda y. g (h2 x y))).
intros.
unfold pi_p.unfold pi_p.
apply (iter_p_gen_knm nat (S O) times sym_times assoc_times ? ? ? h11 h12)
  [intros.apply sym_eq.apply times_n_SO.
  |assumption
  |assumption
  ]
qed.

theorem pi_p_pi_p: 
\forall g: nat \to nat \to nat.
\forall h11,h12,h21,h22: nat \to nat \to nat. 
\forall n1,m1,n2,m2.
\forall p11,p21:nat \to bool.
\forall p12,p22:nat \to nat \to bool.
(\forall i,j. i < n2 \to j < m2 \to p21 i = true \to p22 i j = true \to 
p11 (h11 i j) = true \land p12 (h11 i j) (h12 i j) = true
\land h21 (h11 i j) (h12 i j) = i \land h22 (h11 i j) (h12 i j) = j
\land h11 i j < n1 \land h12 i j < m1) \to
(\forall i,j. i < n1 \to j < m1 \to p11 i = true \to p12 i j = true \to 
p21 (h21 i j) = true \land p22 (h21 i j) (h22 i j) = true
\land h11 (h21 i j) (h22 i j) = i \land h12 (h21 i j) (h22 i j) = j
\land (h21 i j) < n2 \land (h22 i j) < m2) \to
pi_p n1 p11 
     (\lambda x:nat .pi_p m1 (p12 x) (\lambda y. g x y)) =
pi_p n2 p21 
    (\lambda x:nat .pi_p m2 (p22 x)  (\lambda y. g (h11 x y) (h12 x y))).
intros.
unfold pi_p.unfold pi_p.
apply (iter_p_gen_2_eq ? ? ? sym_times assoc_times ? ? ? ? h21 h22)
  [intros.apply sym_eq.apply times_n_SO.
  |assumption
  |assumption
  ]
qed.

theorem pi_p_pi_p1: 
\forall g: nat \to nat \to nat.
\forall n,m.
\forall p11,p21:nat \to bool.
\forall p12,p22:nat \to nat \to bool.
(\forall x,y. x < n \to y < m \to 
 (p11 x \land p12 x y) = (p21 y \land p22 y x)) \to
pi_p n p11 (\lambda x:nat.pi_p m (p12 x) (\lambda y. g x y)) =
pi_p m p21 (\lambda y:nat.pi_p n (p22 y) (\lambda x. g x y)).
intros.
unfold pi_p.unfold pi_p.
apply (iter_p_gen_iter_p_gen ? ? ? sym_times assoc_times)
  [intros.apply sym_eq.apply times_n_SO.
  |assumption
  ]
qed. *)