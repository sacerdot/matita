(**************************************************************************)
(*       ___	                                                          *)
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

include "nat/primes.ma".
(* include "nat/ord.ma". *)
include "nat/generic_iter_p.ma".
(* include "nat/count.ma". necessary just to use bool_to_nat and bool_to_nat_andb*)
include "nat/iteration2.ma".

(* pi_p on nautral numbers is a specialization of iter_p_gen *)
definition pi_p: nat \to (nat \to bool) \to (nat \to nat) \to nat \def
\lambda n, p, g. (iter_p_gen n p nat g (S O) times).

(*
notation < "(mstyle scriptlevel 1 scriptsizemultiplier 1.7(Π) ­
             ) 
            \below 
            (p
            \atop 
            (ident i < n)) f" 
non associative with precedence 65 for 
@{ 'product $n (λ${ident i}:$xx1.$p) (λ${ident i}:$xx2.$f) }.

notation < "(mstyle scriptlevel 1 scriptsizemultiplier 1.7(Π) ­
             ) 
            \below 
            ((ident i < n)) f" 
non associative with precedence 65 for 
@{ 'product $n (λ_:$xx1.$xx3) (λ${ident i}:$xx2.$f) }.

interpretation "big product" 'product n p f = (pi_p n p f).

notation > "'Pi' (ident x) < n | p . term 46 f"
non associative with precedence 65
for @{ 'product $n (λ${ident x}.$p) (λ${ident x}.$f) }. 

notation > "'Pi' (ident x) ≤ n | p . term 46 f"
non associative with precedence 65
for @{ 'product (S $n) (λ${ident x}.$p) (λ${ident x}.$f) }. 

notation > "'Pi' (ident x) < n . term 46 f"
non associative with precedence 65
for @{ 'product $n (λ_.true) (λ${ident x}.$f) }. 
*)

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

(* monotonicity *)
theorem le_pi_p: 
\forall n:nat. \forall p:nat \to bool. \forall g1,g2:nat \to nat.
(\forall i. i < n \to p i = true \to g1 i \le g2 i ) \to 
pi_p n p g1 \le pi_p n p g2.
intros.
elim n in H ⊢ %
  [apply le_n.
  |apply (bool_elim ? (p n1));intros
    [rewrite > true_to_pi_p_Sn
      [rewrite > true_to_pi_p_Sn in ⊢ (? ? %)
        [apply le_times
          [apply H1[apply le_n|assumption]
          |apply H.
           intros.
           apply H1[apply le_S.assumption|assumption]
          ]
        |assumption
        ]
      |assumption
      ]
    |rewrite > false_to_pi_p_Sn
      [rewrite > false_to_pi_p_Sn in ⊢ (? ? %)
        [apply H.
         intros.
         apply H1[apply le_S.assumption|assumption]
        |assumption
        ]
      |assumption
      ]
    ]
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

theorem pi_p_SO: \forall n,p. 
pi_p n p (\lambda i.S O) = S O.
intros.elim n
  [reflexivity
  |simplify.elim (p n1)
    [simplify.rewrite < plus_n_O.assumption
    |simplify.assumption
    ]
  ]
qed.

theorem exp_pi_p: \forall n,m,p,f. 
pi_p n p (\lambda x.exp (f x) m) = exp (pi_p n p f) m.
intros.
elim m
  [simplify.apply pi_p_SO
  |simplify.
   rewrite > times_pi_p.
   rewrite < H.
   reflexivity
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
qed.