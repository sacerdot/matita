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

set "baseuri" "cic:/matita/nat/iteration2".

include "nat/primes.ma".
include "nat/ord.ma".
include "nat/generic_sigma_p.ma".


(* sigma_p on nautral numbers is a specialization of sigma_p_gen *)
definition sigma_p: nat \to (nat \to bool) \to (nat \to nat) \to nat \def
\lambda n, p, g. (sigma_p_gen n p nat g O plus).

theorem symmetricIntPlus: symmetric nat plus.
change with (\forall a,b:nat. (plus a b) = (plus b a)).
intros.
rewrite > sym_plus.
reflexivity.
qed.
   
(*the following theorems on sigma_p in N are obtained by the more general ones
 * in sigma_p_gen.ma
 *)
theorem true_to_sigma_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to nat.
p n = true \to sigma_p (S n) p g = 
(g n)+(sigma_p n p g).
intros.
unfold sigma_p.
apply true_to_sigma_p_Sn_gen.
assumption.
qed.
   
theorem false_to_sigma_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to nat.
p n = false \to sigma_p (S n) p g = sigma_p n p g.
intros.
unfold sigma_p.
apply false_to_sigma_p_Sn_gen.
assumption.

qed.

theorem eq_sigma_p: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to nat.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros.
unfold sigma_p.
apply eq_sigma_p_gen;
  assumption.
qed.

theorem eq_sigma_p1: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to nat.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to p1 x = true \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros.
unfold sigma_p.
apply eq_sigma_p1_gen;
  assumption.
qed.

theorem sigma_p_false: 
\forall g: nat \to nat.\forall n.sigma_p n (\lambda x.false) g = O.
intros.
unfold sigma_p.
apply sigma_p_false_gen.
qed.

theorem sigma_p_plus: \forall n,k:nat.\forall p:nat \to bool.
\forall g: nat \to nat.
sigma_p (k+n) p g 
= sigma_p k (\lambda x.p (x+n)) (\lambda x.g (x+n)) + sigma_p n p g.
intros.
unfold sigma_p.
apply (sigma_p_plusA_gen nat n k p g O plus)
[ apply symmetricIntPlus.
| intros.
  apply sym_eq.
  apply plus_n_O
| apply associative_plus
]
qed.

theorem false_to_eq_sigma_p: \forall n,m:nat.n \le m \to
\forall p:nat \to bool.
\forall g: nat \to nat. (\forall i:nat. n \le i \to i < m \to
p i = false) \to sigma_p m p g = sigma_p n p g.
intros.
unfold sigma_p.
apply (false_to_eq_sigma_p_gen);
  assumption.
qed.

theorem sigma_p2 : 
\forall n,m:nat.
\forall p1,p2:nat \to bool.
\forall g: nat \to nat \to nat.
sigma_p (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (mod x m))) 
  (\lambda x.g (div x m) (mod x m)) =
sigma_p n p1 
  (\lambda x.sigma_p m p2 (g x)).
intros.
unfold sigma_p.
apply (sigma_p2_gen n m p1 p2 nat g O plus)
[ apply symmetricIntPlus
| apply associative_plus
| intros.
  apply sym_eq.
  apply plus_n_O
]
qed.

theorem sigma_p2' : 
\forall n,m:nat.
\forall p1:nat \to bool.
\forall p2:nat \to nat \to bool.
\forall g: nat \to nat \to nat.
sigma_p (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (div x m) (mod x m))) 
  (\lambda x.g (div x m) (mod x m)) =
sigma_p n p1 
  (\lambda x.sigma_p m (p2 x) (g x)).
intros.
unfold sigma_p.
apply (sigma_p2_gen' n m p1 p2 nat g O plus)
[ apply symmetricIntPlus
| apply associative_plus
| intros.
  apply sym_eq.
  apply plus_n_O
]
qed.

lemma sigma_p_gi: \forall g: nat \to nat.
\forall n,i.\forall p:nat \to bool.i < n \to p i = true \to 
sigma_p n p g = g i + sigma_p n (\lambda x. andb (p x) (notb (eqb x i))) g.
intros.
unfold sigma_p.
apply (sigma_p_gi_gen)
[ apply symmetricIntPlus
| apply associative_plus
| intros.
  apply sym_eq.
  apply plus_n_O
| assumption
| assumption
]
qed.

theorem eq_sigma_p_gh: 
\forall g,h,h1: nat \to nat.\forall n,n1.
\forall p1,p2:nat \to bool.
(\forall i. i < n \to p1 i = true \to p2 (h i) = true) \to
(\forall i. i < n \to p1 i = true \to h1 (h i) = i) \to 
(\forall i. i < n \to p1 i = true \to h i < n1) \to 
(\forall j. j < n1 \to p2 j = true \to p1 (h1 j) = true) \to
(\forall j. j < n1 \to p2 j = true \to h (h1 j) = j) \to 
(\forall j. j < n1 \to p2 j = true \to h1 j < n) \to 
sigma_p n p1 (\lambda x.g(h x)) = sigma_p n1 (\lambda x.p2 x) g.
intros.
unfold sigma_p.
apply (eq_sigma_p_gh_gen nat O plus ? ? ? g h h1 n n1 p1 p2)
[ apply symmetricIntPlus
| apply associative_plus
| intros.
  apply sym_eq.
  apply plus_n_O
| assumption
| assumption
| assumption
| assumption
| assumption
| assumption
]
qed.


theorem sigma_p_divides: 
\forall n,m,p:nat.O < n \to prime p \to Not (divides p n) \to 
\forall g: nat \to nat.
sigma_p (S (n*(exp p m))) (\lambda x.divides_b x (n*(exp p m))) g =
sigma_p (S n) (\lambda x.divides_b x n)
  (\lambda x.sigma_p (S m) (\lambda y.true) (\lambda y.g (x*(exp p y)))).
intros.
unfold sigma_p.
apply (sigma_p_divides_gen nat O plus n m p ? ? ? g)
[ assumption
| assumption
| assumption
| apply symmetricIntPlus
| apply associative_plus
| intros.
  apply sym_eq.
  apply plus_n_O
]
qed.

theorem distributive_times_plus_sigma_p: \forall n,k:nat. \forall p:nat \to bool. \forall g:nat \to nat.
k*(sigma_p n p g) = sigma_p n p (\lambda i:nat.k * (g i)).
intros.
apply (distributive_times_plus_sigma_p_generic nat plus O times n k p g)
[ apply symmetricIntPlus
| apply associative_plus
| intros.
  apply sym_eq.
  apply plus_n_O
| apply symmetric_times
| apply distributive_times_plus
| intros.
  rewrite < (times_n_O a).
  reflexivity
]
qed.

