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

set "baseuri" "cic:/matita/Z/sigma_p.ma".

include "Z/times.ma".
include "nat/primes.ma".
include "nat/ord.ma".
include "nat/generic_sigma_p.ma".

(* sigma_p in Z is a specialization of sigma_p_gen *)
definition sigma_p: nat \to (nat \to bool) \to (nat \to Z) \to Z \def
\lambda n, p, g. (sigma_p_gen n p Z g OZ Zplus).

theorem symmetricZPlus: symmetric Z Zplus.
change with (\forall a,b:Z. (Zplus a b) = (Zplus b a)).
intros.
rewrite > sym_Zplus.
reflexivity.
qed.
   
theorem true_to_sigma_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to Z.
p n = true \to sigma_p (S n) p g = 
(g n)+(sigma_p n p g).
intros.
unfold sigma_p.
apply true_to_sigma_p_Sn_gen.
assumption.
qed.
   
theorem false_to_sigma_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to Z.
p n = false \to sigma_p (S n) p g = sigma_p n p g.
intros.
unfold sigma_p.
apply false_to_sigma_p_Sn_gen.
assumption.
qed.

theorem eq_sigma_p: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to Z.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros.
unfold sigma_p.
apply eq_sigma_p_gen;
  assumption.
qed.

theorem eq_sigma_p1: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to Z.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to p1 x = true \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros.
unfold sigma_p.
apply eq_sigma_p1_gen;
  assumption.
qed.

theorem sigma_p_false: 
\forall g: nat \to Z.\forall n.sigma_p n (\lambda x.false) g = O.
intros.
unfold sigma_p.
apply sigma_p_false_gen.
qed.

theorem sigma_p_plus: \forall n,k:nat.\forall p:nat \to bool.
\forall g: nat \to Z.
sigma_p (k+n) p g 
= sigma_p k (\lambda x.p (x+n)) (\lambda x.g (x+n)) + sigma_p n p g.
intros.
unfold sigma_p.
apply (sigma_p_plusA_gen Z n k p g OZ Zplus)
[ apply symmetricZPlus.
| intros.
  apply cic:/matita/Z/plus/Zplus_z_OZ.con
| apply associative_Zplus
]
qed.

theorem false_to_eq_sigma_p: \forall n,m:nat.n \le m \to
\forall p:nat \to bool.
\forall g: nat \to Z. (\forall i:nat. n \le i \to i < m \to
p i = false) \to sigma_p m p g = sigma_p n p g.
intros.
unfold sigma_p.
apply (false_to_eq_sigma_p_gen);
  assumption.
qed.

theorem sigma_p2 : 
\forall n,m:nat.
\forall p1,p2:nat \to bool.
\forall g: nat \to nat \to Z.
sigma_p (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (mod x m))) 
  (\lambda x.g (div x m) (mod x m)) =
sigma_p n p1 
  (\lambda x.sigma_p m p2 (g x)).
intros.
unfold sigma_p.
apply (sigma_p2_gen n m p1 p2 Z g OZ Zplus)
[ apply symmetricZPlus
| apply associative_Zplus
| intros.
  apply Zplus_z_OZ
]
qed.

(* a stronger, dependent version, required e.g. for dirichlet product *)

theorem sigma_p2' : 
\forall n,m:nat.
\forall p1:nat \to bool.
\forall p2:nat \to nat \to bool.
\forall g: nat \to nat \to Z.
sigma_p (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (div x m) (mod x m))) 
  (\lambda x.g (div x m) (mod x m)) =
sigma_p n p1 
  (\lambda x.sigma_p m (p2 x) (g x)).
intros.
unfold sigma_p.
apply (sigma_p2_gen' n m p1 p2 Z g OZ Zplus)
[ apply symmetricZPlus
| apply associative_Zplus
| intros.
  apply Zplus_z_OZ
]
qed.

lemma sigma_p_gi: \forall g: nat \to Z.
\forall n,i.\forall p:nat \to bool.i < n \to p i = true \to 
sigma_p n p g = g i + sigma_p n (\lambda x. andb (p x) (notb (eqb x i))) g.
intros.
unfold sigma_p.
apply (sigma_p_gi_gen)
[ apply symmetricZPlus
| apply associative_Zplus
| intros.
  apply Zplus_z_OZ
| assumption
| assumption
]
qed.

theorem eq_sigma_p_gh: 
\forall g: nat \to Z.
\forall h,h1: nat \to nat.\forall n,n1.
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
apply (eq_sigma_p_gh_gen Z OZ Zplus ? ? ? g h h1 n n1 p1 p2)
[ apply symmetricZPlus
| apply associative_Zplus
| intros.
  apply Zplus_z_OZ
| assumption
| assumption
| assumption
| assumption
| assumption
| assumption
]
qed.


theorem sigma_p_divides_b: 
\forall n,m,p:nat.O < n \to prime p \to Not (divides p n) \to 
\forall g: nat \to Z.
sigma_p (S (n*(exp p m))) (\lambda x.divides_b x (n*(exp p m))) g =
sigma_p (S n) (\lambda x.divides_b x n)
  (\lambda x.sigma_p (S m) (\lambda y.true) (\lambda y.g (x*(exp p y)))).
intros.
unfold sigma_p.
apply (sigma_p_divides_gen Z OZ Zplus n m p ? ? ? g)
[ assumption
| assumption
| assumption
| apply symmetricZPlus
| apply associative_Zplus
| intros.
  apply Zplus_z_OZ
]
qed.

    
(* sigma_p and Ztimes *)
lemma Ztimes_sigma_pl: \forall z:Z.\forall n:nat.\forall p. \forall f.
z * (sigma_p n p f) = sigma_p n p (\lambda i.z*(f i)).
intros.
apply (distributive_times_plus_sigma_p_generic Z Zplus OZ Ztimes n z p f)
[ apply symmetricZPlus
| apply associative_Zplus
| intros.
  apply Zplus_z_OZ
| apply symmetric_Ztimes
| apply distributive_Ztimes_Zplus
| intros.
  rewrite > (Ztimes_z_OZ a).
  reflexivity
]
qed.

lemma Ztimes_sigma_pr: \forall z:Z.\forall n:nat.\forall p. \forall f.
(sigma_p n p f) * z = sigma_p n p (\lambda i.(f i)*z).
intros.
rewrite < sym_Ztimes.
rewrite > Ztimes_sigma_pl.
apply eq_sigma_p
  [intros.reflexivity
  |intros.apply sym_Ztimes
  ]
qed.