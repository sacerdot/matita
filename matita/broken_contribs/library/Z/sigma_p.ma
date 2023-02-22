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

include "Z/times.ma".
include "nat/primes.ma".
include "nat/ord.ma".
include "nat/generic_iter_p.ma".

(* sigma_p in Z is a specialization of iter_p_gen *)
definition sigma_p: nat \to (nat \to bool) \to (nat \to Z) \to Z \def
\lambda n, p, g. (iter_p_gen n p Z g OZ Zplus).

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
apply true_to_iter_p_gen_Sn.
assumption.
qed.
   
theorem false_to_sigma_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to Z.
p n = false \to sigma_p (S n) p g = sigma_p n p g.
intros.
unfold sigma_p.
apply false_to_iter_p_gen_Sn.
assumption.
qed.

theorem eq_sigma_p: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to Z.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros.
unfold sigma_p.
apply eq_iter_p_gen;
  assumption.
qed.

theorem eq_sigma_p1: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to Z.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to p1 x = true \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros.
unfold sigma_p.
apply eq_iter_p_gen1;
  assumption.
qed.

theorem sigma_p_false: 
\forall g: nat \to Z.\forall n.sigma_p n (\lambda x.false) g = O.
intros.
unfold sigma_p.
apply iter_p_gen_false.
qed.

theorem sigma_p_plus: \forall n,k:nat.\forall p:nat \to bool.
\forall g: nat \to Z.
sigma_p (k+n) p g 
= sigma_p k (\lambda x.p (x+n)) (\lambda x.g (x+n)) + sigma_p n p g.
intros.
unfold sigma_p.
apply (iter_p_gen_plusA Z n k p g OZ Zplus)
[ apply symmetricZPlus.
| intros.
  apply Zplus_z_OZ.
| apply associative_Zplus
]
qed.

theorem false_to_eq_sigma_p: \forall n,m:nat.n \le m \to
\forall p:nat \to bool.
\forall g: nat \to Z. (\forall i:nat. n \le i \to i < m \to
p i = false) \to sigma_p m p g = sigma_p n p g.
intros.
unfold sigma_p.
apply (false_to_eq_iter_p_gen);
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
apply (iter_p_gen2 n m p1 p2 Z g OZ Zplus)
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
apply (iter_p_gen2' n m p1 p2 Z g OZ Zplus)
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
apply (iter_p_gen_gi)
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
sigma_p n p1 (\lambda x.g(h x)) = sigma_p n1 p2 g.
intros.
unfold sigma_p.
apply (eq_iter_p_gen_gh Z OZ Zplus ? ? ? g h h1 n n1 p1 p2)
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


theorem divides_exp_to_lt_ord:\forall n,m,j,p. O < n \to prime p \to
p \ndivides n \to j \divides n*(exp p m) \to ord j p < S m.
intros.
cut (m = ord (n*(exp p m)) p)
  [apply le_S_S.
   rewrite > Hcut.
   apply divides_to_le_ord
    [elim (le_to_or_lt_eq ? ? (le_O_n j))
      [assumption
      |apply False_ind.
       apply (lt_to_not_eq ? ? H).
       elim H3.
       rewrite < H4 in H5.simplify in H5.
       elim (times_O_to_O ? ? H5)
        [apply sym_eq.assumption
        |apply False_ind.
         apply (not_le_Sn_n O).
         rewrite < H6 in \vdash (? ? %).
         apply lt_O_exp.
         elim H1.apply lt_to_le.assumption
        ]
      ]
    |rewrite > (times_n_O O).
     apply lt_times
      [assumption|apply lt_O_exp.apply (prime_to_lt_O ? H1)]
    |assumption
    |assumption
    ]
  |unfold ord.
   rewrite > (p_ord_exp1 p ? m n)
    [reflexivity
    |apply (prime_to_lt_O ? H1)
    |assumption
    |apply sym_times
    ]
  ]
qed.

theorem divides_exp_to_divides_ord_rem:\forall n,m,j,p. O < n \to prime p \to
p \ndivides n \to j \divides n*(exp p m) \to ord_rem j p \divides n.
intros.
cut (O < j)
  [cut (n = ord_rem (n*(exp p m)) p)
    [rewrite > Hcut1.
     apply divides_to_divides_ord_rem
      [assumption   
      |rewrite > (times_n_O O).
       apply lt_times
        [assumption|apply lt_O_exp.apply (prime_to_lt_O ? H1)]
      |assumption
      |assumption
      ]
    |unfold ord_rem.
     rewrite > (p_ord_exp1 p ? m n)
      [reflexivity
      |apply (prime_to_lt_O ? H1)
      |assumption
      |apply sym_times
      ]
    ]
  |elim (le_to_or_lt_eq ? ? (le_O_n j))
    [assumption
    |apply False_ind.
     apply (lt_to_not_eq ? ? H).
     elim H3.
     rewrite < H4 in H5.simplify in H5.
     elim (times_O_to_O ? ? H5)
      [apply sym_eq.assumption
      |apply False_ind.
       apply (not_le_Sn_n O).
       rewrite < H6 in \vdash (? ? %).
       apply lt_O_exp.
       elim H1.apply lt_to_le.assumption
      ]
    ]
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
apply (iter_p_gen_divides Z OZ Zplus n m p ? ? ? g)
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
apply (distributive_times_plus_iter_p_gen Z Zplus OZ Ztimes n z p f)
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


theorem sigma_p_knm: 
\forall g: nat \to Z.
\forall h2:nat \to nat \to nat.
\forall h11,h12:nat \to nat. 
\forall k,n,m.
\forall p1,p21:nat \to bool.
\forall p22:nat \to nat \to bool.
(\forall x. x < k \to p1 x = true \to 
p21 (h11 x) = true \land p22 (h11 x) (h12 x) = true
\land h2 (h11 x) (h12 x) = x 
\land (h11 x) < n \land (h12 x) < m) \to
(\forall i,j. i < n \to j < m \to p21 i = true \to p22 i j = true \to 
p1 (h2 i j) = true \land 
h11 (h2 i j) = i \land h12 (h2 i j) = j
\land h2 i j < k) \to
sigma_p k p1 g=
sigma_p n p21 (\lambda x:nat.sigma_p m (p22 x) (\lambda y. g (h2 x y))).
intros.
unfold sigma_p.
unfold sigma_p in \vdash (? ? ? (? ? ? ? (\lambda x:?.%) ? ?)).
apply iter_p_gen_knm
  [ apply symmetricZPlus
  |apply associative_Zplus
  | intro.
    apply (Zplus_z_OZ a)
  | exact h11
  | exact h12
  | assumption
  | assumption
  ]
qed.


theorem sigma_p2_eq: 
\forall g: nat \to nat \to Z.
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
sigma_p n1 p11 (\lambda x:nat .sigma_p m1 (p12 x) (\lambda y. g x y)) =
sigma_p n2 p21 (\lambda x:nat .sigma_p m2 (p22 x) (\lambda y. g (h11 x y) (h12 x y))).
intros.
unfold sigma_p.
unfold sigma_p in \vdash (? ? (? ? ? ? (\lambda x:?.%) ? ?) ?).
unfold sigma_p in \vdash (? ? ? (? ? ? ? (\lambda x:?.%) ? ?)).

apply(iter_p_gen_2_eq Z OZ Zplus ? ? ? g h11 h12 h21 h22 n1 m1 n2 m2 p11 p21 p12 p22)
[ apply symmetricZPlus
| apply associative_Zplus
| intro.
  apply (Zplus_z_OZ a)
| assumption
| assumption
]
qed.




(*





rewrite < sigma_p2'.
letin ha:= (\lambda x,y.(((h11 x y)*m1) + (h12 x y))).
letin ha12:= (\lambda x.(h21 (x/m1) (x \mod m1))).
letin ha22:= (\lambda x.(h22 (x/m1) (x \mod m1))).

apply (trans_eq ? ? 
(sigma_p n2 p21 (\lambda x:nat. sigma_p m2 (p22 x)
 (\lambda y:nat.(g (((h11 x y)*m1+(h12 x y))/m1) (((h11 x y)*m1+(h12 x y))\mod m1)) ) ) ))
[
  apply (sigma_p_knm (\lambda e. (g (e/m1) (e \mod m1))) ha ha12 ha22);intros
  [ elim (and_true ? ? H3).
    cut(O \lt m1)
    [ cut(x/m1 < n1)
      [ cut((x \mod m1) < m1)
        [ elim (H1 ? ? Hcut1 Hcut2 H4 H5).
          elim H6.clear H6.
          elim H8.clear H8.
          elim H6.clear H6.
          elim H8.clear H8.
          split
          [ split
            [ split
              [ split
                [ assumption
                | assumption
                ]
              | rewrite > H11.
                rewrite > H10.
                apply sym_eq.
                apply div_mod.
                assumption
              ]
            | assumption
            ]
          | assumption
          ]
        | apply lt_mod_m_m.
          assumption
        ]
      | apply (lt_times_n_to_lt m1)
        [ assumption
        | apply (le_to_lt_to_lt ? x)
          [ apply (eq_plus_to_le ? ? (x \mod m1)).
            apply div_mod.
            assumption
          | assumption
        ]
      ]  
    ]
    | apply not_le_to_lt.unfold.intro.
      generalize in match H2.
      apply (le_n_O_elim ? H6).
      rewrite < times_n_O.
      apply le_to_not_lt.
      apply le_O_n.              
    ]
  | elim (H ? ? H2 H3 H4 H5).
    elim H6.clear H6.
    elim H8.clear H8.
    elim H6.clear H6.
    elim H8.clear H8.
    cut(((h11 i j)*m1 + (h12 i j))/m1 = (h11 i j))
    [ cut(((h11 i j)*m1 + (h12 i j)) \mod m1 = (h12 i j))
      [ split
        [ split
          [ split
            [ apply true_to_true_to_andb_true
              [ rewrite > Hcut.
                assumption
              | rewrite > Hcut1.
                rewrite > Hcut.
                assumption
              ] 
            | rewrite > Hcut1.
              rewrite > Hcut.
              assumption
            ]
          | rewrite > Hcut1.
            rewrite > Hcut.
            assumption            
          ]
        | cut(O \lt m1)
          [ cut(O \lt n1)      
            [ apply (lt_to_le_to_lt ? ((h11 i j)*m1 + m1) )
              [ apply (lt_plus_r).
                assumption
              | rewrite > sym_plus.
                rewrite > (sym_times (h11 i j) m1).
                rewrite > times_n_Sm.
                rewrite > sym_times.
                apply (le_times_l).
                assumption  
              ]
            | apply not_le_to_lt.unfold.intro.
              generalize in match H9.
              apply (le_n_O_elim ? H8).       
              apply le_to_not_lt.
              apply le_O_n
            ]
          | apply not_le_to_lt.unfold.intro.
            generalize in match H7.
            apply (le_n_O_elim ? H8).       
            apply le_to_not_lt.
            apply le_O_n
          ]  
        ]
      | rewrite > (mod_plus_times m1 (h11 i j) (h12 i j)).
        reflexivity.
        assumption
      ]     
    | rewrite > (div_plus_times m1 (h11 i j) (h12 i j)).
      reflexivity.
      assumption
    ]
  ]
| apply (eq_sigma_p1)
  [ intros. reflexivity
  | intros.
    apply (eq_sigma_p1)
    [ intros. reflexivity
    | intros.
      rewrite > (div_plus_times)
      [ rewrite > (mod_plus_times)
        [ reflexivity
        | elim (H x x1 H2 H4 H3 H5).
          assumption
        ]
      | elim (H x x1 H2 H4 H3 H5).       
        assumption
      ]
    ]
  ]
]
qed.

rewrite < sigma_p2' in \vdash (? ? ? %).
apply sym_eq.
letin h := (\lambda x.(h11 (x/m2) (x\mod m2))*m1 + (h12 (x/m2) (x\mod m2))).
letin h1 := (\lambda x.(h21 (x/m1) (x\mod m1))*m2 + (h22 (x/m1) (x\mod m1))).
apply (trans_eq ? ? 
  (sigma_p (n2*m2) (\lambda x:nat.p21 (x/m2)\land p22 (x/m2) (x\mod m2))
  (\lambda x:nat.g ((h x)/m1) ((h x)\mod m1))))
  [clear h.clear h1.
   apply eq_sigma_p1
    [intros.reflexivity
    |intros.
     cut (O < m2)
      [cut (x/m2 < n2)
        [cut (x \mod m2 < m2)
          [elim (and_true ? ? H3).
           elim (H ? ? Hcut1 Hcut2 H4 H5).
           elim H6.clear H6.
           elim H8.clear H8.
           elim H6.clear H6.
           elim H8.clear H8.
           apply eq_f2
            [apply sym_eq.
             apply div_plus_times.
             assumption
            | 
              apply sym_eq.
              apply mod_plus_times.
              assumption
            ]
          |apply lt_mod_m_m.
           assumption
          ]
        |apply (lt_times_n_to_lt m2)
          [assumption
          |apply (le_to_lt_to_lt ? x)
            [apply (eq_plus_to_le ? ? (x \mod m2)).
             apply div_mod.
             assumption
            |assumption
            ]
          ]
        ]
      |apply not_le_to_lt.unfold.intro.
       generalize in match H2.
       apply (le_n_O_elim ? H4).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]      
    ]
  |apply (eq_sigma_p_gh ? h h1);intros
    [cut (O < m2)
      [cut (i/m2 < n2)
        [cut (i \mod m2 < m2)
          [elim (and_true ? ? H3).
           elim (H ? ? Hcut1 Hcut2 H4 H5).
           elim H6.clear H6.
           elim H8.clear H8.
           elim H6.clear H6.
           elim H8.clear H8.
           cut ((h11 (i/m2) (i\mod m2)*m1+h12 (i/m2) (i\mod m2))/m1 = 
                 h11 (i/m2) (i\mod m2))
            [cut ((h11 (i/m2) (i\mod m2)*m1+h12 (i/m2) (i\mod m2))\mod m1 =
                  h12 (i/m2) (i\mod m2))
              [rewrite > Hcut3.
               rewrite > Hcut4.
               rewrite > H6.
               rewrite > H12.
               reflexivity
              |apply mod_plus_times. 
               assumption
              ]
            |apply div_plus_times.
             assumption
            ]
          |apply lt_mod_m_m.
           assumption
          ]
        |apply (lt_times_n_to_lt m2)
          [assumption
          |apply (le_to_lt_to_lt ? i)
            [apply (eq_plus_to_le ? ? (i \mod m2)).
             apply div_mod.
             assumption
            |assumption
            ]
          ]
        ]
      |apply not_le_to_lt.unfold.intro.
       generalize in match H2.
       apply (le_n_O_elim ? H4).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]      
    |cut (O < m2)
      [cut (i/m2 < n2)
        [cut (i \mod m2 < m2)
          [elim (and_true ? ? H3).
           elim (H ? ? Hcut1 Hcut2 H4 H5).
           elim H6.clear H6.
           elim H8.clear H8.
           elim H6.clear H6.
           elim H8.clear H8.
           cut ((h11 (i/m2) (i\mod m2)*m1+h12 (i/m2) (i\mod m2))/m1 = 
                 h11 (i/m2) (i\mod m2))
            [cut ((h11 (i/m2) (i\mod m2)*m1+h12 (i/m2) (i\mod m2))\mod m1 =
                  h12 (i/m2) (i\mod m2))
              [rewrite > Hcut3.
               rewrite > Hcut4.
               rewrite > H10.
               rewrite > H11.
               apply sym_eq.
               apply div_mod.
               assumption
              |apply mod_plus_times. 
               assumption
              ]
            |apply div_plus_times.
             assumption
            ]
          |apply lt_mod_m_m.
           assumption
          ]
        |apply (lt_times_n_to_lt m2)
          [assumption
          |apply (le_to_lt_to_lt ? i)
            [apply (eq_plus_to_le ? ? (i \mod m2)).
             apply div_mod.
             assumption
            |assumption
            ]
          ]
        ]
      |apply not_le_to_lt.unfold.intro.
       generalize in match H2.
       apply (le_n_O_elim ? H4).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]      
    |cut (O < m2)
      [cut (i/m2 < n2)
        [cut (i \mod m2 < m2)
          [elim (and_true ? ? H3).
           elim (H ? ? Hcut1 Hcut2 H4 H5).
           elim H6.clear H6.
           elim H8.clear H8.
           elim H6.clear H6.
           elim H8.clear H8.
           apply lt_times_plus_times
            [assumption|assumption]
          |apply lt_mod_m_m.
           assumption
          ]
        |apply (lt_times_n_to_lt m2)
          [assumption
          |apply (le_to_lt_to_lt ? i)
            [apply (eq_plus_to_le ? ? (i \mod m2)).
             apply div_mod.
             assumption
            |assumption
            ]
          ]
        ]
      |apply not_le_to_lt.unfold.intro.
       generalize in match H2.
       apply (le_n_O_elim ? H4).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]
    |cut (O < m1)
      [cut (j/m1 < n1)
        [cut (j \mod m1 < m1)
          [elim (and_true ? ? H3).
           elim (H1 ? ? Hcut1 Hcut2 H4 H5).
           elim H6.clear H6.
           elim H8.clear H8.
           elim H6.clear H6.
           elim H8.clear H8.
           cut ((h21 (j/m1) (j\mod m1)*m2+h22 (j/m1) (j\mod m1))/m2 = 
                 h21 (j/m1) (j\mod m1))
            [cut ((h21 (j/m1) (j\mod m1)*m2+h22 (j/m1) (j\mod m1))\mod m2 =
                  h22 (j/m1) (j\mod m1))
              [rewrite > Hcut3.
               rewrite > Hcut4.
               rewrite > H6.
               rewrite > H12.
               reflexivity
              |apply mod_plus_times. 
               assumption
              ]
            |apply div_plus_times.
             assumption
            ]
          |apply lt_mod_m_m.
           assumption
          ] 
        |apply (lt_times_n_to_lt m1)
          [assumption
          |apply (le_to_lt_to_lt ? j)
            [apply (eq_plus_to_le ? ? (j \mod m1)).
             apply div_mod.
             assumption
            |assumption
            ]
          ]
        ]
      |apply not_le_to_lt.unfold.intro.
       generalize in match H2.
       apply (le_n_O_elim ? H4).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ] 
    |cut (O < m1)
      [cut (j/m1 < n1)
        [cut (j \mod m1 < m1)
          [elim (and_true ? ? H3).
           elim (H1 ? ? Hcut1 Hcut2 H4 H5).
           elim H6.clear H6.
           elim H8.clear H8.
           elim H6.clear H6.
           elim H8.clear H8.
           cut ((h21 (j/m1) (j\mod m1)*m2+h22 (j/m1) (j\mod m1))/m2 = 
                 h21 (j/m1) (j\mod m1))
            [cut ((h21 (j/m1) (j\mod m1)*m2+h22 (j/m1) (j\mod m1))\mod m2 =
                  h22 (j/m1) (j\mod m1))
              [rewrite > Hcut3.
               rewrite > Hcut4.               
               rewrite > H10.
               rewrite > H11.
               apply sym_eq.
               apply div_mod.
               assumption
              |apply mod_plus_times. 
               assumption
              ]
            |apply div_plus_times.
             assumption
            ]
          |apply lt_mod_m_m.
           assumption
          ] 
        |apply (lt_times_n_to_lt m1)
          [assumption
          |apply (le_to_lt_to_lt ? j)
            [apply (eq_plus_to_le ? ? (j \mod m1)).
             apply div_mod.
             assumption
            |assumption
            ]
          ]
        ]
      |apply not_le_to_lt.unfold.intro.
       generalize in match H2.
       apply (le_n_O_elim ? H4).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ] 
    |cut (O < m1)
      [cut (j/m1 < n1)
        [cut (j \mod m1 < m1)
          [elim (and_true ? ? H3).
           elim (H1 ? ? Hcut1 Hcut2 H4 H5).
           elim H6.clear H6.
           elim H8.clear H8.
           elim H6.clear H6.
           elim H8.clear H8.
           apply (lt_times_plus_times ? ? ? m2)
            [assumption|assumption]
          |apply lt_mod_m_m.
           assumption
          ] 
        |apply (lt_times_n_to_lt m1)
          [assumption
          |apply (le_to_lt_to_lt ? j)
            [apply (eq_plus_to_le ? ? (j \mod m1)).
             apply div_mod.
             assumption
            |assumption
            ]
          ]
        ]
      |apply not_le_to_lt.unfold.intro.
       generalize in match H2.
       apply (le_n_O_elim ? H4).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]
    ]
  ]
qed.
*)


