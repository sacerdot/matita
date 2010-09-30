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
include "nat/ord.ma".
include "nat/generic_iter_p.ma".
include "nat/count.ma".(*necessary just to use bool_to_nat and bool_to_nat_andb*)

(* sigma_p on nautral numbers is a specialization of sigma_p_gen *)
definition sigma_p: nat \to (nat \to bool) \to (nat \to nat) \to nat \def
\lambda n, p, g. (iter_p_gen n p nat g O plus).

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
apply true_to_iter_p_gen_Sn.
assumption.
qed.
   
theorem false_to_sigma_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to nat.
p n = false \to sigma_p (S n) p g = sigma_p n p g.
intros.
unfold sigma_p.
apply false_to_iter_p_gen_Sn.
assumption.
qed.  

theorem eq_sigma_p: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to nat.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros.
unfold sigma_p.
apply eq_iter_p_gen;
  assumption.
qed.

theorem eq_sigma_p1: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to nat.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to p1 x = true \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros.
unfold sigma_p.
apply eq_iter_p_gen1;
  assumption.
qed.

theorem sigma_p_false: 
\forall g: nat \to nat.\forall n.sigma_p n (\lambda x.false) g = O.
intros.
unfold sigma_p.
apply iter_p_gen_false.
qed.

theorem sigma_p_plus: \forall n,k:nat.\forall p:nat \to bool.
\forall g: nat \to nat.
sigma_p (k+n) p g 
= sigma_p k (\lambda x.p (x+n)) (\lambda x.g (x+n)) + sigma_p n p g.
intros.
unfold sigma_p.
apply (iter_p_gen_plusA nat n k p g O plus)
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
apply (false_to_eq_iter_p_gen);
  assumption.
qed.

theorem or_false_to_eq_sigma_p:
\forall n,m:nat.\forall p:nat \to bool.
\forall g: nat \to nat. 
n \le m \to (\forall i:nat. n \le i \to i < m \to p i = false \lor g i = O)
\to sigma_p m p g = sigma_p n p g.
intros.
unfold sigma_p.
apply or_false_eq_baseA_to_eq_iter_p_gen
  [intros.reflexivity
  |assumption
  |assumption
  ]
qed.

theorem bool_to_nat_to_eq_sigma_p:
\forall n:nat.\forall p1,p2:nat \to bool.
\forall g1,g2: nat \to nat. 
(\forall i:nat. 
bool_to_nat (p1 i)*(g1 i) = bool_to_nat (p2 i)*(g2 i)) 
\to sigma_p n p1 g1 = sigma_p n p2 g2.
intros.elim n
  [reflexivity
  |generalize in match (H n1).
   apply (bool_elim ? (p1 n1));intro
    [apply (bool_elim ? (p2 n1));intros
      [rewrite > true_to_sigma_p_Sn
        [rewrite > true_to_sigma_p_Sn
          [apply eq_f2
            [simplify in H4.
             rewrite > plus_n_O.
             rewrite > plus_n_O in ⊢ (? ? ? %).
             assumption
            |assumption
            ]
          |assumption
          ]
        |assumption
        ]
      |rewrite > true_to_sigma_p_Sn
        [rewrite > false_to_sigma_p_Sn
          [change in ⊢ (? ? ? %) with (O + sigma_p n1 p2 g2).
           apply eq_f2
            [simplify in H4.
             rewrite > plus_n_O.
             assumption
            |assumption
            ]
          |assumption
          ]
        |assumption
        ]
      ]
    |apply (bool_elim ? (p2 n1));intros
      [rewrite > false_to_sigma_p_Sn
        [rewrite > true_to_sigma_p_Sn
          [change in ⊢ (? ? % ?) with (O + sigma_p n1 p1 g1).
           apply eq_f2
            [simplify in H4.
             rewrite < plus_n_O in H4.
             assumption
            |assumption
            ]
          |assumption
          ]
        |assumption
        ]
      |rewrite > false_to_sigma_p_Sn
        [rewrite > false_to_sigma_p_Sn
          [assumption
          |assumption
          ]
        |assumption
        ]
      ]
    ]
  ]
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
apply (iter_p_gen2 n m p1 p2 nat g O plus)
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
  (\lambda x.andb (p1 (div x m)) (p2 (div x m) (mod x  m))) 
  (\lambda x.g (div x m) (mod x m)) =
sigma_p n p1 
  (\lambda x.sigma_p m (p2 x) (g x)).
intros.
unfold sigma_p.
apply (iter_p_gen2' n m p1 p2 nat g O plus)
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
apply (iter_p_gen_gi)
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
sigma_p n p1 (\lambda x.g(h x)) = sigma_p n1 p2 g.
intros.
unfold sigma_p.
apply (eq_iter_p_gen_gh nat O plus ? ? ? g h h1 n n1 p1 p2)
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

theorem eq_sigma_p_pred: 
\forall n,p,g. p O = true \to
sigma_p (S n) (\lambda i.p (pred i)) (\lambda i.g(pred i)) = 
plus (sigma_p n p g) (g O).
intros.
unfold sigma_p.
apply eq_iter_p_gen_pred
  [assumption
  |apply symmetricIntPlus
  |apply associative_plus
  |intros.apply sym_eq.apply plus_n_O
  ]
qed.

(* monotonicity *)
theorem le_sigma_p: 
\forall n:nat. \forall p:nat \to bool. \forall g1,g2:nat \to nat.
(\forall i. i < n \to p i = true \to g1 i \le g2 i ) \to 
sigma_p n p g1 \le sigma_p n p g2.
intros.
elim n in H ⊢ %
  [apply le_n.
  |apply (bool_elim ? (p n1));intros
    [rewrite > true_to_sigma_p_Sn
      [rewrite > true_to_sigma_p_Sn in ⊢ (? ? %)
        [apply le_plus
          [apply H1[apply le_n|assumption]
          |apply H.
           intros.
           apply H1[apply le_S.assumption|assumption]
          ]
        |assumption
        ]
      |assumption
      ]
    |rewrite > false_to_sigma_p_Sn
      [rewrite > false_to_sigma_p_Sn in ⊢ (? ? %)
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

(* a slightly more general result *)
theorem le_sigma_p1: 
\forall n:nat. \forall p1,p2:nat \to bool. \forall g1,g2:nat \to nat.
(\forall i. i < n \to 
bool_to_nat (p1 i)*(g1 i) \le bool_to_nat (p2 i)*g2 i) \to 
sigma_p n p1 g1 \le sigma_p n p2 g2.
intros.
elim n in H ⊢ %
  [apply le_n.
  |apply (bool_elim ? (p1 n1));intros
    [apply (bool_elim ? (p2 n1));intros
      [rewrite > true_to_sigma_p_Sn
        [rewrite > true_to_sigma_p_Sn in ⊢ (? ? %)
          [apply le_plus
            [lapply (H1 n1) as H5
              [rewrite > H2 in H5.
               rewrite > H3 in H5.
               simplify in H5.
               rewrite < plus_n_O in H5.
               rewrite < plus_n_O in H5.
               assumption
              |apply le_S_S.apply le_n
              ]
            |apply H.intros.
             apply H1.apply le_S.assumption
            ]
          |assumption
          ]
        |assumption
        ]
      |rewrite > true_to_sigma_p_Sn
        [rewrite > false_to_sigma_p_Sn in ⊢ (? ? %)
          [change in ⊢ (? ? %) with (O + sigma_p n1 p2 g2).
           apply le_plus
            [lapply (H1 n1) as H5
              [rewrite > H2 in H5.
               rewrite > H3 in H5.
               simplify in H5.
               rewrite < plus_n_O in H5.
               assumption
              |apply le_S_S.apply le_n
              ]
            |apply H.intros.
             apply H1.apply le_S.assumption
            ]
          |assumption
          ]
        |assumption
        ]
      ]
    |apply (bool_elim ? (p2 n1));intros
      [rewrite > false_to_sigma_p_Sn
        [rewrite > true_to_sigma_p_Sn in ⊢ (? ? %)
          [change in ⊢ (? % ?) with (O + sigma_p n1 p1 g1).
           apply le_plus
            [lapply (H1 n1) as H5
              [rewrite > H2 in H5.
               rewrite > H3 in H5.
               simplify in H5.
               rewrite < plus_n_O in H5.
               assumption
              |apply le_S_S.apply le_n
              ]
            |apply H.intros.
             apply H1.apply le_S.assumption
            ]
          |assumption
          ]
        |assumption
        ]
      |rewrite > false_to_sigma_p_Sn
        [rewrite > false_to_sigma_p_Sn in ⊢ (? ? %)
          [apply H.intros.
           apply H1.apply le_S.assumption
          |assumption
          ]
        |assumption
        ]
      ]
    ]
  ]
qed.

theorem lt_sigma_p: 
\forall n:nat. \forall p:nat \to bool. \forall g1,g2:nat \to nat.
(\forall i. i < n \to p i = true \to g1 i \le g2 i ) \to
(\exists i. i < n \and (p i = true) \and (g1 i < g2 i)) \to
sigma_p n p g1 < sigma_p n p g2.
intros 4.
elim n
  [elim H1.clear H1.
   elim H2.clear H2.
   elim H1.clear H1.
   apply False_ind.
   apply (lt_to_not_le ? ? H2).
   apply le_O_n
  |apply (bool_elim ? (p n1));intros
    [apply (bool_elim ? (leb (S (g1 n1)) (g2 n1)));intros
      [rewrite > true_to_sigma_p_Sn
        [rewrite > true_to_sigma_p_Sn in ⊢ (? ? %)
          [change with 
           (S (g1 n1)+sigma_p n1 p g1 \le g2 n1+sigma_p n1 p g2).
           apply le_plus
            [apply leb_true_to_le.assumption
            |apply le_sigma_p.intros.
             apply H1
              [apply lt_to_le.apply le_S_S.assumption
              |assumption
              ]
            ]
          |assumption
          ]
        |assumption
        ]
      |rewrite > true_to_sigma_p_Sn
        [rewrite > true_to_sigma_p_Sn in ⊢ (? ? %)
          [unfold lt.
           rewrite > plus_n_Sm.
           apply le_plus
            [apply H1
              [apply le_n
              |assumption
              ]
            |apply H
              [intros.apply H1
                [apply lt_to_le.apply le_S_S.assumption
                |assumption
                ]
              |elim H2.clear H2.
               elim H5.clear H5.
               elim H2.clear H2.
               apply (ex_intro ? ? a).
               split
                [split
                  [elim (le_to_or_lt_eq a n1)
                    [assumption
                    |absurd (g1 a < g2 a)
                      [assumption
                      |apply leb_false_to_not_le.
                       rewrite > H2.
                       assumption
                      ]
                    |apply le_S_S_to_le.
                     assumption
                    ]
                  |assumption
                  ]
                |assumption
                ]
              ]
            ]
          |assumption
          ]
        |assumption
        ]
      ]
    |rewrite > false_to_sigma_p_Sn
      [rewrite > false_to_sigma_p_Sn in ⊢ (? ? %)
        [apply H
          [intros.apply H1
            [apply lt_to_le.apply le_S_S.assumption
            |assumption
            ]
          |elim H2.clear H2.
           elim H4.clear H4.
           elim H2.clear H2.
           apply (ex_intro ? ? a).
           split
            [split
              [elim (le_to_or_lt_eq a n1)
                [assumption
                |apply False_ind.
                 apply not_eq_true_false.
                 rewrite < H6.
                 rewrite < H3.
                 rewrite < H2. 
                 reflexivity
                |apply le_S_S_to_le.
                 assumption
                ]
              |assumption
              ]
            |assumption
            ]
          ]
        |assumption
        ]
      |assumption
      ]
    ]
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
apply (iter_p_gen_divides nat O plus n m p ? ? ? g)
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
apply (distributive_times_plus_iter_p_gen nat plus O times n k p g)
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

(*some properties of sigma_p invoked with an "always true" predicate (in this 
  way sigma_p just counts the elements, without doing any control) or with
  the nat \to nat function which always returns (S O).
  It 's not easily possible proving these theorems in a general form 
  in generic_sigma_p.ma
 *)

theorem sigma_p_true: \forall n:nat.
(sigma_p n (\lambda x.true) (\lambda x.S O)) = n.
intros.
elim n
[ simplify.
  reflexivity
| rewrite > (true_to_sigma_p_Sn n1 (\lambda x:nat.true) (\lambda x:nat.S O))
  [ rewrite > H.
    simplify.
    reflexivity
  | reflexivity 
  ]
]
qed.

theorem sigma_P_SO_to_sigma_p_true: \forall n:nat. \forall g:nat \to bool.
sigma_p n g (\lambda n:nat. (S O)) = 
sigma_p n (\lambda x:nat.true) (\lambda i:nat.bool_to_nat (g i)).
intros.
elim n
[ simplify.
  reflexivity
| cut ((g n1) = true \lor (g n1) = false)
  [ rewrite > true_to_sigma_p_Sn in \vdash (? ? ? %)
    [ elim Hcut
      [ rewrite > H1.
        rewrite > true_to_sigma_p_Sn in \vdash (? ? % ?)
        [ simplify.
          apply eq_f.
          assumption
        | assumption
        ]
      | rewrite > H1.
        rewrite > false_to_sigma_p_Sn in \vdash (? ? % ?)
        [ simplify.
          assumption
        | assumption
        ]
      ]
    | reflexivity
    ]
  | elim (g n1)
    [ left.
      reflexivity
    | right.
      reflexivity
    ]
  ]
]
qed.

(* I introduce an equivalence in the form map_iter_i in order to use
 * the existing result about permutation in that part of the library.
 *) 
 
theorem eq_map_iter_i_sigma_p_alwaysTrue:  \forall n:nat.\forall g:nat \to nat. 
map_iter_i n g plus O = sigma_p (S n) (\lambda c:nat.true) g.
intros.
elim n
[ simplify.
  rewrite < plus_n_O.
  reflexivity
| rewrite > true_to_sigma_p_Sn
  [ simplify in \vdash (? ? % ?).
    rewrite < plus_n_O.
    apply eq_f.
    assumption
  | reflexivity
  ]
]
qed.

theorem sigma_p_plus_1: \forall n:nat. \forall f,g:nat \to nat.
\forall p.
sigma_p n p (\lambda a:nat.(f a) + (g a)) = 
sigma_p n p f + sigma_p n p g.
intros.
elim n
[ simplify.
  reflexivity
| apply (bool_elim ? (p n1)); intro;
  [ rewrite > true_to_sigma_p_Sn
    [ rewrite > (true_to_sigma_p_Sn n1 p f)
      [ rewrite > (true_to_sigma_p_Sn n1 p g)
        [ rewrite > assoc_plus in \vdash (? ? ? %).
          rewrite < assoc_plus in \vdash (? ? ? (? ? %)).
          rewrite < sym_plus in \vdash (? ? ? (? ? (? % ?))).
          rewrite > assoc_plus in \vdash (? ? ? (? ? %)).
          rewrite < assoc_plus in \vdash (? ? ? %).
          apply eq_f.
          assumption]]]
   assumption
 | rewrite > false_to_sigma_p_Sn
    [ rewrite > (false_to_sigma_p_Sn n1 p f)
      [ rewrite > (false_to_sigma_p_Sn n1 p g)
        [assumption]]]
   assumption
]]
qed.

theorem eq_sigma_p_sigma_p_times1 : \forall n,m:nat.\forall f:nat \to nat.
sigma_p (n*m) (\lambda x:nat.true) f =
sigma_p m (\lambda x:nat.true) 
    (\lambda a.(sigma_p n (\lambda x:nat.true) (\lambda b.f (b*m + a)))).
intro.
elim n
[ simplify.
  elim m
  [ simplify.
    reflexivity
  | rewrite > true_to_sigma_p_Sn
    [ rewrite < H.
      reflexivity
    | reflexivity
    ]
  ]
| change in \vdash (? ? ? (? ? ? (\lambda a:?.%))) with ((f ((n1*m)+a)) + 
  (sigma_p n1 (\lambda x:nat.true) (\lambda b:nat.f (b*m +a)))).
  rewrite > sigma_p_plus_1 in \vdash (? ? ? %).
  rewrite > (sym_times (S n1) m).
  rewrite < (times_n_Sm m  n1).
  rewrite > sigma_p_plus in \vdash (? ? % ?).
  apply eq_f2
  [ rewrite < (sym_times m n1).
    apply eq_sigma_p
    [ intros. 
      reflexivity
    | intros.
      rewrite < (sym_plus ? (m * n1)).
      reflexivity
    ]
  | rewrite > (sym_times m n1).
    apply H
  ]
]
qed.

theorem eq_sigma_p_sigma_p_times2 : \forall n,m:nat.\forall f:nat \to nat.
sigma_p (n *m) (\lambda c:nat.true) f =
sigma_p  n (\lambda c:nat.true) 
  (\lambda a.(sigma_p m (\lambda c:nat.true) (\lambda b:nat.f (b* n + a)))).
intros.
rewrite > sym_times.
apply eq_sigma_p_sigma_p_times1.
qed.

theorem sigma_p_times:\forall n,m:nat. 
\forall f,f1,f2:nat \to bool.
\forall g:nat \to nat \to nat. 
\forall g1,g2: nat \to nat.
(\forall a,b:nat. a < (S n) \to b < (S m) \to (g b a) < (S n)*(S m)) \to
(\forall a,b:nat. a < (S n) \to b < (S m) \to (g1 (g b a)) = a) \to
(\forall a,b:nat. a < (S n) \to b < (S m) \to (g2 (g b a)) = b) \to
(\forall a,b:nat. a < (S n) \to b < (S m) \to f (g b a) = andb (f2 b) (f1 a)) \to
(sigma_p ((S n) * (S m)) f (\lambda c:nat.(S O))) = 
sigma_p (S n) f1 (\lambda c:nat.(S O)) * sigma_p (S m) f2 (\lambda c:nat.(S O)). 
intros.

rewrite > (sigma_P_SO_to_sigma_p_true ).
rewrite > (S_pred ((S n)*(S m))) in \vdash (? ? (? % ? ?) ?)
[ rewrite < (eq_map_iter_i_sigma_p_alwaysTrue (pred ((S n)* (S m)))).
  rewrite > (permut_to_eq_map_iter_i plus assoc_plus sym_plus ? ? ? 
           (\lambda i.g (div i (S n)) (mod i (S n))))
  [ rewrite > eq_map_iter_i_sigma_p_alwaysTrue.
    rewrite < S_pred
    [ rewrite > eq_sigma_p_sigma_p_times2.
      apply (trans_eq ? ? (sigma_p (S n)  (\lambda c:nat.true) 
        (\lambda a. sigma_p (S m) (\lambda c:nat.true) 
                (\lambda b.(bool_to_nat (f2 b))*(bool_to_nat (f1 a))))))
      [ apply eq_sigma_p;intros
        [ reflexivity
        | apply eq_sigma_p;intros
          [ reflexivity
          | 
            rewrite > (div_mod_spec_to_eq (x1*(S n) + x) (S n) ((x1*(S n) + x)/(S n)) 
                                                  ((x1*(S n) + x) \mod (S n)) x1 x)
            [ rewrite > (div_mod_spec_to_eq2 (x1*(S n) + x) (S n) ((x1*(S n) + x)/(S n)) 
                                                  ((x1*(S n) + x) \mod (S n)) x1 x)
              [ rewrite > H3
                [ apply bool_to_nat_andb
                | assumption
                | assumption
                ]
              | apply div_mod_spec_div_mod.
                apply lt_O_S
              | constructor 1
                [ assumption
                | reflexivity
                ]
              ]
            | apply div_mod_spec_div_mod.
              apply lt_O_S
            | constructor 1
              [ assumption
              | reflexivity
              ]
            ]
          ]
        ]
      | apply (trans_eq ? ? 
         (sigma_p (S n) (\lambda c:nat.true) (\lambda n.((bool_to_nat (f1 n)) *
         (sigma_p (S m) (\lambda c:nat.true) (\lambda n.bool_to_nat (f2 n)))))))
        [ apply eq_sigma_p;intros
          [ reflexivity
          | rewrite > distributive_times_plus_sigma_p.
            apply eq_sigma_p;intros
            [ reflexivity
            | rewrite > sym_times. 
              reflexivity
            ]
          ]
        | apply sym_eq.
          rewrite > sigma_P_SO_to_sigma_p_true.
          rewrite > sigma_P_SO_to_sigma_p_true in \vdash (? ? (? ? %) ?).
          rewrite > sym_times. 
          rewrite > distributive_times_plus_sigma_p.
          apply eq_sigma_p;intros
          [ reflexivity
          | rewrite > distributive_times_plus_sigma_p.
            rewrite < sym_times.
            rewrite > distributive_times_plus_sigma_p.
            apply eq_sigma_p;
              intros; reflexivity            
          ]
        ]
      ]
    | apply lt_O_times_S_S
    ]
    
  | unfold permut.
    split
    [ intros.
      rewrite < plus_n_O.
      apply le_S_S_to_le.
      rewrite < S_pred in \vdash (? ? %)
      [ change with ((g (i/(S n)) (i \mod (S n))) \lt (S n)*(S m)).
        apply H
        [ apply lt_mod_m_m.
          unfold lt. 
          apply le_S_S.
          apply le_O_n 
        | apply (lt_times_to_lt_l n).
          apply (le_to_lt_to_lt ? i)
          [ rewrite > (div_mod i (S n)) in \vdash (? ? %)
            [ rewrite > sym_plus.
              apply le_plus_n
            | unfold lt. 
              apply le_S_S.
              apply le_O_n
            ]
          | unfold lt.
            rewrite > S_pred in \vdash (? ? %)
            [ apply le_S_S.
              rewrite > plus_n_O in \vdash (? ? %).
              rewrite > sym_times. 
              assumption
            | apply lt_O_times_S_S
            ]
          ]
        ]
      | apply lt_O_times_S_S
      ]
    | rewrite < plus_n_O.
      unfold injn.
      intros.
      cut (i < (S n)*(S m))
      [ cut (j < (S n)*(S m))
        [ cut ((i \mod (S n)) < (S n))
          [ cut ((i/(S n)) < (S m))
            [ cut ((j \mod (S n)) < (S n))
              [ cut ((j/(S n)) < (S m))
                [ rewrite > (div_mod i (S n))
                  [ rewrite > (div_mod j (S n))
                    [ rewrite < (H1 (i \mod (S n)) (i/(S n)) Hcut2 Hcut3).
                      rewrite < (H2 (i \mod (S n)) (i/(S n)) Hcut2 Hcut3) in \vdash (? ? (? % ?) ?).
                      rewrite < (H1 (j \mod (S n)) (j/(S n)) Hcut4 Hcut5).
                      rewrite < (H2 (j \mod (S n)) (j/(S n)) Hcut4 Hcut5) in \vdash (? ? ? (? % ?)).
                      rewrite > H6.
                      reflexivity
                    | unfold lt.
                      apply le_S_S.
                      apply le_O_n
                    ]
                  | unfold lt. 
                    apply le_S_S.
                    apply le_O_n
                  ]
                | apply (lt_times_to_lt_l n).
                  apply (le_to_lt_to_lt ? j)
                  [ rewrite > (div_mod j (S n)) in \vdash (? ? %)
                    [ rewrite > sym_plus.
                      apply le_plus_n
                    | unfold lt. apply le_S_S.
                      apply le_O_n
                    ]
                  | rewrite < sym_times. 
                    assumption                    
                  ]
                ]
              | apply lt_mod_m_m.
                unfold lt. 
                apply le_S_S.
                apply le_O_n
              ]
            | apply (lt_times_to_lt_l n).
              apply (le_to_lt_to_lt ? i)
              [ rewrite > (div_mod i (S n)) in \vdash (? ? %)
                [ rewrite > sym_plus.
                  apply le_plus_n
                | unfold lt. 
                  apply le_S_S.
                  apply le_O_n
                ]
              | rewrite < sym_times. 
                assumption
              ]
            ]
          | apply lt_mod_m_m.
            unfold lt. 
            apply le_S_S.
            apply le_O_n
          ]
        | unfold lt.
          rewrite > S_pred in \vdash (? ? %)
          [ apply le_S_S.
            assumption
          | apply lt_O_times_S_S 
          ]
        ]
      | unfold lt.
        rewrite > S_pred in \vdash (? ? %)
        [ apply le_S_S.
          assumption
        | apply lt_O_times_S_S 
        ]
      ]
    ]
  | intros.
    apply False_ind.
    apply (not_le_Sn_O m1 H4)
  ]
| apply lt_O_times_S_S
]
qed.

theorem sigma_p_knm: 
\forall g: nat \to nat.
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
  [apply symmetricIntPlus
  |apply associative_plus
  |intro.rewrite < plus_n_O.reflexivity
  |exact h11
  |exact h12
  |assumption
  |assumption
  ]
qed.
  
  
theorem sigma_p2_eq: 
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
sigma_p n1 p11 (\lambda x:nat .sigma_p m1 (p12 x) (\lambda y. g x y)) =
sigma_p n2 p21 (\lambda x:nat .sigma_p m2 (p22 x) (\lambda y. g (h11 x y) (h12 x y))).
intros.
unfold sigma_p.
unfold sigma_p in \vdash (? ? (? ? ? ? (\lambda x:?.%) ? ?) ?).
unfold sigma_p in \vdash (? ? ? (? ? ? ? (\lambda x:?.%) ? ?)).

apply(iter_p_gen_2_eq nat O plus ? ? ? g h11 h12 h21 h22 n1 m1 n2 m2 p11 p21 p12 p22)
[ apply symmetricIntPlus
| apply associative_plus
| intro.
  rewrite < (plus_n_O).
  reflexivity
| assumption
| assumption
]
qed.

theorem sigma_p_sigma_p: 
\forall g: nat \to nat \to nat.
\forall n,m.
\forall p11,p21:nat \to bool.
\forall p12,p22:nat \to nat \to bool.
(\forall x,y. x < n \to y < m \to 
 (p11 x \land p12 x y) = (p21 y \land p22 y x)) \to
sigma_p n p11 (\lambda x:nat.sigma_p m (p12 x) (\lambda y. g x y)) =
sigma_p m p21 (\lambda y:nat.sigma_p n (p22 y) (\lambda x. g x y)).
intros.
unfold sigma_p.unfold sigma_p.
apply (iter_p_gen_iter_p_gen ? ? ? sym_plus assoc_plus)
  [intros.apply sym_eq.apply plus_n_O.
  |assumption
  ]
qed.