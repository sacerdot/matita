(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

set "baseuri" "cic:/matita/nat/generic_sigma_p.ma".

include "nat/primes.ma".
include "nat/ord.ma".



(*a generic definition of summatory indexed over natural numbers:
 * n:N is the advanced end in the range of the sommatory 
 * p: N -> bool is a predicate. if (p i) = true, then (g i) is summed, else it isn't 
 * A is the type of the elements of the sum.
 * g:nat -> A, is the function which associates the nth element of the sum to the nth natural numbers 
 * baseA (of type A) is the neutral element of A for plusA operation
 * plusA: A -> A -> A is the sum over elements in A. 
 *)
let rec sigma_p_gen (n:nat) (p: nat \to bool) (A:Type) (g: nat \to A) 
   (baseA: A) (plusA: A \to A \to A)  \def
  match n with
   [ O \Rightarrow baseA
   | (S k) \Rightarrow 
      match p k with
      [true \Rightarrow (plusA (g k) (sigma_p_gen k p A g baseA plusA))
      |false \Rightarrow sigma_p_gen k p A g baseA plusA]
   ].
   
theorem true_to_sigma_p_Sn_gen: 
\forall n:nat. \forall p:nat \to bool. \forall A:Type. \forall g:nat \to A.
\forall baseA:A. \forall plusA: A \to A \to A.
p n = true \to sigma_p_gen (S n) p A g baseA plusA = 
(plusA (g n) (sigma_p_gen n p A g baseA plusA)).
intros.
simplify.
rewrite > H.
reflexivity.
qed.



theorem false_to_sigma_p_Sn_gen: 
\forall n:nat. \forall p:nat \to bool. \forall A:Type. \forall g:nat \to A.
\forall baseA:A. \forall plusA: A \to A \to A.
p n = false \to sigma_p_gen (S n) p A g baseA plusA = sigma_p_gen n p A g baseA plusA.
intros.
simplify.
rewrite > H.
reflexivity.
qed.


theorem eq_sigma_p_gen: \forall p1,p2:nat \to bool. \forall A:Type.
\forall g1,g2: nat \to A. \forall baseA: A. 
\forall plusA: A \to A \to A. \forall n:nat.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to g1 x = g2 x) \to
sigma_p_gen n p1 A g1 baseA plusA = sigma_p_gen n p2 A g2 baseA plusA.
intros 8.
elim n
[ reflexivity
| apply (bool_elim ? (p1 n1))
  [ intro.
    rewrite > (true_to_sigma_p_Sn_gen ? ? ? ? ? ? H3).
    rewrite > true_to_sigma_p_Sn_gen     
    [ apply eq_f2
      [ apply H2.apply le_n.
      | apply H
        [ intros.apply H1.apply le_S.assumption
        | intros.apply H2.apply le_S.assumption
        ]
      ]
    | rewrite < H3.apply sym_eq.apply H1.apply le_n
    ]
  | intro.
    rewrite > (false_to_sigma_p_Sn_gen ? ? ? ? ? ? H3).
    rewrite > false_to_sigma_p_Sn_gen
    [ apply H
      [ intros.apply H1.apply le_S.assumption
      | intros.apply H2.apply le_S.assumption
      ]
    | rewrite < H3.apply sym_eq.apply H1.apply le_n
    ]
  ]
]
qed.

theorem eq_sigma_p1_gen: \forall p1,p2:nat \to bool. \forall A:Type.
\forall g1,g2: nat \to A. \forall baseA: A. 
\forall plusA: A \to A \to A.\forall n:nat.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to p1 x = true \to g1 x = g2 x) \to
sigma_p_gen n p1 A g1 baseA plusA = sigma_p_gen n p2 A g2 baseA plusA.
intros 8.
elim n
[ reflexivity
| apply (bool_elim ? (p1 n1))
  [ intro.
    rewrite > (true_to_sigma_p_Sn_gen ? ? ? ? ? ? H3).
    rewrite > true_to_sigma_p_Sn_gen
    [ apply eq_f2
      [ apply H2
        [ apply le_n
        | assumption
        ]
      | apply H
        [ intros.apply H1.apply le_S.assumption
        | intros.apply H2
          [ apply le_S.assumption
          | assumption
          ]
        ]
      ]
    | rewrite < H3.
      apply sym_eq.apply H1.apply le_n
    ]
  | intro.
    rewrite > (false_to_sigma_p_Sn_gen ? ? ? ? ? ? H3).
    rewrite > false_to_sigma_p_Sn_gen
    [ apply H
      [ intros.apply H1.apply le_S.assumption
      | intros.apply H2
        [ apply le_S.assumption
        | assumption
        ]
      ]
    | rewrite < H3.apply sym_eq.
      apply H1.apply le_n
    ]
  ]
]
qed.

theorem sigma_p_false_gen: \forall A:Type. \forall g: nat \to A. \forall baseA:A.
\forall plusA: A \to A \to A. \forall n.
sigma_p_gen n (\lambda x.false) A g baseA plusA = baseA.
intros.
elim n
[ reflexivity
| simplify.
  assumption
]
qed.

theorem sigma_p_plusA_gen: \forall A:Type. \forall n,k:nat.\forall p:nat \to bool.
\forall g: nat \to A. \forall baseA:A. \forall plusA: A \to A \to A.
(symmetric A plusA) \to (\forall a:A. (plusA a baseA) = a) \to (associative A plusA)
\to
sigma_p_gen (k + n) p A g baseA plusA 
= (plusA (sigma_p_gen k (\lambda x.p (x+n)) A (\lambda x.g (x+n)) baseA plusA)
         (sigma_p_gen n p A g baseA plusA)).
intros.

elim k
[ rewrite < (plus_n_O n).
  simplify.
  rewrite > H in \vdash (? ? ? %).
  rewrite > (H1 ?).
  reflexivity
| apply (bool_elim ? (p (n1+n)))
  [ intro.     
    rewrite > (true_to_sigma_p_Sn_gen ? ? ? ? ? ? H4).
    rewrite > (true_to_sigma_p_Sn_gen n1 (\lambda x.p (x+n)) ? ? ? ? H4).
    rewrite > (H2 (g (n1 + n)) ? ?).
    rewrite < H3.
    reflexivity
  | intro.
    rewrite > (false_to_sigma_p_Sn_gen ? ? ? ? ? ? H4).
    rewrite > (false_to_sigma_p_Sn_gen n1 (\lambda x.p (x+n)) ? ? ? ? H4).
    assumption
  ]
]
qed.

theorem false_to_eq_sigma_p_gen: \forall A:Type. \forall n,m:nat.\forall p:nat \to bool.
\forall g: nat \to A. \forall baseA:A. \forall plusA: A \to A \to A. 
n \le m \to (\forall i:nat. n \le i \to i < m \to p i = false)
\to sigma_p_gen m p A g baseA plusA = sigma_p_gen n p A g baseA plusA.
intros 8.
elim H
[ reflexivity
| simplify.
  rewrite > H3
  [ simplify.
    apply H2.
    intros.
    apply H3
    [ apply H4
    | apply le_S.
      assumption
    ]
  | assumption
  |apply le_n
  ]
]
qed.

theorem sigma_p2_gen : 
\forall n,m:nat.
\forall p1,p2:nat \to bool.
\forall A:Type.
\forall g: nat \to nat \to A.
\forall baseA: A.
\forall plusA: A \to A \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a)
\to
sigma_p_gen (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (mod x m)))
  A 
  (\lambda x.g (div x m) (mod x m)) 
  baseA
  plusA  =
sigma_p_gen n p1 A
  (\lambda x.sigma_p_gen m p2 A (g x) baseA plusA)
  baseA plusA.
intros.
elim n
[ simplify.
  reflexivity
| apply (bool_elim ? (p1 n1))
  [ intro.
    rewrite > (true_to_sigma_p_Sn_gen ? ? ? ? ? ? H4).
    simplify in \vdash (? ? (? % ? ? ? ? ?) ?).
    rewrite > sigma_p_plusA_gen
    [ rewrite < H3.
      apply eq_f2
      [ apply eq_sigma_p_gen
        [ intros.
          rewrite > sym_plus.
          rewrite > (div_plus_times ? ? ? H5).
          rewrite > (mod_plus_times ? ? ? H5).
          rewrite > H4.
          simplify.
          reflexivity
        | intros.
          rewrite > sym_plus.
          rewrite > (div_plus_times ? ? ? H5).
          rewrite > (mod_plus_times ? ? ? H5).
          rewrite > H4.
          simplify.reflexivity.   
        ]
      | reflexivity
      ]
    | assumption
    | assumption
    | assumption
    ]
  | intro.
    rewrite > (false_to_sigma_p_Sn_gen ? ? ? ? ? ? H4).
    simplify in \vdash (? ? (? % ? ? ? ? ?) ?).
    rewrite > sigma_p_plusA_gen
    [ rewrite > H3.
      apply (trans_eq ? ? (plusA baseA
           (sigma_p_gen n1 p1 A (\lambda x:nat.sigma_p_gen m p2 A (g x) baseA plusA) baseA plusA )))
      [ apply eq_f2
        [ rewrite > (eq_sigma_p_gen ? (\lambda x.false) A ? (\lambda x:nat.g ((x+n1*m)/m) ((x+n1*m)\mod m)))
          [ apply sigma_p_false_gen
          | intros.
            rewrite > sym_plus.
            rewrite > (div_plus_times ? ? ? H5).
            rewrite > (mod_plus_times ? ? ? H5).
            rewrite > H4.
            simplify.reflexivity
          | intros.reflexivity.
          ]
        | reflexivity
        ]
      | rewrite < H.
        rewrite > H2.
        reflexivity.  
      ]
    | assumption
    | assumption
    | assumption
    ]
  ]
]
qed.


theorem sigma_p2_gen': 
\forall n,m:nat.
\forall p1: nat \to bool.
\forall p2: nat \to nat \to bool.
\forall A:Type.
\forall g: nat \to nat \to A.
\forall baseA: A.
\forall plusA: A \to A \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a)
\to
sigma_p_gen (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (div x m)(mod x m)))
  A 
  (\lambda x.g (div x m) (mod x m)) 
  baseA
  plusA  =
sigma_p_gen n p1 A
  (\lambda x.sigma_p_gen m (p2 x) A (g x) baseA plusA)
  baseA plusA.
intros.
elim n
[ simplify.
  reflexivity
| apply (bool_elim ? (p1 n1))
  [ intro.
    rewrite > (true_to_sigma_p_Sn_gen ? ? ? ? ? ? H4).
    simplify in \vdash (? ? (? % ? ? ? ? ?) ?).
    rewrite > sigma_p_plusA_gen
    [ rewrite < H3.
      apply eq_f2
      [ apply eq_sigma_p_gen
        [ intros.
          rewrite > sym_plus.
          rewrite > (div_plus_times ? ? ? H5).
          rewrite > (mod_plus_times ? ? ? H5).
          rewrite > H4.
          simplify.
          reflexivity
        | intros.
          rewrite > sym_plus.
          rewrite > (div_plus_times ? ? ? H5).
          rewrite > (mod_plus_times ? ? ? H5).
          rewrite > H4.
          simplify.reflexivity.   
        ]
      | reflexivity
      ]
    | assumption
    | assumption
    | assumption
    ]
  | intro.
    rewrite > (false_to_sigma_p_Sn_gen ? ? ? ? ? ? H4).
    simplify in \vdash (? ? (? % ? ? ? ? ?) ?).
    rewrite > sigma_p_plusA_gen
    [ rewrite > H3.
      apply (trans_eq ? ? (plusA baseA
           (sigma_p_gen n1 p1 A (\lambda x:nat.sigma_p_gen m (p2 x) A (g x) baseA plusA) baseA plusA )))
      [ apply eq_f2
        [ rewrite > (eq_sigma_p_gen ? (\lambda x.false) A ? (\lambda x:nat.g ((x+n1*m)/m) ((x+n1*m)\mod m)))
          [ apply sigma_p_false_gen
          | intros.
            rewrite > sym_plus.
            rewrite > (div_plus_times ? ? ? H5).
            rewrite > (mod_plus_times ? ? ? H5).
            rewrite > H4.
            simplify.reflexivity
          | intros.reflexivity.
          ]
        | reflexivity
        ]
      | rewrite < H.
        rewrite > H2.
        reflexivity.  
      ]
    | assumption
    | assumption
    | assumption
    ]
  ]
]
qed.

lemma sigma_p_gi_gen: 
\forall A:Type.
\forall g: nat \to A.
\forall baseA:A.
\forall plusA: A \to A \to A.
\forall n,i:nat.
\forall p:nat \to bool.
(symmetric A plusA) \to  (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a) 
  \to 
  
i < n \to p i = true \to
(sigma_p_gen n p A g baseA plusA) = 
(plusA (g i) (sigma_p_gen n (\lambda x:nat. andb (p x) (notb (eqb x i))) A g baseA plusA)).
intros 5.
elim n
[ apply False_ind.
  apply (not_le_Sn_O i).
  assumption
| apply (bool_elim ? (p n1));intro
  [ elim (le_to_or_lt_eq i n1)
    [ rewrite > true_to_sigma_p_Sn_gen
      [ rewrite > true_to_sigma_p_Sn_gen
        [ rewrite < (H2 (g i) ? ?).
          rewrite > (H1 (g i) (g n1)).
          rewrite > (H2 (g n1) ? ?).
          apply eq_f2
          [ reflexivity
          | apply H
            [ assumption
            | assumption
            | assumption 
            | assumption
            | assumption
            ]
          ]
        | rewrite > H6.simplify.
          change with (notb (eqb n1 i) = notb false).
          apply eq_f.
          apply not_eq_to_eqb_false.
          unfold Not.intro.
          apply (lt_to_not_eq ? ? H7).
          apply sym_eq.assumption
        ]
      | assumption
      ]
    | rewrite > true_to_sigma_p_Sn_gen
      [ rewrite > H7.
        apply eq_f2
        [ reflexivity
        | rewrite > false_to_sigma_p_Sn_gen
          [ apply eq_sigma_p_gen
            [ intros.
              elim (p x)
              [ simplify.
                change with (notb false = notb (eqb x n1)).
                apply eq_f.
                apply sym_eq. 
                apply not_eq_to_eqb_false.
                apply (lt_to_not_eq ? ? H8)
              | reflexivity
              ]
            | intros.
              reflexivity
            ]
          | rewrite > H6.
            rewrite > (eq_to_eqb_true ? ? (refl_eq ? n1)).
            reflexivity
          ]
        ]
      | assumption
      ]
    | apply le_S_S_to_le.
      assumption
    ]
  | rewrite > false_to_sigma_p_Sn_gen
    [ elim (le_to_or_lt_eq i n1)
      [ rewrite > false_to_sigma_p_Sn_gen
        [ apply H
          [ assumption
          | assumption
          | assumption
          | assumption
          | assumption
          ]
        | rewrite > H6.reflexivity
        ]
      | apply False_ind. 
        apply not_eq_true_false.
        rewrite < H5.
        rewrite > H7.
        assumption
      | apply le_S_S_to_le.
        assumption
      ]
    | assumption
    ]
  ] 
] 
qed.


theorem eq_sigma_p_gh_gen: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a) \to
\forall g: nat \to A.
\forall h,h1: nat \to nat.
\forall n,n1:nat.
\forall p1,p2:nat \to bool.
(\forall i. i < n \to p1 i = true \to p2 (h i) = true) \to
(\forall i. i < n \to p1 i = true \to h1 (h i) = i) \to 
(\forall i. i < n \to p1 i = true \to h i < n1) \to 
(\forall j. j < n1 \to p2 j = true \to p1 (h1 j) = true) \to
(\forall j. j < n1 \to p2 j = true \to h (h1 j) = j) \to 
(\forall j. j < n1 \to p2 j = true \to h1 j < n) \to 

sigma_p_gen n p1 A (\lambda x.g(h x)) baseA plusA = 
sigma_p_gen n1 (\lambda x.p2 x) A g baseA plusA.
intros 10.
elim n
[ generalize in match H8.
  elim n1
  [ reflexivity
  | apply (bool_elim ? (p2 n2));intro
    [ apply False_ind.
      apply (not_le_Sn_O (h1 n2)).
      apply H10
      [ apply le_n
      | assumption
      ]
    | rewrite > false_to_sigma_p_Sn_gen
      [ apply H9.
        intros.  
        apply H10
        [ apply le_S.
          apply H12
        | assumption
        ]
      | assumption
      ]
    ]
  ]
| apply (bool_elim ? (p1 n1));intro
  [ rewrite > true_to_sigma_p_Sn_gen
    [ rewrite > (sigma_p_gi_gen A g baseA plusA n2 (h n1))
      [ apply eq_f2
        [ reflexivity
        | apply H3
          [ intros.
            rewrite > H4
            [ simplify.
              change with ((\not eqb (h i) (h n1))= \not false).
              apply eq_f.
              apply not_eq_to_eqb_false.
              unfold Not.
              intro.
              apply (lt_to_not_eq ? ? H11).
              rewrite < H5
              [ rewrite < (H5 n1)
                [ apply eq_f.
                  assumption
                | apply le_n
                | assumption
                ]
              | apply le_S.
                assumption
              | assumption
              ]
            | apply le_S.assumption
            | assumption
            ]
          | intros.
            apply H5
            [ apply le_S.
              assumption
            | assumption
            ]
          | intros.
            apply H6
            [ apply le_S.assumption
            | assumption
            ]
          | intros.
            apply H7
            [ assumption
            | generalize in match H12.
              elim (p2 j)
              [ reflexivity
              | assumption
              ]
            ]
          | intros.
            apply H8
            [ assumption
            | generalize in match H12.
              elim (p2 j)
              [ reflexivity
              | assumption
              ]
            ]
          | intros.
            elim (le_to_or_lt_eq (h1 j) n1)
            [ assumption
            | generalize in match H12.
              elim (p2 j)
              [ simplify in H13.
                absurd (j = (h n1))
                [ rewrite < H13.
                  rewrite > H8
                  [ reflexivity
                  | assumption
                  | autobatch
                  ]
                | apply eqb_false_to_not_eq.
                  generalize in match H14.
                  elim (eqb j (h n1))
                  [ apply sym_eq.assumption
                  | reflexivity
                  ]
                ]
              | simplify in H14.
                apply False_ind.
                apply not_eq_true_false.
                apply sym_eq.assumption
              ]
            | apply le_S_S_to_le.
              apply H9
              [ assumption
              | generalize in match H12.
                elim (p2 j)
                [ reflexivity
                | assumption
                ]
              ]
            ]
          ]
        ]
      | assumption  
      | assumption
      | assumption  
      | apply H6
        [ apply le_n
        | assumption
        ]
      | apply H4
        [ apply le_n
        | assumption
        ]
      ]
    | assumption
    ]
  | rewrite > false_to_sigma_p_Sn_gen
    [ apply H3
      [ intros.
        apply H4[apply le_S.assumption|assumption]
      | intros.
        apply H5[apply le_S.assumption|assumption]
      | intros.
        apply H6[apply le_S.assumption|assumption]
      | intros.
        apply H7[assumption|assumption]
      | intros.
        apply H8[assumption|assumption]
      | intros.
        elim (le_to_or_lt_eq (h1 j) n1)
        [ assumption
        | absurd (j = (h n1))
          [ rewrite < H13.
            rewrite > H8
            [ reflexivity
            | assumption
            | assumption
            ]
          | unfold Not.intro.
            apply not_eq_true_false.
            rewrite < H10.
            rewrite < H13.
            rewrite > H7
            [ reflexivity
            | assumption
            | assumption
            ]
          ]
        | apply le_S_S_to_le.
          apply H9
          [ assumption
          | assumption
          ]
        ]
      ]
    | assumption
    ]
  ]
]
qed.



definition p_ord_times \def
\lambda p,m,x.
  match p_ord x p with
  [pair q r \Rightarrow r*m+q].
  
theorem  eq_p_ord_times: \forall p,m,x.
p_ord_times p m x = (ord_rem x p)*m+(ord x p).
intros.unfold p_ord_times. unfold ord_rem.
unfold ord.
elim (p_ord x p).
reflexivity.
qed.

theorem div_p_ord_times: 
\forall p,m,x. ord x p < m \to p_ord_times p m x / m = ord_rem x p.
intros.rewrite > eq_p_ord_times.
apply div_plus_times.
assumption.
qed.

theorem mod_p_ord_times: 
\forall p,m,x. ord x p < m \to p_ord_times p m x \mod m = ord x p.
intros.rewrite > eq_p_ord_times.
apply mod_plus_times.
assumption.
qed.

theorem sigma_p_divides_gen:
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
\forall n,m,p:nat.O < n \to prime p \to Not (divides p n) \to 
\forall g: nat \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a)

\to

sigma_p_gen (S (n*(exp p m))) (\lambda x.divides_b x (n*(exp p m))) A g baseA plusA =
sigma_p_gen (S n) (\lambda x.divides_b x n) A
  (\lambda x.sigma_p_gen (S m) (\lambda y.true) A (\lambda y.g (x*(exp p y))) baseA plusA) baseA plusA.
intros.
cut (O < p)
  [rewrite < (sigma_p2_gen ? ? ? ? ? ? ? ? H3 H4 H5).
   apply (trans_eq ? ? 
    (sigma_p_gen (S n*S m) (\lambda x:nat.divides_b (x/S m) n) A
       (\lambda x:nat.g (x/S m*(p)\sup(x\mod S m)))  baseA plusA) )
    [apply sym_eq.
     apply (eq_sigma_p_gh_gen ? ? ? ? ? ? g ? (p_ord_times p (S m)))
      [ assumption
      | assumption
      | assumption
      |intros.
       lapply (divides_b_true_to_lt_O ? ? H H7).
       apply divides_to_divides_b_true
        [rewrite > (times_n_O O).
         apply lt_times
          [assumption
          |apply lt_O_exp.assumption
          ]
        |apply divides_times
          [apply divides_b_true_to_divides.assumption
          |apply (witness ? ? (p \sup (m-i \mod (S m)))).
           rewrite < exp_plus_times.
           apply eq_f.
           rewrite > sym_plus.
           apply plus_minus_m_m.
           autobatch
          ]
        ]
      |intros.
       lapply (divides_b_true_to_lt_O ? ? H H7).
       unfold p_ord_times.
       rewrite > (p_ord_exp1 p ? (i \mod (S m)) (i/S m))
        [change with ((i/S m)*S m+i \mod S m=i).
         apply sym_eq.
         apply div_mod.
         apply lt_O_S
        |assumption
        |unfold Not.intro.
         apply H2.
         apply (trans_divides ? (i/ S m))
          [assumption|
           apply divides_b_true_to_divides;assumption]
        |apply sym_times.
        ]
      |intros.
       apply le_S_S.
       apply le_times
        [apply le_S_S_to_le.
         change with ((i/S m) < S n).
         apply (lt_times_to_lt_l m).
         apply (le_to_lt_to_lt ? i)
          [autobatch|assumption]
        |apply le_exp
          [assumption
          |apply le_S_S_to_le.
           apply lt_mod_m_m.
           apply lt_O_S
          ]
        ]
      |intros.
       cut (ord j p < S m)
        [rewrite > div_p_ord_times
          [apply divides_to_divides_b_true
            [apply lt_O_ord_rem
             [elim H1.assumption
             |apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
               [assumption|apply lt_O_exp.assumption]
             ]
           |cut (n = ord_rem (n*(exp p m)) p)
              [rewrite > Hcut2.
               apply divides_to_divides_ord_rem
                [apply (divides_b_true_to_lt_O ? ? ? H7).
                 rewrite > (times_n_O O).
                 apply lt_times
                 [assumption|apply lt_O_exp.assumption]
                 |rewrite > (times_n_O O).
                   apply lt_times
                  [assumption|apply lt_O_exp.assumption]
               |assumption
               |apply divides_b_true_to_divides.
                assumption
               ]
              |unfold ord_rem.
              rewrite > (p_ord_exp1 p ? m n)
                [reflexivity
               |assumption
                |assumption
               |apply sym_times
               ]
             ]
            ]
          |assumption
          ]
        |cut (m = ord (n*(exp p m)) p)
          [apply le_S_S.
           rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |apply sym_times
            ]
          ]
        ]
      |intros.
       cut (ord j p < S m)
        [rewrite > div_p_ord_times
          [rewrite > mod_p_ord_times
            [rewrite > sym_times.
             apply sym_eq.
             apply exp_ord
              [elim H1.assumption
              |apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              ]
           |cut (m = ord (n*(exp p m)) p)
             [apply le_S_S.
              rewrite > Hcut2.
              apply divides_to_le_ord
               [apply (divides_b_true_to_lt_O ? ? ? H7).
                rewrite > (times_n_O O).
                apply lt_times
                 [assumption|apply lt_O_exp.assumption]
               |rewrite > (times_n_O O).
                apply lt_times
                 [assumption|apply lt_O_exp.assumption]
               |assumption
               |apply divides_b_true_to_divides.
                assumption
               ]
             |unfold ord.
              rewrite > (p_ord_exp1 p ? m n)
                [reflexivity
                |assumption
                |assumption
                |apply sym_times
                ]
              ]
            ]
          |assumption
          ]
        |cut (m = ord (n*(exp p m)) p)
          [apply le_S_S.
           rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |apply sym_times
            ]
          ]
        ]
      |intros.
       rewrite > eq_p_ord_times.
       rewrite > sym_plus.
       apply (lt_to_le_to_lt ? (S m +ord_rem j p*S m))
        [apply lt_plus_l.
         apply le_S_S.
         cut (m = ord (n*(p \sup m)) p)
          [rewrite > Hcut1.
           apply divides_to_le_ord
            [apply (divides_b_true_to_lt_O ? ? ? H7).
             rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |rewrite > (times_n_O O).
             apply lt_times
              [assumption|apply lt_O_exp.assumption]
            |assumption
            |apply divides_b_true_to_divides.
             assumption
            ]
          |unfold ord.
           rewrite > sym_times.
           rewrite > (p_ord_exp1 p ? m n)
            [reflexivity
            |assumption
            |assumption
            |reflexivity
            ]
          ]
        |change with (S (ord_rem j p)*S m \le S n*S m).
         apply le_times_l.
         apply le_S_S.
         cut (n = ord_rem (n*(p \sup m)) p)
          [rewrite > Hcut1.
           apply divides_to_le
            [apply lt_O_ord_rem
              [elim H1.assumption
              |rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              ]
            |apply divides_to_divides_ord_rem
              [apply (divides_b_true_to_lt_O ? ? ? H7).
               rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              |rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              |assumption
              |apply divides_b_true_to_divides.
               assumption
              ]
            ]
        |unfold ord_rem.
         rewrite > sym_times.
         rewrite > (p_ord_exp1 p ? m n)
          [reflexivity
          |assumption
          |assumption
          |reflexivity
          ]
        ]
      ]
    ]
  |apply eq_sigma_p_gen
  
    [intros.
     elim (divides_b (x/S m) n);reflexivity
    |intros.reflexivity
    ]
  ]
|elim H1.apply lt_to_le.assumption
]
qed.
    
(*distributive property for sigma_p_gen*)
theorem distributive_times_plus_sigma_p_generic: \forall A:Type.
\forall plusA: A \to A \to A. \forall basePlusA: A.
\forall timesA: A \to A \to A. 
\forall n:nat. \forall k:A. \forall p:nat \to bool. \forall g:nat \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  basePlusA) = a) \to
(symmetric A timesA) \to (distributive A timesA plusA) \to
(\forall a:A. (timesA a basePlusA) = basePlusA)
 
  \to

((timesA k (sigma_p_gen n p A g basePlusA plusA)) = 
 (sigma_p_gen n p A (\lambda i:nat.(timesA k (g i))) basePlusA plusA)).
intros.
elim n
[ simplify.
  apply H5
| cut( (p n1) = true \lor (p n1) = false)
  [ elim Hcut
    [ rewrite > (true_to_sigma_p_Sn_gen ? ? ? ? ? ? H7).
      rewrite > (true_to_sigma_p_Sn_gen ? ? ? ? ? ? H7) in \vdash (? ? ? %).
      rewrite > (H4).
      rewrite > (H3 k (g n1)).
      apply eq_f.
      assumption
    | rewrite > (false_to_sigma_p_Sn_gen ? ? ? ? ? ? H7).
      rewrite > (false_to_sigma_p_Sn_gen ? ? ? ? ? ? H7) in \vdash (? ? ? %).
      assumption
    ]
  | elim ((p n1))
    [ left.
      reflexivity
    | right.
      reflexivity
    ]
  ]
]
qed.


