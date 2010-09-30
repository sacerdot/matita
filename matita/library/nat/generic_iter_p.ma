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

include "nat/div_and_mod_diseq.ma".
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
 
let rec iter_p_gen (n:nat) (p: nat \to bool) (A:Type) (g: nat \to A) 
   (baseA: A) (plusA: A \to A \to A)  \def
  match n with
   [ O \Rightarrow baseA
   | (S k) \Rightarrow 
      match p k with
      [true \Rightarrow (plusA (g k) (iter_p_gen k p A g baseA plusA))
      |false \Rightarrow iter_p_gen k p A g baseA plusA]
   ].
   
theorem true_to_iter_p_gen_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall A:Type. \forall g:nat \to A.
\forall baseA:A. \forall plusA: A \to A \to A.
p n = true \to iter_p_gen (S n) p A g baseA plusA = 
(plusA (g n) (iter_p_gen n p A g baseA plusA)).
intros.
simplify.
rewrite > H.
reflexivity.
qed.

theorem false_to_iter_p_gen_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall A:Type. \forall g:nat \to A.
\forall baseA:A. \forall plusA: A \to A \to A.
p n = false \to iter_p_gen (S n) p A g baseA plusA = iter_p_gen n p A g baseA plusA.
intros.
simplify.
rewrite > H.
reflexivity.
qed.

theorem eq_iter_p_gen: \forall p1,p2:nat \to bool. \forall A:Type.
\forall g1,g2: nat \to A. \forall baseA: A. 
\forall plusA: A \to A \to A. \forall n:nat.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to g1 x = g2 x) \to
iter_p_gen n p1 A g1 baseA plusA = iter_p_gen n p2 A g2 baseA plusA.
intros 8.
elim n
[ reflexivity
| apply (bool_elim ? (p1 n1))
  [ intro.
    rewrite > (true_to_iter_p_gen_Sn ? ? ? ? ? ? H3).
    rewrite > true_to_iter_p_gen_Sn     
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
    rewrite > (false_to_iter_p_gen_Sn ? ? ? ? ? ? H3).
    rewrite > false_to_iter_p_gen_Sn
    [ apply H
      [ intros.apply H1.apply le_S.assumption
      | intros.apply H2.apply le_S.assumption
      ]
    | rewrite < H3.apply sym_eq.apply H1.apply le_n
    ]
  ]
]
qed.

theorem eq_iter_p_gen1: \forall p1,p2:nat \to bool. \forall A:Type.
\forall g1,g2: nat \to A. \forall baseA: A. 
\forall plusA: A \to A \to A.\forall n:nat.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to p1 x = true \to g1 x = g2 x) \to
iter_p_gen n p1 A g1 baseA plusA = iter_p_gen n p2 A g2 baseA plusA.
intros 8.
elim n
[ reflexivity
| apply (bool_elim ? (p1 n1))
  [ intro.
    rewrite > (true_to_iter_p_gen_Sn ? ? ? ? ? ? H3).
    rewrite > true_to_iter_p_gen_Sn
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
    rewrite > (false_to_iter_p_gen_Sn ? ? ? ? ? ? H3).
    rewrite > false_to_iter_p_gen_Sn
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

theorem iter_p_gen_false: \forall A:Type. \forall g: nat \to A. \forall baseA:A.
\forall plusA: A \to A \to A. \forall n.
iter_p_gen n (\lambda x.false) A g baseA plusA = baseA.
intros.
elim n
[ reflexivity
| simplify.
  assumption
]
qed.

theorem iter_p_gen_plusA: \forall A:Type. \forall n,k:nat.\forall p:nat \to bool.
\forall g: nat \to A. \forall baseA:A. \forall plusA: A \to A \to A.
(symmetric A plusA) \to (\forall a:A. (plusA a baseA) = a) \to (associative A plusA)
\to
iter_p_gen (k + n) p A g baseA plusA 
= (plusA (iter_p_gen k (\lambda x.p (x+n)) A (\lambda x.g (x+n)) baseA plusA)
         (iter_p_gen n p A g baseA plusA)).
intros.

elim k
[ simplify.
  rewrite > H in \vdash (? ? ? %).
  rewrite > (H1 ?).
  reflexivity
| apply (bool_elim ? (p (n1+n)))
  [ intro.     
    rewrite > (true_to_iter_p_gen_Sn ? ? ? ? ? ? H4).
    rewrite > (true_to_iter_p_gen_Sn n1 (\lambda x.p (x+n)) ? ? ? ? H4).
    rewrite > (H2 (g (n1 + n)) ? ?).
    rewrite < H3.
    reflexivity
  | intro.
    rewrite > (false_to_iter_p_gen_Sn ? ? ? ? ? ? H4).
    rewrite > (false_to_iter_p_gen_Sn n1 (\lambda x.p (x+n)) ? ? ? ? H4).
    assumption
  ]
]
qed.

theorem false_to_eq_iter_p_gen: \forall A:Type. \forall n,m:nat.\forall p:nat \to bool.
\forall g: nat \to A. \forall baseA:A. \forall plusA: A \to A \to A. 
n \le m \to (\forall i:nat. n \le i \to i < m \to p i = false)
\to iter_p_gen m p A g baseA plusA = iter_p_gen n p A g baseA plusA.
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

(* a therem slightly more general than the previous one *)
theorem or_false_eq_baseA_to_eq_iter_p_gen: \forall A:Type. \forall n,m:nat.\forall p:nat \to bool.
\forall g: nat \to A. \forall baseA:A. \forall plusA: A \to A \to A.
(\forall a. plusA baseA a = a) \to
n \le m \to (\forall i:nat. n \le i \to i < m \to p i = false \lor g i = baseA)
\to iter_p_gen m p A g baseA plusA = iter_p_gen n p A g baseA plusA.
intros 9.
elim H1
[reflexivity
|apply (bool_elim ? (p n1));intro
  [elim (H4 n1)
    [apply False_ind.
     apply not_eq_true_false.
     rewrite < H5.
     rewrite < H6.
     reflexivity
    |rewrite > true_to_iter_p_gen_Sn
      [rewrite > H6.
       rewrite > H.
       apply H3.intros.
       apply H4
        [assumption
        |apply le_S.assumption
        ]
      |assumption
      ]
    |assumption
    |apply le_n
    ]
  |rewrite > false_to_iter_p_gen_Sn
    [apply H3.intros.
     apply H4
      [assumption
      |apply le_S.assumption
      ]
    |assumption
    ]
  ]
]
qed.
    
theorem iter_p_gen2 : 
\forall n,m:nat.
\forall p1,p2:nat \to bool.
\forall A:Type.
\forall g: nat \to nat \to A.
\forall baseA: A.
\forall plusA: A \to A \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a)
\to
iter_p_gen (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (mod x m)))
  A 
  (\lambda x.g (div x m) (mod x m)) 
  baseA
  plusA  =
iter_p_gen n p1 A
  (\lambda x.iter_p_gen m p2 A (g x) baseA plusA)
  baseA plusA.
intros.
elim n
[ simplify.
  reflexivity
| apply (bool_elim ? (p1 n1))
  [ intro.
    rewrite > (true_to_iter_p_gen_Sn ? ? ? ? ? ? H4).
    simplify in \vdash (? ? (? % ? ? ? ? ?) ?).
    rewrite > iter_p_gen_plusA
    [ rewrite < H3.
      apply eq_f2
      [ apply eq_iter_p_gen
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
          reflexivity.   
        ]
      | reflexivity
      ]
    | assumption
    | assumption
    | assumption
    ]
  | intro.
    rewrite > (false_to_iter_p_gen_Sn ? ? ? ? ? ? H4).
    simplify in \vdash (? ? (? % ? ? ? ? ?) ?).
    rewrite > iter_p_gen_plusA
    [ rewrite > H3.
      apply (trans_eq ? ? (plusA baseA
           (iter_p_gen n1 p1 A (\lambda x:nat.iter_p_gen m p2 A (g x) baseA plusA) baseA plusA )))
      [ apply eq_f2
        [ rewrite > (eq_iter_p_gen ? (\lambda x.false) A ? (\lambda x:nat.g ((x+n1*m)/m) ((x+n1*m)\mod m)))
          [ apply iter_p_gen_false
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

theorem iter_p_gen2': 
\forall n,m:nat.
\forall p1: nat \to bool.
\forall p2: nat \to nat \to bool.
\forall A:Type.
\forall g: nat \to nat \to A.
\forall baseA: A.
\forall plusA: A \to A \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a)
\to
iter_p_gen (n*m) 
  (\lambda x.andb (p1 (div x m)) (p2 (div x m)(mod x m)))
  A 
  (\lambda x.g (div x m) (mod x m)) 
  baseA
  plusA  =
iter_p_gen n p1 A
  (\lambda x.iter_p_gen m (p2 x) A (g x) baseA plusA)
  baseA plusA.
intros.
elim n
[ simplify.
  reflexivity
| apply (bool_elim ? (p1 n1))
  [ intro.
    rewrite > (true_to_iter_p_gen_Sn ? ? ? ? ? ? H4).
    simplify in \vdash (? ? (? % ? ? ? ? ?) ?).
    rewrite > iter_p_gen_plusA
    [ rewrite < H3.
      apply eq_f2
      [ apply eq_iter_p_gen
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
          reflexivity.   
        ]
      | reflexivity
      ]
    | assumption
    | assumption
    | assumption
    ]
  | intro.
    rewrite > (false_to_iter_p_gen_Sn ? ? ? ? ? ? H4).
    simplify in \vdash (? ? (? % ? ? ? ? ?) ?).
    rewrite > iter_p_gen_plusA
    [ rewrite > H3.
      apply (trans_eq ? ? (plusA baseA
           (iter_p_gen n1 p1 A (\lambda x:nat.iter_p_gen m (p2 x) A (g x) baseA plusA) baseA plusA )))
      [ apply eq_f2
        [ rewrite > (eq_iter_p_gen ? (\lambda x.false) A ? (\lambda x:nat.g ((x+n1*m)/m) ((x+n1*m)\mod m)))
          [ apply iter_p_gen_false
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

lemma iter_p_gen_gi: 
\forall A:Type.
\forall g: nat \to A.
\forall baseA:A.
\forall plusA: A \to A \to A.
\forall n,i:nat.
\forall p:nat \to bool.
(symmetric A plusA) \to  (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a) 
  \to 
  
i < n \to p i = true \to
(iter_p_gen n p A g baseA plusA) = 
(plusA (g i) (iter_p_gen n (\lambda x:nat. andb (p x) (notb (eqb x i))) A g baseA plusA)).
intros 5.
elim n
[ apply False_ind.
  apply (not_le_Sn_O i).
  assumption
| apply (bool_elim ? (p n1));intro
  [ elim (le_to_or_lt_eq i n1)
    [ rewrite > true_to_iter_p_gen_Sn
      [ rewrite > true_to_iter_p_gen_Sn
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
    | rewrite > true_to_iter_p_gen_Sn
      [ rewrite > H7.
        apply eq_f2
        [ reflexivity
        | rewrite > false_to_iter_p_gen_Sn
          [ apply eq_iter_p_gen
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
  | rewrite > false_to_iter_p_gen_Sn
    [ elim (le_to_or_lt_eq i n1)
      [ rewrite > false_to_iter_p_gen_Sn
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

(* invariance under permutation; single sum *)
theorem eq_iter_p_gen_gh: 
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

iter_p_gen n p1 A (\lambda x.g(h x)) baseA plusA = 
iter_p_gen n1 p2 A g baseA plusA.
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
    | rewrite > false_to_iter_p_gen_Sn
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
  [ rewrite > true_to_iter_p_gen_Sn
    [ rewrite > (iter_p_gen_gi A g baseA plusA n2 (h n1))
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
                  | apply andb_true_true; [2: apply H12]
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
  | rewrite > false_to_iter_p_gen_Sn
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

theorem eq_iter_p_gen_pred: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A.
\forall n,p,g.
p O = true \to
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a) \to
iter_p_gen (S n) (\lambda i.p (pred i)) A (\lambda i.g(pred i)) baseA plusA = 
plusA (iter_p_gen n p A g baseA plusA) (g O).
intros.
elim n
  [rewrite > true_to_iter_p_gen_Sn
    [simplify.apply H1
    |assumption
    ]
  |apply (bool_elim ? (p n1));intro
    [rewrite > true_to_iter_p_gen_Sn
      [rewrite > true_to_iter_p_gen_Sn in ⊢ (? ? ? %)
        [rewrite > H2 in ⊢ (? ? ? %).
         apply eq_f.assumption
        |assumption
        ]
      |assumption
      ]
    |rewrite > false_to_iter_p_gen_Sn
      [rewrite > false_to_iter_p_gen_Sn in ⊢ (? ? ? %);assumption
      |assumption
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

lemma lt_times_to_lt_O: \forall i,n,m:nat. i < n*m \to O < m.
intros.
elim (le_to_or_lt_eq O ? (le_O_n m))
  [assumption
  |apply False_ind.
   rewrite < H1 in H.
   rewrite < times_n_O in H.
   apply (not_le_Sn_O ? H)
  ]
qed.

theorem iter_p_gen_knm:
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to A.
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
iter_p_gen k p1 A g baseA plusA =
iter_p_gen n p21 A (\lambda x:nat.iter_p_gen m (p22 x) A (\lambda y. g (h2 x y)) baseA plusA) baseA plusA.
intros.
rewrite < (iter_p_gen2' n m p21 p22 ? ? ? ? H H1 H2).
apply sym_eq.
apply (eq_iter_p_gen_gh A baseA plusA H H1 H2 g ? (\lambda x.(h11 x)*m+(h12 x)))
 [intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    assumption
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    rewrite > H10.
    rewrite > H9.
    apply sym_eq.
    apply div_mod.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)  
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H4 (i/m) (i \mod m));clear H4
   [elim H7.clear H7.
    elim H4.clear H4.
    assumption
   |apply (lt_times_to_lt_div ? ? ? H5)
   |apply lt_mod_m_m.
    apply (lt_times_to_lt_O ? ? ? H5)
   |apply (andb_true_true ? ? H6)
   |apply (andb_true_true_r ? ? H6)
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7.
  rewrite > div_plus_times
   [rewrite > mod_plus_times
     [rewrite > H9.
      rewrite > H12.
      reflexivity.
     |assumption
     ]
   |assumption
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7. 
  rewrite > div_plus_times
   [rewrite > mod_plus_times
     [assumption
     |assumption
     ]
   |assumption
   ]
 |intros.
  elim (H3 j H5 H6).
  elim H7.clear H7.
  elim H9.clear H9.
  elim H7.clear H7. 
  apply (lt_to_le_to_lt ? ((h11 j)*m+m))
   [apply monotonic_lt_plus_r.
    assumption
   |rewrite > sym_plus.
    change with ((S (h11 j)*m) \le n*m).
    apply monotonic_le_times_l.
    assumption
   ]
 ]
qed.

theorem iter_p_gen_divides:
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
\forall n,m,p:nat.O < n \to prime p \to Not (divides p n) \to 
\forall g: nat \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  baseA) = a)

\to

iter_p_gen (S (n*(exp p m))) (\lambda x.divides_b x (n*(exp p m))) A g baseA plusA =
iter_p_gen (S n) (\lambda x.divides_b x n) A
  (\lambda x.iter_p_gen (S m) (\lambda y.true) A (\lambda y.g (x*(exp p y))) baseA plusA) baseA plusA.
intros.
cut (O < p)
  [rewrite < (iter_p_gen2 ? ? ? ? ? ? ? ? H3 H4 H5).
   apply (trans_eq ? ? 
    (iter_p_gen (S n*S m) (\lambda x:nat.divides_b (x/S m) n) A
       (\lambda x:nat.g (x/S m*(p)\sup(x\mod S m)))  baseA plusA) )
    [apply sym_eq.
     apply (eq_iter_p_gen_gh ? ? ? ? ? ? g ? (p_ord_times p (S m)))
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
           autobatch by le_S_S_to_le, lt_mod_m_m, lt_O_S;
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
         apply (le_to_lt_to_lt ? i);[2:assumption]
         autobatch by eq_plus_to_le, div_mod, lt_O_S.
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
  |apply eq_iter_p_gen
  
    [intros.
     elim (divides_b (x/S m) n);reflexivity
    |intros.reflexivity
    ]
  ]
|elim H1.apply lt_to_le.assumption
]
qed.
    
(*distributive property for iter_p_gen*)
theorem distributive_times_plus_iter_p_gen: \forall A:Type.
\forall plusA: A \to A \to A. \forall basePlusA: A.
\forall timesA: A \to A \to A. 
\forall n:nat. \forall k:A. \forall p:nat \to bool. \forall g:nat \to A.
(symmetric A plusA) \to (associative A plusA) \to (\forall a:A.(plusA a  basePlusA) = a) \to
(symmetric A timesA) \to (distributive A timesA plusA) \to
(\forall a:A. (timesA a basePlusA) = basePlusA)
 
  \to

((timesA k (iter_p_gen n p A g basePlusA plusA)) = 
 (iter_p_gen n p A (\lambda i:nat.(timesA k (g i))) basePlusA plusA)).
intros.
elim n
[ simplify.
  apply H5
| cut( (p n1) = true \lor (p n1) = false)
  [ elim Hcut
    [ rewrite > (true_to_iter_p_gen_Sn ? ? ? ? ? ? H7).
      rewrite > (true_to_iter_p_gen_Sn ? ? ? ? ? ? H7) in \vdash (? ? ? %).
      rewrite > (H4).
      rewrite > (H3 k (g n1)).
      apply eq_f.
      assumption
    | rewrite > (false_to_iter_p_gen_Sn ? ? ? ? ? ? H7).
      rewrite > (false_to_iter_p_gen_Sn ? ? ? ? ? ? H7) in \vdash (? ? ? %).
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

(* old version - proved without theorem iter_p_gen_knm
theorem iter_p_gen_2_eq: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to nat \to A.
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
iter_p_gen n1 p11 A 
     (\lambda x:nat .iter_p_gen m1 (p12 x) A (\lambda y. g x y) baseA plusA) 
     baseA plusA =
iter_p_gen n2 p21 A 
    (\lambda x:nat .iter_p_gen m2 (p22 x) A  (\lambda y. g (h11 x y) (h12 x y)) baseA plusA )
    baseA plusA.
intros.
rewrite < (iter_p_gen2' ? ? ? ? ? ? ? ? H H1 H2).
rewrite < (iter_p_gen2' ? ? ? ? ? ? ? ? H H1 H2).
apply sym_eq.
letin h := (\lambda x.(h11 (x/m2) (x\mod m2))*m1 + (h12 (x/m2) (x\mod m2))).
letin h1 := (\lambda x.(h21 (x/m1) (x\mod m1))*m2 + (h22 (x/m1) (x\mod m1))).
apply (trans_eq ? ? 
  (iter_p_gen (n2*m2) (\lambda x:nat.p21 (x/m2)\land p22 (x/m2) (x\mod m2)) A
  (\lambda x:nat.g ((h x)/m1) ((h x)\mod m1)) baseA plusA ))
  [clear h.clear h1.
   apply eq_iter_p_gen1
    [intros.reflexivity
    |intros.
     cut (O < m2)
      [cut (x/m2 < n2)
        [cut (x \mod m2 < m2)
          [elim (and_true ? ? H6).
           elim (H3 ? ? Hcut1 Hcut2 H7 H8).
           elim H9.clear H9.
           elim H11.clear H11.
           elim H9.clear H9.
           elim H11.clear H11.
           apply eq_f2
            [apply sym_eq.
             apply div_plus_times.
             assumption
            | apply sym_eq.
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
       generalize in match H5.
       apply (le_n_O_elim ? H7).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]      
    ]
  |apply (eq_iter_p_gen_gh ? ? ? H H1 H2 ? h h1);intros
    [cut (O < m2)
      [cut (i/m2 < n2)
        [cut (i \mod m2 < m2)
          [elim (and_true ? ? H6).
           elim (H3 ? ? Hcut1 Hcut2 H7 H8).
           elim H9.clear H9.
           elim H11.clear H11.
           elim H9.clear H9.
           elim H11.clear H11.
           cut ((h11 (i/m2) (i\mod m2)*m1+h12 (i/m2) (i\mod m2))/m1 = 
                 h11 (i/m2) (i\mod m2))
            [cut ((h11 (i/m2) (i\mod m2)*m1+h12 (i/m2) (i\mod m2))\mod m1 =
                  h12 (i/m2) (i\mod m2))
              [rewrite > Hcut3.
               rewrite > Hcut4.
               rewrite > H9.
               rewrite > H15.
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
       generalize in match H5.
       apply (le_n_O_elim ? H7).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]      
    |cut (O < m2)
      [cut (i/m2 < n2)
        [cut (i \mod m2 < m2)
          [elim (and_true ? ? H6).
           elim (H3 ? ? Hcut1 Hcut2 H7 H8).
           elim H9.clear H9.
           elim H11.clear H11.
           elim H9.clear H9.
           elim H11.clear H11.
           cut ((h11 (i/m2) (i\mod m2)*m1+h12 (i/m2) (i\mod m2))/m1 = 
                 h11 (i/m2) (i\mod m2))
            [cut ((h11 (i/m2) (i\mod m2)*m1+h12 (i/m2) (i\mod m2))\mod m1 =
                  h12 (i/m2) (i\mod m2))
              [rewrite > Hcut3.
               rewrite > Hcut4.
               rewrite > H13.
               rewrite > H14.
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
       generalize in match H5.
       apply (le_n_O_elim ? H7).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]      
    |cut (O < m2)
      [cut (i/m2 < n2)
        [cut (i \mod m2 < m2)
          [elim (and_true ? ? H6).
           elim (H3 ? ? Hcut1 Hcut2 H7 H8).
           elim H9.clear H9.
           elim H11.clear H11.
           elim H9.clear H9.
           elim H11.clear H11.
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
       generalize in match H5.
       apply (le_n_O_elim ? H7).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]
    |cut (O < m1)
      [cut (j/m1 < n1)
        [cut (j \mod m1 < m1)
          [elim (and_true ? ? H6).
           elim (H4 ? ? Hcut1 Hcut2 H7 H8).
           elim H9.clear H9.
           elim H11.clear H11.
           elim H9.clear H9.
           elim H11.clear H11.
           cut ((h21 (j/m1) (j\mod m1)*m2+h22 (j/m1) (j\mod m1))/m2 = 
                 h21 (j/m1) (j\mod m1))
            [cut ((h21 (j/m1) (j\mod m1)*m2+h22 (j/m1) (j\mod m1))\mod m2 =
                  h22 (j/m1) (j\mod m1))
              [rewrite > Hcut3.
               rewrite > Hcut4.
               rewrite > H9.
               rewrite > H15.
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
       generalize in match H5.
       apply (le_n_O_elim ? H7).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ] 
    |cut (O < m1)
      [cut (j/m1 < n1)
        [cut (j \mod m1 < m1)
          [elim (and_true ? ? H6).
           elim (H4 ? ? Hcut1 Hcut2 H7 H8).
           elim H9.clear H9.
           elim H11.clear H11.
           elim H9.clear H9.
           elim H11.clear H11.
           cut ((h21 (j/m1) (j\mod m1)*m2+h22 (j/m1) (j\mod m1))/m2 = 
                 h21 (j/m1) (j\mod m1))
            [cut ((h21 (j/m1) (j\mod m1)*m2+h22 (j/m1) (j\mod m1))\mod m2 =
                  h22 (j/m1) (j\mod m1))
              [rewrite > Hcut3.
               rewrite > Hcut4.               
               rewrite > H13.
               rewrite > H14.
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
       generalize in match H5.
       apply (le_n_O_elim ? H7).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ] 
    |cut (O < m1)
      [cut (j/m1 < n1)
        [cut (j \mod m1 < m1)
          [elim (and_true ? ? H6).
           elim (H4 ? ? Hcut1 Hcut2 H7 H8).
           elim H9.clear H9.
           elim H11.clear H11.
           elim H9.clear H9.
           elim H11.clear H11.
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
       generalize in match H5.
       apply (le_n_O_elim ? H7).
       rewrite < times_n_O.
       apply le_to_not_lt.
       apply le_O_n  
      ]
    ]
  ]
qed.*)


theorem iter_p_gen_2_eq: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to nat \to A.
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
iter_p_gen n1 p11 A 
     (\lambda x:nat .iter_p_gen m1 (p12 x) A (\lambda y. g x y) baseA plusA) 
     baseA plusA =
iter_p_gen n2 p21 A 
    (\lambda x:nat .iter_p_gen m2 (p22 x) A  (\lambda y. g (h11 x y) (h12 x y)) baseA plusA )
    baseA plusA.

intros.
rewrite < (iter_p_gen2' ? ? ? ? ? ? ? ? H H1 H2).
letin ha:= (\lambda x,y.(((h11 x y)*m1) + (h12 x y))).
letin ha12:= (\lambda x.(h21 (x/m1) (x \mod m1))).
letin ha22:= (\lambda x.(h22 (x/m1) (x \mod m1))).

apply (trans_eq ? ? 
(iter_p_gen n2 p21 A (\lambda x:nat. iter_p_gen m2 (p22 x) A
 (\lambda y:nat.(g (((h11 x y)*m1+(h12 x y))/m1) (((h11 x y)*m1+(h12 x y))\mod m1))) baseA plusA ) baseA plusA))
[
  apply (iter_p_gen_knm A baseA plusA H H1 H2 (\lambda e. (g (e/m1) (e \mod m1))) ha ha12 ha22);intros
  [ elim (and_true ? ? H6).
    cut(O \lt m1)
    [ cut(x/m1 < n1)
      [ cut((x \mod m1) < m1)
        [ elim (H4 ? ? Hcut1 Hcut2 H7 H8).
          elim H9.clear H9.
          elim H11.clear H11.
          elim H9.clear H9.
          elim H11.clear H11.
          split
          [ split
            [ split
              [ split
                [ assumption
                | assumption
                ]
              | unfold ha.
                unfold ha12.
                unfold ha22.
                rewrite > H14.
                rewrite > H13.
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
      generalize in match H5.
      apply (le_n_O_elim ? H9).
      rewrite < times_n_O.
      apply le_to_not_lt.
      apply le_O_n.              
    ]
  | elim (H3 ? ? H5 H6 H7 H8).
    elim H9.clear H9.
    elim H11.clear H11.
    elim H9.clear H9.
    elim H11.clear H11.
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
            | unfold ha.
              unfold ha12.
              rewrite > Hcut1.
              rewrite > Hcut.
              assumption
            ]
          | unfold ha.
            unfold ha22.
            rewrite > Hcut1.
            rewrite > Hcut.
            assumption            
          ]
        | cut(O \lt m1)
          [ cut(O \lt n1)      
            [ apply (lt_to_le_to_lt ? ((h11 i j)*m1 + m1) )
              [ unfold ha.
                apply (lt_plus_r).
                assumption
              | rewrite > sym_plus.
                rewrite > (sym_times (h11 i j) m1).
                rewrite > times_n_Sm.
                rewrite > sym_times.
                apply (le_times_l).
                assumption  
              ]
            | apply not_le_to_lt.unfold.intro.
              generalize in match H12.
              apply (le_n_O_elim ? H11).       
              apply le_to_not_lt.
              apply le_O_n
            ]
          | apply not_le_to_lt.unfold.intro.
            generalize in match H10.
            apply (le_n_O_elim ? H11).       
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
| apply (eq_iter_p_gen1)
  [ intros. reflexivity 
  | intros.
    apply (eq_iter_p_gen1)
    [ intros. reflexivity
    | intros.
      rewrite > (div_plus_times)
      [ rewrite > (mod_plus_times)
        [ reflexivity
        | elim (H3 x x1 H5 H7 H6 H8).
          assumption
        ]
      | elim (H3 x x1 H5 H7 H6 H8).       
        assumption
      ]
    ]
  ]
]
qed.

theorem iter_p_gen_iter_p_gen: 
\forall A:Type.
\forall baseA: A.
\forall plusA: A \to A \to A. 
(symmetric A plusA) \to 
(associative A plusA) \to 
(\forall a:A.(plusA a  baseA) = a)\to
\forall g: nat \to nat \to A.
\forall n,m.
\forall p11,p21:nat \to bool.
\forall p12,p22:nat \to nat \to bool.
(\forall x,y. x < n \to y < m \to 
 (p11 x \land p12 x y) = (p21 y \land p22 y x)) \to
iter_p_gen n p11 A 
  (\lambda x:nat.iter_p_gen m (p12 x) A (\lambda y. g x y) baseA plusA) 
  baseA plusA =
iter_p_gen m p21 A 
  (\lambda y:nat.iter_p_gen n (p22 y) A  (\lambda x. g x y) baseA plusA )
  baseA plusA.
intros.
apply (iter_p_gen_2_eq A baseA plusA H H1 H2 (\lambda x,y. g x y) (\lambda x,y.y) (\lambda x,y.x) (\lambda x,y.y) (\lambda x,y.x)
       n m m n p11 p21 p12 p22)
  [intros.split
    [split
      [split
        [split
          [split
            [apply (andb_true_true ? (p12 j i)).
             rewrite > H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            |apply (andb_true_true_r (p11 j)).
             rewrite > H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            ]
          |reflexivity
          ]
        |reflexivity
        ]
      |assumption
      ]
    |assumption
    ]
  |intros.split
    [split
      [split
        [split
          [split
            [apply (andb_true_true ? (p22 j i)).
             rewrite < H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            |apply (andb_true_true_r (p21 j)).
             rewrite < H3
              [rewrite > H6.rewrite > H7.reflexivity
              |assumption
              |assumption
              ]
            ]
          |reflexivity
          ]
        |reflexivity
        ]
      |assumption
      ]
    |assumption
    ]
  ]
qed.