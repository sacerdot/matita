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

include "nat/permutation.ma".
include "nat/count.ma".

let rec map_iter_p n p (g:nat \to nat) (a:nat) f \def
  match n with
   [ O \Rightarrow a
   | (S k) \Rightarrow 
      match p (S k) with
      [true \Rightarrow f (g (S k)) (map_iter_p k p g a f)
      |false \Rightarrow map_iter_p k p g a f]
   ].

theorem eq_map_iter_p: \forall g1,g2:nat \to nat.
\forall p:nat \to bool.
\forall f:nat \to nat \to nat. \forall a,n:nat.
(\forall m:nat. m \le n \to g1 m = g2 m) \to 
map_iter_p n p g1 a f = map_iter_p n p g2 a f.
intros 6.elim n
  [simplify.reflexivity.
  |simplify.elim (p (S n1))
    [simplify.apply eq_f2
      [apply H1.apply le_n
      |simplify.apply H.intros.apply H1.
       apply le_S.assumption
      ]
    |simplify.apply H.intros.apply H1.
     apply le_S.assumption
    ]
 ]
qed.

(* useful since simplify simpifies too much *)

theorem map_iter_p_O: \forall p.\forall g.\forall f. \forall a:nat.
map_iter_p O p g a f = a.
intros.simplify.reflexivity.
qed.

theorem map_iter_p_S_true: \forall p.\forall g.\forall f. \forall a,n:nat.
p (S n) = true \to 
map_iter_p (S n) p g a f = f (g (S n)) (map_iter_p n p g a f).
intros.simplify.rewrite > H.reflexivity.
qed.

theorem map_iter_p_S_false: \forall p.\forall g.\forall f. \forall a,n:nat.
p (S n) = false \to 
map_iter_p (S n) p g a f = map_iter_p n p g a f.
intros.simplify.rewrite > H.reflexivity.
qed.

(* map_iter examples *)
definition pi_p \def \lambda p. \lambda n.
map_iter_p n p (\lambda n.n) (S O) times.

lemma pi_p_S: \forall n.\forall p.
pi_p p (S n) = 
  match p (S n) with
    [true \Rightarrow (S n)*(pi_p p n)
    |false \Rightarrow (pi_p p n)
    ].
intros.reflexivity.
qed.

lemma lt_O_pi_p: \forall n.\forall p.
O < pi_p p n.
intros.elim n
  [simplify.apply le_n
  |rewrite > pi_p_S.
   elim p (S n1)
    [change with (O < (S n1)*(pi_p p n1)).
     rewrite >(times_n_O n1).
     apply lt_times[apply le_n|assumption]
    | assumption
    ]
  ]
qed.

let rec card n p \def 
  match n with
  [O \Rightarrow O
  |(S m) \Rightarrow 
      (bool_to_nat (p (S m))) + (card m p)].

lemma count_card: \forall p.\forall n.
p O = false \to count (S n) p = card n p.
intros.elim n
  [simplify.rewrite > H. reflexivity
  |simplify.
   rewrite < plus_n_O.
   apply eq_f.assumption
  ]
qed.

lemma count_card1: \forall p.\forall n.
p O = false \to p n = false \to count n p = card n p.
intros 3.apply (nat_case n)
  [intro.simplify.rewrite > H. reflexivity
  |intros.rewrite > (count_card ? ? H).
   simplify.rewrite > H1.reflexivity
  ]
qed.
 
lemma a_times_pi_p: \forall p. \forall a,n.
exp a (card n p) * pi_p p n = map_iter_p n p (\lambda n.a*n) (S O) times.
intros.elim n
  [simplify.reflexivity
  |simplify.apply (bool_elim ? (p (S n1)))
    [intro.
     change with 
      (a*exp a (card n1 p) * ((S n1) * (pi_p p n1)) = 
       a*(S n1)*map_iter_p n1 p (\lambda n.a*n) (S O) times).
       rewrite < H.
       autobatch
    |intro.assumption
    ]
  ]
qed.

definition permut_p \def \lambda f. \lambda p:nat\to bool. \lambda n.
\forall i. i \le n \to p i = true \to ((f i \le n \land p (f i) = true)
\land (\forall j. p j = true \to j \le n \to i \neq j \to (f i \neq f j))).

definition extentional_eq_n \def \lambda f,g:nat \to nat.\lambda n.
\forall x. x \le n \to f x = g x.

lemma extentional_eq_n_to_permut_p: \forall f,g. \forall p. \forall n. 
extentional_eq_n f g n\to permut_p f p n \to permut_p g p n.
intros.unfold permut_p.
intros.
elim (H1 i H2 H3).
split
  [elim H4.split
    [rewrite < (H  i H2).assumption
    |rewrite < (H  i H2).assumption
    ]
  |intros.
   unfold.intro.apply (H5 j H6 H7 H8).
     rewrite > (H  i H2).
     rewrite > (H  j H7).assumption
  ]
qed.

theorem permut_p_compose: \forall f,g.\forall p.\forall n.
permut_p f p n \to permut_p g p n \to permut_p (compose  ? ? ? g f) p n.
intros.unfold permut_p.intros.
elim (H i H2 H3).
elim H4.
elim (H1 (f i) H6 H7).
elim H8.
split
  [split
    [unfold compose.assumption
    |unfold compose.rewrite < H11.reflexivity
    ]
  |intros.
   unfold compose.
   apply (H9 (f j))
    [elim (H j H13 H12).elim H15.rewrite < H18.reflexivity
    |elim (H j H13 H12).elim H15.assumption.
    |apply (H5 j H12 H13 H14)
    ]
  ]
qed.

theorem permut_p_S_to_permut_p: \forall f.\forall p.\forall n.
permut_p f p (S n) \to (f (S n)) = (S n) \to permut_p f p n.
intros.
unfold permut_p.
intros.
split
  [elim (H i (le_S i n H2) H3).split
    [elim H4.
     elim (le_to_or_lt_eq (f i) (S n))
      [apply le_S_S_to_le.assumption
      |absurd (f i = (S n))
        [assumption
        |rewrite < H1.
         apply H5
          [rewrite < H8.assumption
          |apply le_n
          |unfold.intro.
           apply (not_le_Sn_n n).rewrite < H9.assumption
          ]   
        ]
      |assumption
      ]
    |elim H4.assumption
    ]
  |intros.
   elim (H i (le_S i n H2) H3).
   apply H8
    [assumption|apply le_S.assumption|assumption]
  ]
qed.

lemma permut_p_transpose: \forall p.\forall i,j,n.
i \le n \to j \le n \to p i = p j \to
permut_p (transpose i j) p n.
unfold permut_p.intros.
split
  [split
    [unfold transpose.
     apply (eqb_elim i1 i)
      [intro.
       apply (eqb_elim i1 j)
        [simplify.intro.assumption
        |simplify.intro.assumption
        ]
      |intro.
       apply (eqb_elim i1 j)
        [simplify.intro.assumption
        |simplify.intro.assumption
        ]
      ]
    |unfold transpose.
     apply (eqb_elim i1 i)
      [intro.
       apply (eqb_elim i1 j)
        [simplify.intro.rewrite < H6.assumption
        |simplify.intro.rewrite < H2.rewrite < H5.assumption
        ]
      |intro.
       apply (eqb_elim i1 j)
        [simplify.intro.rewrite > H2.rewrite < H6.assumption
        |simplify.intro.assumption
        ]
      ]
    ]
  |intros.unfold Not.
   intro.apply H7.
   apply (injective_transpose ? ? ? ? H8).
  ]
qed.

theorem eq_map_iter_p_k: \forall f,g.\forall p.\forall a,k,n:nat.
p (S n-k) = true \to (\forall i. (S n)-k < i \to i \le (S n) \to (p i) = false) \to
map_iter_p (S n) p g a f = map_iter_p (S n-k) p g a f.
intros 5.
elim k 3
  [rewrite < minus_n_O.reflexivity
  |apply (nat_case n1)
    [intros.
     rewrite > map_iter_p_S_false
      [reflexivity
      |apply H2[simplify.apply lt_O_S.|apply le_n]
      ]
    |intros.
     rewrite > map_iter_p_S_false
      [rewrite > (H m H1)
        [reflexivity
        |intros.
         apply (H2 i H3).
         apply le_S.
         assumption
        ]
      |apply H2[autobatch |apply le_n]
      ]
    ]
  ]
qed.

theorem eq_map_iter_p_a: \forall p.\forall f.\forall g. \forall a,n:nat. 
(\forall i.i \le n \to p i = false) \to map_iter_p n p g a f = a.
intros 5.
elim n
  [simplify.reflexivity
  |rewrite > map_iter_p_S_false
    [apply H.
     intros.
     apply H1.apply le_S.assumption
    |apply H1.apply le_n
    ]
  ]
qed.
 
theorem eq_map_iter_p_transpose: \forall p.\forall f.associative nat f \to
symmetric2 nat nat f \to \forall g. \forall a,k,n:nat. k < n \to
(p (S n) = true) \to (p (n-k)) = true \to (\forall i. n-k < i \to i \le n \to (p i) = false)
\to map_iter_p (S n) p g a f = map_iter_p (S n) p (\lambda m. g (transpose (n-k) (S n) m)) a f.
intros 8.
apply (nat_case n)
  [intro.absurd (k < O)
    [assumption|apply le_to_not_lt.apply le_O_n]
  |intros.
   rewrite > (map_iter_p_S_true ? ? ? ? ? H3).
   rewrite > (map_iter_p_S_true ? ? ? ? ? H3).
   rewrite > (eq_map_iter_p_k ? ? ? ? ? ? H4 H5).
   rewrite > (eq_map_iter_p_k ? ? ? ? ? ? H4 H5).
   generalize in match H4.
   rewrite > minus_Sn_m
    [intro.
     rewrite > (map_iter_p_S_true ? ? ? ? ? H6).
     rewrite > (map_iter_p_S_true ? ? ? ? ? H6).
     rewrite > transpose_i_j_j.
     rewrite > transpose_i_j_i.
     cut (map_iter_p (m-k) p g a f =
      map_iter_p (m-k) p (\lambda x.g (transpose (S(m-k)) (S(S m)) x)) a f)
      [rewrite < Hcut.
       rewrite < H.
       rewrite < H1 in \vdash (? ? (? % ?) ?).
       rewrite > H.
       reflexivity
      |apply eq_map_iter_p.
       intros.unfold transpose.
       cut (eqb m1 (S (m-k)) =false)
        [cut (eqb m1 (S (S m)) =false)
          [rewrite > Hcut.
           rewrite > Hcut1.
           reflexivity
          |apply not_eq_to_eqb_false.
           apply lt_to_not_eq.
           apply (le_to_lt_to_lt ? m)
            [apply (trans_le ? (m-k))
              [assumption| autobatch]
            |apply le_S.apply le_n
            ]
          ]
        |apply not_eq_to_eqb_false.
         apply lt_to_not_eq.
         unfold. autobatch;
        ]
      ]
    |apply le_S_S_to_le.assumption
    ]
  ]
qed.

theorem eq_map_iter_p_transpose1: \forall p.\forall f.associative nat f \to
symmetric2 nat nat f \to \forall g. \forall a,k1,k2,n:nat. O < k1 \to k1 < k2 \to k2 \le n \to
(p k1) = true \to (p k2) = true \to (\forall i. k1 < i \to i < k2 \to (p i) = false)
\to map_iter_p n p g a f = map_iter_p n p (\lambda m. g (transpose k1 k2 m)) a f.
intros 10.
elim n 2
  [absurd (k2 \le O)
    [assumption|apply lt_to_not_le.apply (trans_lt ? k1 ? H2 H3)]
  |apply (eqb_elim (S n1) k2)
   [intro.
    rewrite < H4.
    intros.
    cut (k1 = n1 - (n1 -k1))
     [rewrite > Hcut.
      apply (eq_map_iter_p_transpose p f H H1 g a (n1-k1))
        [cut (k1 \le n1)[autobatch|autobatch]
        |assumption
        |rewrite < Hcut.assumption
        |rewrite < Hcut.intros.
         apply (H9 i H10).unfold.autobatch   
       ]
     |apply sym_eq.
       apply plus_to_minus.
       autobatch;
     ]
   |intros.
     cut ((S n1) \neq k1)
      [apply (bool_elim ? (p (S n1)))
       [intro. 
        rewrite > map_iter_p_S_true
          [rewrite > map_iter_p_S_true
            [cut ((transpose k1 k2 (S n1)) = (S n1))
              [rewrite > Hcut1.
               apply eq_f.
               apply (H3 H5)
                [elim (le_to_or_lt_eq ? ? H6)
                  [autobatch
                  |absurd (S n1=k2)[apply sym_eq.assumption|assumption]
                  ]
                |assumption
                |assumption
                |assumption
                ]
              |unfold transpose.
               rewrite > (not_eq_to_eqb_false ? ? Hcut).
               rewrite > (not_eq_to_eqb_false ? ? H4).
               reflexivity
              ]
            |assumption
            ]
          |assumption
          ]
        |intro.
          rewrite > map_iter_p_S_false
          [rewrite > map_iter_p_S_false
            [apply (H3 H5)
              [elim (le_to_or_lt_eq ? ? H6)
                [autobatch
                |absurd (S n1=k2)[apply sym_eq.assumption|assumption]
                ]
              |assumption
              |assumption
              |assumption
              ]
            |assumption
            ]
          |assumption
          ]
        ]
      |unfold.intro.
       absurd (k1 < k2)
        [assumption
        |apply le_to_not_lt.
         rewrite < H10.
         assumption
        ]
      ]
    ]
  ]
qed.

lemma decidable_n:\forall p.\forall n.
(\forall m. m \le n \to (p m) = false) \lor 
(\exists m. m \le n \land (p m) = true \land 
\forall i. m < i \to i \le n \to (p i) = false).
intros.
elim n
  [apply (bool_elim ? (p O))
    [intro.right.
     apply (ex_intro ? ? O).
     split
      [split[apply le_n|assumption]
      |intros.absurd (O<i)[assumption|apply le_to_not_lt.assumption]
      ]
    |intro.left.
     intros.apply (le_n_O_elim m H1).assumption
    ]
  |apply (bool_elim ? (p (S n1)))
    [intro.right.
     apply (ex_intro ? ? (S n1)).
     split
      [split[apply le_n|assumption]
      |intros.absurd (S n1<i)[assumption|apply le_to_not_lt.assumption]
      ]
    |elim H
      [left.
       intros.
       elim (le_to_or_lt_eq m (S n1) H3)
        [apply H1.apply le_S_S_to_le.assumption
        |rewrite > H4.assumption
        ]
      |right.
       elim H1.elim H3.elim H4.
       apply (ex_intro ? ? a).
       split
        [split[apply le_S.assumption|assumption]
        |intros.elim (le_to_or_lt_eq i (S n1) H9)
          [apply H5[assumption|apply le_S_S_to_le.assumption]
          |rewrite > H10.assumption
          ]
        ]
      ]
    ]
  ]
qed.

lemma decidable_n1:\forall p.\forall n,j. j \le n \to (p j)=true \to
(\forall m. j < m \to m \le n \to (p m) = false) \lor 
(\exists m. j < m \land m \le n \land (p m) = true \land 
\forall i. m < i \to i \le n \to (p i) = false).
intros.
elim (decidable_n p n)
  [absurd ((p j)=true)
    [assumption
    |unfold.intro.
     apply not_eq_true_false.
     rewrite < H3.
     apply H2.assumption
    ]
  |elim H2.clear H2.
   apply (nat_compare_elim j a)
    [intro.
     right.
     apply (ex_intro ? ? a).
     elim H3.clear H3.
     elim H4.clear H4.
     split
      [split
        [split
          [assumption|assumption]
        |assumption
        ]
      |assumption
      ]
    |intro.
     rewrite > H2.
     left.
     elim H3 2.assumption
    |intro.
     absurd (p j = true)
      [assumption
      |unfold.intro.
       apply not_eq_true_false.
       rewrite < H4.
       elim H3.clear H3.
       apply (H6 j H2).assumption
      ]
    ]
  ]
qed.    

lemma decidable_n2:\forall p.\forall n,j. j \le n \to (p j)=true \to
(\forall m. j < m \to m \le n \to (p m) = false) \lor 
(\exists m. j < m \land m \le n \land (p m) = true \land 
\forall i. j < i \to i < m \to (p i) = false).
intros 3.
elim n
  [left.
   apply (le_n_O_elim j H).intros.
   absurd (m \le O)
    [assumption|apply lt_to_not_le.assumption]
  |elim (le_to_or_lt_eq ? ? H1)
    [cut (j \le n1)
      [elim (H Hcut H2)
        [apply (bool_elim ? (p (S n1)))
          [intro.
           right.
           apply (ex_intro ? ? (S n1)).
           split
            [split
              [split
                [assumption|apply le_n]
              |assumption
              ]
            |intros.
             apply (H4 i H6).
             apply le_S_S_to_le.
             assumption
            ]
          |intro.
           left.
           intros.
           elim (le_to_or_lt_eq ? ? H7)
            [apply H4
              [assumption|apply le_S_S_to_le.assumption]
            |rewrite > H8.assumption
            ]
          ]
        |right.
         elim H4.clear H4.
         elim H5.clear H5.
         elim H4.clear H4.
         elim H5.clear H5.
         apply (ex_intro ? ? a).
         split
          [split
            [split[assumption|apply le_S.assumption]
            |assumption
            ]
          |assumption
          ]
        ]
      |apply le_S_S_to_le.
       assumption
      ]
    |left.
     intros.
     absurd (j < m)
      [assumption
      |apply le_to_not_lt.
       rewrite > H3.
       assumption
      ]
    ]
  ]
qed.

theorem eq_map_iter_p_transpose2: \forall p.\forall f.associative nat f \to
symmetric2 nat nat f \to \forall g. \forall a,k,n:nat. O < k \to k \le n \to
(p (S n) = true) \to (p k) = true 
\to map_iter_p (S n) p g a f = map_iter_p (S n) p (\lambda m. g (transpose k (S n) m)) a f.
intros 10.
cut (k = (S n)-(S n -k))
  [generalize in match H3.clear H3.
   generalize in match g.
   generalize in match H2.clear H2.
   rewrite > Hcut.
   (*generalize in match Hcut.clear Hcut.*)
   (* generalize in match H3.clear H3.*)
   (* something wrong here 
     rewrite > Hcut in \vdash (?\rarr ?\rarr %). *)
   apply (nat_elim1 (S n - k)).
     intros.
     elim (decidable_n2 p n (S n -m) H4 H6)
      [apply (eq_map_iter_p_transpose1 p f H H1 f1 a)
        [assumption.
        |unfold.autobatch.
        |apply le_n
        |assumption
        |assumption
        |intros.apply H7
          [assumption|apply le_S_S_to_le.assumption]
        ]
      |elim H7.clear H7.
       elim H8.clear H8.
       elim H7.clear H7.
       elim H8.clear H8.
       apply (trans_eq  ? ? 
        (map_iter_p (S n) p (\lambda i.f1 (transpose a1 (S n) (transpose (S n -m) a1 i))) a f))
        [apply (trans_eq  ? ? 
         (map_iter_p (S n) p (\lambda i.f1 (transpose a1 (S n) i)) a f))
          [cut (a1 = (S n -(S n -a1)))
            [rewrite > Hcut1.
             apply H2
              [apply lt_plus_to_lt_minus
                [apply le_S.assumption
                |rewrite < sym_plus.
                 apply lt_minus_to_lt_plus.
                 assumption
                ]
              |rewrite < Hcut1.
               apply (trans_lt ? (S n -m))[assumption|assumption]
              |rewrite < Hcut1.assumption
              |assumption
              |rewrite < Hcut1.assumption
              ]
           |apply minus_m_minus_mn.
            apply le_S.assumption
           ]
         |apply (eq_map_iter_p_transpose1 p f H H1)
          [assumption
          |assumption
          |apply le_S.assumption
          |assumption
          |assumption
          |assumption
          ]
        ]
      |apply (trans_eq  ? ? 
        (map_iter_p (S n) p (\lambda i.f1 (transpose a1 (S n) (transpose (S n -m) a1 (transpose (S n -(S n -a1)) (S n) i)))) a f)) 
        [cut (a1 = (S n) -(S n -a1))
          [apply H2 
            [apply lt_plus_to_lt_minus
              [apply le_S.assumption
              |rewrite < sym_plus.
               apply lt_minus_to_lt_plus.
               assumption
              ]
            |rewrite < Hcut1.
             apply (trans_lt ? (S n -m))[assumption|assumption]
            |rewrite < Hcut1.assumption
            |assumption
            |rewrite < Hcut1.assumption
            ]
          |apply minus_m_minus_mn.
           apply le_S.assumption
          ]
        |apply eq_map_iter_p.
         cut (a1 = (S n) -(S n -a1))
          [intros.
           apply eq_f.
           rewrite < Hcut1.
           rewrite < transpose_i_j_j_i.
           rewrite > (transpose_i_j_j_i (S n -m)).
           rewrite > (transpose_i_j_j_i a1 (S n)).
           rewrite > (transpose_i_j_j_i (S n -m)).
           apply sym_eq.
           apply eq_transpose
            [unfold.intro.
             apply (not_le_Sn_n n).
             rewrite < H12.assumption
            |unfold.intro.
             apply (not_le_Sn_n n).
             rewrite > H12.assumption
            |unfold.intro.
             apply (not_le_Sn_n a1).
             rewrite < H12 in \vdash (? (? %) ?).assumption
            ]
          |apply minus_m_minus_mn.
           apply le_S.assumption
          ]
        ]
      ]
    ]
  |apply minus_m_minus_mn.
   apply le_S.assumption
  ]
qed.

theorem eq_map_iter_p_transpose3: \forall p.\forall f.associative nat f \to
symmetric2 nat nat f \to \forall g. \forall a,k,n:nat. O < k \to k \le (S n) \to
(p (S n) = true) \to (p k) = true 
\to map_iter_p (S n) p g a f = map_iter_p (S n) p (\lambda m. g (transpose k (S n) m)) a f.
intros.
elim (le_to_or_lt_eq ? ? H3)
  [apply (eq_map_iter_p_transpose2 p f H H1 g a k n H2)
    [apply le_S_S_to_le.assumption|assumption|assumption]
  |rewrite > H6.
   apply eq_map_iter_p.
   intros.
   apply eq_f.apply sym_eq. apply transpose_i_i. 
  ]
qed.

lemma permut_p_O: \forall p.\forall h.\forall n.
permut_p h p n \to p O = false \to \forall m. (S m) \le n \to p (S m) = true \to O < h(S m).
intros.unfold permut_p in H.
apply not_le_to_lt.unfold.intro.
elim (H (S m) H2 H3).
elim H5.
absurd (p (h (S m)) = true)
  [assumption
  |apply (le_n_O_elim ? H4).
   unfold.intro.
   apply not_eq_true_false.
   rewrite < H9.rewrite < H1.reflexivity
  ]
qed.

theorem eq_map_iter_p_permut: \forall p.\forall f.associative nat f \to
symmetric2 nat nat f \to \forall n.\forall g. \forall h.\forall a:nat.
permut_p h p n \to p O = false \to
map_iter_p n p g a f = map_iter_p n p (compose ? ? ? g h) a f .
intros 5.
elim n
  [simplify.reflexivity 
  |apply (bool_elim ? (p (S n1)))
    [intro.
     apply (trans_eq ? ? (map_iter_p (S n1) p (\lambda m.g ((transpose (h (S n1)) (S n1)) m)) a f))
      [unfold permut_p in H3.
       elim (H3 (S n1) (le_n ?) H5).
       elim H6. clear H6.
       apply (eq_map_iter_p_transpose3 p f H H1 g a (h(S n1)) n1)
        [apply (permut_p_O ? ? ? H3 H4)
          [apply le_n|assumption]
        |assumption
        |assumption
        |assumption
        ]
      |apply (trans_eq ? ? (map_iter_p (S n1) p (\lambda m.
        (g(transpose (h (S n1)) (S n1) 
         (transpose (h (S n1)) (S n1) (h m)))) ) a f))
        [rewrite > (map_iter_p_S_true ? ? ? ? ? H5).
         rewrite > (map_iter_p_S_true ? ? ? ? ? H5).
         apply eq_f2
          [rewrite > transpose_i_j_j.
           rewrite > transpose_i_j_i.
           rewrite > transpose_i_j_j.
           reflexivity
          |apply (H2 (\lambda m.(g(transpose (h (S n1)) (S n1) m))) ?)
            [unfold.intros.
             split
              [split
                [simplify.
                 unfold permut_p in H3.
                 elim (H3 i (le_S ? ? H6) H7).
                 elim H8. clear H8.
                 elim (le_to_or_lt_eq ? ? H10)
                  [unfold transpose.
                   rewrite > (not_eq_to_eqb_false ? ? (lt_to_not_eq ? ? H8)). 
                   cut (h i \neq h (S n1))
                    [rewrite > (not_eq_to_eqb_false ? ? Hcut). 
                     simplify.
                     apply le_S_S_to_le.
                     assumption
                    |apply H9
                      [apply H5
                      |apply le_n
                      |apply lt_to_not_eq.
                       unfold.apply le_S_S.assumption
                      ]
                    ]
                  |rewrite > H8.
                   apply (eqb_elim (S n1) (h (S n1)))
                    [intro.
                     absurd (h i = h (S n1))
                      [rewrite > H8.
                       assumption
                      |apply H9
                        [assumption
                        |apply le_n
                        |apply lt_to_not_eq.
                         unfold.apply le_S_S.assumption
                        ]
                      ]
                    |intro.
                     unfold transpose.
                     rewrite > (not_eq_to_eqb_false ? ? H12).
                     rewrite > (eq_to_eqb_true ? ? (refl_eq ? (S n1))).
                     simplify.
                     elim (H3 (S n1) (le_n ? ) H5).
                     elim H13.clear H13.
                     elim (le_to_or_lt_eq ? ? H15)
                      [apply le_S_S_to_le.assumption
                      |apply False_ind.
                       apply H12.
                       apply sym_eq.assumption
                      ]
                    ]
                  ]
                |simplify.
                 unfold permut_p in H3.
                 unfold transpose.
                 apply (eqb_elim (h i) (S n1))
                  [intro.
                   apply (eqb_elim (h i) (h (S n1)))
                    [intro.simplify.assumption
                    |intro.simplify.
                     elim (H3 (S n1) (le_n ? ) H5).
                     elim H10. assumption
                    ]
                  |intro.
                   apply (eqb_elim (h i) (h (S n1)))
                    [intro.simplify.assumption
                    |intro.simplify.
                     elim (H3 i (le_S ? ? H6) H7).
                     elim H10. assumption
                    ]
                  ]
                ]
              |simplify.intros.unfold Not.intro.
               unfold permut_p in H3.
               elim (H3 i (le_S i ? H6) H7).
               apply (H13 j H8 (le_S j ? H9) H10).
               apply (injective_transpose ? ? ? ? H11)
              ]
            |assumption
            ]
          ]
        |apply eq_map_iter_p.
         intros.
         rewrite > transpose_transpose.reflexivity
        ]
      ]
  |intro.
   rewrite > (map_iter_p_S_false ? ? ? ? ? H5).
   rewrite > (map_iter_p_S_false ? ? ? ? ? H5).
   apply H2
    [unfold permut_p.
     unfold permut_p in H3.
     intros.
     elim (H3 i (le_S i ? H6) H7).
     elim H8.
      split
        [split
          [elim (le_to_or_lt_eq ? ? H10)
            [apply le_S_S_to_le.assumption
            |absurd (p (h i) = true)
              [assumption
              |rewrite > H12.
               rewrite > H5.
               unfold.intro.apply not_eq_true_false.
               apply sym_eq.assumption
              ]
            ]
          |assumption
          ]
        |intros.
         apply H9
          [assumption|apply (le_S ? ? H13)|assumption]
        ]
      |assumption
      ]
    ]
  ]           
qed.
 
