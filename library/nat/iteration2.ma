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

set "baseuri" "cic:/matita/nat/iteration2.ma".

include "nat/primes.ma".
include "nat/ord.ma".

let rec sigma_p n p (g:nat \to nat) \def
  match n with
   [ O \Rightarrow O
   | (S k) \Rightarrow 
      match p k with
      [true \Rightarrow (g k)+(sigma_p k p g)
      |false \Rightarrow sigma_p k p g]
   ].
   
theorem true_to_sigma_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to nat.
p n = true \to sigma_p (S n) p g = 
(g n)+(sigma_p n p g).
intros.simplify.
rewrite > H.reflexivity.
qed.
   
theorem false_to_sigma_p_Sn: 
\forall n:nat. \forall p:nat \to bool. \forall g:nat \to nat.
p n = false \to sigma_p (S n) p g = sigma_p n p g.
intros.simplify.
rewrite > H.reflexivity.
qed.

theorem eq_sigma_p: \forall p1,p2:nat \to bool.
\forall g1,g2: nat \to nat.\forall n.
(\forall x.  x < n \to p1 x = p2 x) \to
(\forall x.  x < n \to g1 x = g2 x) \to
sigma_p n p1 g1 = sigma_p n p2 g2.
intros 5.elim n
  [reflexivity
  |apply (bool_elim ? (p1 n1))
    [intro.
     rewrite > (true_to_sigma_p_Sn ? ? ? H3).
     rewrite > true_to_sigma_p_Sn
      [apply eq_f2
        [apply H2.apply le_n.
        |apply H
          [intros.apply H1.apply le_S.assumption
          |intros.apply H2.apply le_S.assumption
          ]
        ]
      |rewrite < H3.apply sym_eq.apply H1.apply le_n
      ]
    |intro.
     rewrite > (false_to_sigma_p_Sn ? ? ? H3).
     rewrite > false_to_sigma_p_Sn
      [apply H
        [intros.apply H1.apply le_S.assumption
        |intros.apply H2.apply le_S.assumption
        ]
      |rewrite < H3.apply sym_eq.apply H1.apply le_n
      ]
    ]
  ]
qed.

theorem sigma_p_false: 
\forall g: nat \to nat.\forall n.sigma_p n (\lambda x.false) g = O.
intros.
elim n[reflexivity|simplify.assumption]
qed.

theorem sigma_p_plus: \forall n,k:nat.\forall p:nat \to bool.
\forall g: nat \to nat.
sigma_p (k+n) p g 
= sigma_p k (\lambda x.p (x+n)) (\lambda x.g (x+n)) + sigma_p n p g.
intros.
elim k
  [reflexivity
  |apply (bool_elim ? (p (n1+n)))
    [intro.
     simplify in \vdash (? ? (? % ? ?) ?).    
     rewrite > (true_to_sigma_p_Sn ? ? ? H1).
     rewrite > (true_to_sigma_p_Sn n1 (\lambda x.p (x+n)) ? H1).
     rewrite > assoc_plus.
     rewrite < H.reflexivity
    |intro.
     simplify in \vdash (? ? (? % ? ?) ?).    
     rewrite > (false_to_sigma_p_Sn ? ? ? H1).
     rewrite > (false_to_sigma_p_Sn n1 (\lambda x.p (x+n)) ? H1).
     assumption.
    ]
  ]
qed.

theorem false_to_eq_sigma_p: \forall n,m:nat.n \le m \to
\forall p:nat \to bool.
\forall g: nat \to nat. (\forall i:nat. n \le i \to i < m \to
p i = false) \to sigma_p m p g = sigma_p n p g.
intros 5.
elim H
  [reflexivity
  |simplify.
   rewrite > H3
    [simplify.
     apply H2.
     intros.
     apply H3[apply H4|apply le_S.assumption]
    |assumption
    |apply le_n
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
elim n
  [simplify.reflexivity
  |apply (bool_elim ? (p1 n1))
    [intro.
     rewrite > (true_to_sigma_p_Sn ? ? ? H1).
     simplify in \vdash (? ? (? % ? ?) ?);
     rewrite > sigma_p_plus.
     rewrite < H.
     apply eq_f2
      [apply eq_sigma_p
        [intros.
         rewrite > sym_plus.
         rewrite > (div_plus_times ? ? ? H2).
         rewrite > (mod_plus_times ? ? ? H2).
         rewrite > H1.
         simplify.reflexivity
        |intros.
         rewrite > sym_plus.
         rewrite > (div_plus_times ? ? ? H2).
         rewrite > (mod_plus_times ? ? ? H2).
         rewrite > H1.
         simplify.reflexivity.   
        ]
      |reflexivity
      ]
    |intro.
     rewrite > (false_to_sigma_p_Sn ? ? ? H1).
     simplify in \vdash (? ? (? % ? ?) ?);
     rewrite > sigma_p_plus.
     rewrite > H.
     apply (trans_eq ? ? (O+(sigma_p n1 p1 (\lambda x:nat.sigma_p m p2 (g x)))))
      [apply eq_f2
        [rewrite > (eq_sigma_p ? (\lambda x.false) ? (\lambda x:nat.g ((x+n1*m)/m) ((x+n1*m)\mod m)))
          [apply sigma_p_false
          |intros.
           rewrite > sym_plus.
           rewrite > (div_plus_times ? ? ? H2).
           rewrite > (mod_plus_times ? ? ? H2).
           rewrite > H1.
           simplify.reflexivity
          |intros.reflexivity.
          ]
        |reflexivity
        ]
      |reflexivity   
      ]
    ]
  ]
qed.

lemma sigma_p_gi: \forall g: nat \to nat.
\forall n,i.\forall p:nat \to bool.i < n \to p i = true \to 
sigma_p n p g = g i + sigma_p n (\lambda x. andb (p x) (notb (eqb x i))) g.
intros 2.
elim n
  [apply False_ind.
   apply (not_le_Sn_O i).
   assumption
  |apply (bool_elim ? (p n1));intro
    [elim (le_to_or_lt_eq i n1)
      [rewrite > true_to_sigma_p_Sn
        [rewrite > true_to_sigma_p_Sn
          [rewrite < assoc_plus.
           rewrite < sym_plus in \vdash (? ? ? (? % ?)).
           rewrite > assoc_plus.
           apply eq_f2
            [reflexivity
            |apply H[assumption|assumption]
            ]
          |rewrite > H3.simplify.
           change with (notb (eqb n1 i) = notb false).
           apply eq_f.
           apply not_eq_to_eqb_false.
           unfold Not.intro.
           apply (lt_to_not_eq ? ? H4).
           apply sym_eq.assumption
          ]
        |assumption
        ]
      |rewrite > true_to_sigma_p_Sn
        [rewrite > H4.
         apply eq_f2
          [reflexivity
          |rewrite > false_to_sigma_p_Sn
            [apply eq_sigma_p
              [intros.
               elim (p x)
                [simplify.
                 change with (notb false = notb (eqb x n1)).
                 apply eq_f.
                 apply sym_eq. 
                 apply not_eq_to_eqb_false.
                 apply (lt_to_not_eq ? ? H5)
                |reflexivity
                ]
              |intros.reflexivity
              ]
            |rewrite > H3.
             rewrite > (eq_to_eqb_true ? ? (refl_eq ? n1)).
             reflexivity
            ]
          ]
        |assumption
        ]
      |apply le_S_S_to_le.assumption
      ]
    |rewrite > false_to_sigma_p_Sn
      [elim (le_to_or_lt_eq i n1)
        [rewrite > false_to_sigma_p_Sn
          [apply H[assumption|assumption]
          |rewrite > H3.reflexivity
          ]
        |apply False_ind. 
         apply not_eq_true_false.
         rewrite < H2.
         rewrite > H4.
         assumption
        |apply le_S_S_to_le.assumption
        ]
      |assumption
      ]
    ] 
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
intros 4.
elim n
  [generalize in match H5.
   elim n1
    [reflexivity
    |apply (bool_elim ? (p2 n2));intro
      [apply False_ind.
       apply (not_le_Sn_O (h1 n2)).
       apply H7
        [apply le_n|assumption]
      |rewrite > false_to_sigma_p_Sn
        [apply H6.
         intros.  
            apply H7[apply le_S.apply H9|assumption]
        |assumption
        ]
      ]
    ]
  |apply (bool_elim ? (p1 n1));intro
    [rewrite > true_to_sigma_p_Sn
      [rewrite > (sigma_p_gi g n2 (h n1))
        [apply eq_f2
          [reflexivity
          |apply H
            [intros.
             rewrite > H1
              [simplify.
               change with ((\not eqb (h i) (h n1))= \not false).
               apply eq_f.
               apply not_eq_to_eqb_false.
               unfold Not.intro.
               apply (lt_to_not_eq ? ? H8).
               rewrite < H2
                [rewrite < (H2 n1)
                  [apply eq_f.assumption|apply le_n|assumption]
                |apply le_S.assumption
                |assumption
                ]
              |apply le_S.assumption
              |assumption
              ]
            |intros.
             apply H2[apply le_S.assumption|assumption]
            |intros.
             apply H3[apply le_S.assumption|assumption]
            |intros.
             apply H4
              [assumption
              |generalize in match H9.
               elim (p2 j)
                [reflexivity|assumption]
              ]
            |intros.
             apply H5
              [assumption
              |generalize in match H9.
               elim (p2 j)
                [reflexivity|assumption]
              ]
            |intros.
             elim (le_to_or_lt_eq (h1 j) n1)
              [assumption
              |generalize in match H9.
               elim (p2 j)
                [simplify in H11.
                 absurd (j = (h n1))
                  [rewrite < H10.
                   rewrite > H5
                    [reflexivity|assumption|auto]
                  |apply eqb_false_to_not_eq.
                   generalize in match H11.
                   elim (eqb j (h n1))
                    [apply sym_eq.assumption|reflexivity]
                  ]
                |simplify in H11.
                 apply False_ind.
                 apply not_eq_true_false.
                 apply sym_eq.assumption
                ]
              |apply le_S_S_to_le.
               apply H6
                [assumption
                |generalize in match H9.
                 elim (p2 j)
                  [reflexivity|assumption]
                ]
              ]
            ]
          ]
        |apply H3[apply le_n|assumption]
        |apply H1[apply le_n|assumption]
        ]
      |assumption
      ]
    |rewrite > false_to_sigma_p_Sn
     [apply H
       [intros.apply H1[apply le_S.assumption|assumption]
       |intros.apply H2[apply le_S.assumption|assumption]
       |intros.apply H3[apply le_S.assumption|assumption]
       |intros.apply H4[assumption|assumption]
       |intros.apply H5[assumption|assumption]
       |intros.
        elim (le_to_or_lt_eq (h1 j) n1)
          [assumption
          |absurd (j = (h n1))
            [rewrite < H10.
             rewrite > H5
               [reflexivity|assumption|assumption]
            |unfold Not.intro.
             apply not_eq_true_false.
             rewrite < H7.
             rewrite < H10.
             rewrite > H4
              [reflexivity|assumption|assumption]
            ]
          |apply le_S_S_to_le.
           apply H6[assumption|assumption]
          ]
        ]
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

theorem sigma_p_divides: 
\forall n,m,p:nat.O < n \to prime p \to Not (divides p n) \to 
\forall g: nat \to nat.
sigma_p (S (n*(exp p m))) (\lambda x.divides_b x (n*(exp p m))) g =
sigma_p (S n) (\lambda x.divides_b x n)
  (\lambda x.sigma_p (S m) (\lambda y.true) (\lambda y.g (x*(exp p y)))).
intros.
cut (O < p)
  [rewrite < sigma_p2.
   apply (trans_eq ? ? 
    (sigma_p (S n*S m) (\lambda x:nat.divides_b (x/S m) n)
       (\lambda x:nat.g (x/S m*(p)\sup(x\mod S m)))))
    [apply sym_eq.
     apply (eq_sigma_p_gh g ? (p_ord_times p (S m)))
      [intros.
       lapply (divides_b_true_to_lt_O ? ? H H4).
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
           auto
          ]
        ]
      |intros.
       lapply (divides_b_true_to_lt_O ? ? H H4).
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
          [auto|assumption]
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
             |apply (divides_b_true_to_lt_O ? ? ? H4).
               rewrite > (times_n_O O).
               apply lt_times
               [assumption|apply lt_O_exp.assumption]
             ]
           |cut (n = ord_rem (n*(exp p m)) p)
              [rewrite > Hcut2.
               apply divides_to_divides_ord_rem
                [apply (divides_b_true_to_lt_O ? ? ? H4).
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
            [apply (divides_b_true_to_lt_O ? ? ? H4).
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
              |apply (divides_b_true_to_lt_O ? ? ? H4).
               rewrite > (times_n_O O).
               apply lt_times
                [assumption|apply lt_O_exp.assumption]
              ]
           |cut (m = ord (n*(exp p m)) p)
             [apply le_S_S.
              rewrite > Hcut2.
              apply divides_to_le_ord
               [apply (divides_b_true_to_lt_O ? ? ? H4).
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
            [apply (divides_b_true_to_lt_O ? ? ? H4).
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
            [apply (divides_b_true_to_lt_O ? ? ? H4).
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
              [apply (divides_b_true_to_lt_O ? ? ? H4).
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
  |apply eq_sigma_p
    [intros.
     elim (divides_b (x/S m) n);reflexivity
    |intros.reflexivity
    ]
  ]
|elim H1.apply lt_to_le.assumption
]
qed.
    

