(**************************************************************************)
(*       ___	                                                            *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||       A.Asperti, C.Sacerdoti Coen,                          *)
(*      ||A||       E.Tassi, S.Zacchiroli                                 *)
(*      \   /                                                             *)
(*       \ /        Matita is distributed under the terms of the          *)
(*        v         GNU Lesser General Public License Version 2.1         *)
(*                                                                        *)
(**************************************************************************)

include "nat/primes.ma".
include "Z/sigma_p.ma".
include "Z/times.ma".

definition dirichlet_product : (nat \to Z) \to (nat \to Z) \to nat \to Z \def
\lambda f,g.\lambda n.
sigma_p (S n) 
 (\lambda d.divides_b d n) (\lambda d. (f d)*(g (div n d))).

(* dirichlet_product is associative only up to extensional equality *)
theorem associative_dirichlet_product: 
\forall f,g,h:nat\to Z.\forall n:nat.O < n \to
dirichlet_product (dirichlet_product f g) h n
 = dirichlet_product f (dirichlet_product g h) n.
intros.
unfold dirichlet_product.
unfold dirichlet_product.
apply (trans_eq ? ? 
(sigma_p (S n) (\lambda d:nat.divides_b d n)
(\lambda d:nat
 .sigma_p (S n) (\lambda d1:nat.divides_b d1 d) (\lambda d1:nat.f d1*g (d/d1)*h (n/d)))))
  [apply eq_sigma_p1
    [intros.reflexivity
    |intros.
     apply (trans_eq ? ? 
     (sigma_p (S x) (\lambda d1:nat.divides_b d1 x) (\lambda d1:nat.f d1*g (x/d1)*h (n/x))))
      [apply Ztimes_sigma_pr
      |(* hint solleva unification uncertain ?? *)
       apply sym_eq.
       apply false_to_eq_sigma_p
        [assumption
        |intros.
         apply not_divides_to_divides_b_false
          [apply (lt_to_le_to_lt ? (S x))
            [apply lt_O_S|assumption]
          |unfold Not. intro.
           apply (lt_to_not_le ? ? H3).
           apply divides_to_le
            [apply (divides_b_true_to_lt_O ? ? H H2).
            |assumption
            ]
          ]
        ]
      ]
    ]
  |apply (trans_eq ? ?
   (sigma_p (S n) (\lambda d:nat.divides_b d n)
    (\lambda d:nat
      .sigma_p (S n) (\lambda d1:nat.divides_b d1 (n/d))
      (\lambda d1:nat.f d*g d1*h ((n/d)/d1)))))
    [apply (trans_eq ? ?
      (sigma_p (S n) (\lambda d:nat.divides_b d n)
       (\lambda d:nat
        .sigma_p (S n) (\lambda d1:nat.divides_b d1 (n/d))
        (\lambda d1:nat.f d*g ((times d d1)/d)*h ((n/times d d1))))))
      [apply (sigma_p2_eq 
        (\lambda d,d1.f d1*g (d/d1)*h (n/d))
        (\lambda d,d1:nat.times d d1) 
        (\lambda d,d1:nat.d) 
        (\lambda d,d1:nat.d1) 
        (\lambda d,d1:nat.d/d1)
        (S n)
        (S n)
        (S n)
        (S n)
        ?
        ?
        (\lambda d,d1:nat.divides_b d1 d)
        (\lambda d,d1:nat.divides_b d1 (n/d))
        )
        [intros.
         split
          [split
            [split
              [split
                [split
                  [apply divides_to_divides_b_true1
                    [assumption
                    |apply (witness ? ? ((n/i)/j)).
                     rewrite > assoc_times.
                     rewrite > sym_times in \vdash (? ? ? (? ? %)).
                     rewrite > divides_to_div
                      [rewrite > sym_times. 
                       rewrite > divides_to_div
                        [reflexivity
                        |apply divides_b_true_to_divides.
                         assumption
                        ]
                      |apply divides_b_true_to_divides.
                       assumption
                      ]
                    ]
                  |apply divides_to_divides_b_true
                    [apply (divides_b_true_to_lt_O ? ? H H3)
                    |apply (witness ? ? j).
                     reflexivity
                    ]
                  ]
                |reflexivity
                ]
              |rewrite < sym_times.
               rewrite > (plus_n_O (j*i)).
               apply div_plus_times.
               apply (divides_b_true_to_lt_O ? ? H H3)
              ]
            |apply (le_to_lt_to_lt ? (i*(n/i)))
              [apply le_times
                [apply le_n
                |apply divides_to_le
                  [elim (le_to_or_lt_eq ? ? (le_O_n (n/i)))
                    [assumption
                    |apply False_ind.
                     apply (lt_to_not_le ? ? H).
                     rewrite < (divides_to_div i n)
                      [rewrite < H5.
                       apply le_n
                      |apply divides_b_true_to_divides.
                       assumption
                      ]
                    ]
                  |apply divides_b_true_to_divides.
                   assumption
                  ]
                ]
              |rewrite < sym_times.
               rewrite > divides_to_div
                [apply le_n
                |apply divides_b_true_to_divides.
                 assumption
                ]
              ]
            ]
          |assumption
          ]
        |intros.
         split
          [split
            [split
              [split
                [split
                  [apply divides_to_divides_b_true1
                    [assumption
                    |apply (transitive_divides ? i)
                      [apply divides_b_true_to_divides.
                       assumption
                      |apply divides_b_true_to_divides.
                       assumption
                      ]
                    ]
                  |apply divides_to_divides_b_true
                    [apply (divides_b_true_to_lt_O i (i/j))
                      [apply (divides_b_true_to_lt_O ? ? ? H3).
                       assumption
                      |apply divides_to_divides_b_true1
                        [apply (divides_b_true_to_lt_O ? ? ? H3).
                         assumption
                        |apply (witness ? ? j).
                         apply sym_eq.
                         apply divides_to_div.
                         apply divides_b_true_to_divides.
                         assumption
                        ]
                      ]
                    |apply (witness ? ? (n/i)).
                     apply (inj_times_l1 j)
                      [apply (divides_b_true_to_lt_O ? ? ? H4).
                       apply (divides_b_true_to_lt_O ? ? ? H3).
                       assumption
                      |rewrite > divides_to_div
                        [rewrite > sym_times in \vdash (? ? ? (? % ?)).
                         rewrite > assoc_times.
                         rewrite > divides_to_div
                          [rewrite > divides_to_div
                            [reflexivity
                            |apply divides_b_true_to_divides.
                             assumption
                            ]
                          |apply divides_b_true_to_divides.
                           assumption
                          ]
                        |apply (transitive_divides ? i)
                          [apply divides_b_true_to_divides.
                           assumption
                          |apply divides_b_true_to_divides.
                           assumption
                          ]
                        ]
                      ]
                    ]
                  ]
                |rewrite < sym_times.
                 apply divides_to_div.
                 apply divides_b_true_to_divides.
                 assumption
                ]
              |reflexivity
              ]
            |assumption
            ]
          |apply (le_to_lt_to_lt ? i)
            [apply le_div.
             apply (divides_b_true_to_lt_O ? ? ? H4).
             apply (divides_b_true_to_lt_O ? ? ? H3).
             assumption
            |assumption
            ]
          ]
        ]
      |apply eq_sigma_p1
        [intros.reflexivity
        |intros.
         apply eq_sigma_p1
          [intros.reflexivity
          |intros.
           apply eq_f2
            [apply eq_f2
              [reflexivity
              |apply eq_f.
               rewrite > sym_times.
               rewrite > (plus_n_O (x1*x)).
               apply div_plus_times.
               apply (divides_b_true_to_lt_O ? ? ? H2).
               assumption
              ]
            |apply eq_f.
             cut (O < x)
              [cut (O < x1)
                [apply (inj_times_l1 (x*x1))
                  [rewrite > (times_n_O O).
                   apply lt_times;assumption
                  |rewrite > divides_to_div
                    [rewrite > sym_times in \vdash (? ? ? (? ? %)).
                     rewrite < assoc_times.
                     rewrite > divides_to_div
                      [rewrite > divides_to_div
                        [reflexivity
                        |apply divides_b_true_to_divides.
                         assumption
                        ]
                      |apply divides_b_true_to_divides.
                       assumption
                      ]
                    |elim (divides_b_true_to_divides ? ? H4).
                     apply (witness ? ? n1).
                     rewrite > assoc_times.
                     rewrite < H5.
                     rewrite < sym_times.
                     apply sym_eq.
                     apply divides_to_div.
                     apply divides_b_true_to_divides.
                     assumption
                    ]
                  ]
                |apply (divides_b_true_to_lt_O ? ? ? H4).
                 apply (lt_times_n_to_lt x)
                  [assumption
                  |simplify.
                   rewrite > divides_to_div
                    [assumption
                    |apply (divides_b_true_to_divides ? ? H2).
                     assumption
                    ]
                  ]
                ]
              |apply (divides_b_true_to_lt_O ? ? ? H2).
               assumption
              ]
            ]
          ]
        ]
      ]
    |apply eq_sigma_p1
      [intros.reflexivity
      |intros.
       apply (trans_eq ? ? 
       (sigma_p (S n) (\lambda d1:nat.divides_b d1 (n/x)) (\lambda d1:nat.f x*(g d1*h (n/x/d1)))))
        [apply eq_sigma_p
          [intros.reflexivity
          |intros.apply assoc_Ztimes
          ]
        |apply (trans_eq ? ? 
          (sigma_p (S (n/x)) (\lambda d1:nat.divides_b d1 (n/x)) (\lambda d1:nat.f x*(g d1*h (n/x/d1)))))
          [apply false_to_eq_sigma_p
            [apply le_S_S.
             cut (O < x)
              [apply (le_times_to_le x)
                [assumption
                |rewrite > sym_times.
                 rewrite > divides_to_div
                  [apply le_times_n.
                   assumption
                  |apply divides_b_true_to_divides.
                   assumption
                  ]
                ]
              |apply (divides_b_true_to_lt_O ? ? ? H2).
               assumption
              ]
            |intros.
             apply not_divides_to_divides_b_false
              [apply (trans_le ? ? ? ? H3).
               apply le_S_S.
               apply le_O_n
              |unfold Not.intro.
               apply (le_to_not_lt ? ? H3).
               apply le_S_S.
               apply divides_to_le
                [apply (lt_times_n_to_lt x)
                  [apply (divides_b_true_to_lt_O ? ? ? H2).
                   assumption
                  |simplify.
                   rewrite > divides_to_div
                    [assumption
                    |apply (divides_b_true_to_divides ? ? H2).
                     assumption
                    ]
                  ]
                |assumption
                ]
              ]
            ]
          |apply sym_eq.
           apply Ztimes_sigma_pl
          ]
        ]
      ]
    ]
  ]
qed.

definition is_one: nat \to Z \def 
\lambda n.
  match n with
  [O \Rightarrow OZ
  | (S p) \Rightarrow 
    match p with
    [ O \Rightarrow pos O
    | (S q) \Rightarrow OZ]]
.

theorem is_one_OZ: \forall n. n \neq S O \to is_one n = OZ.
intro.apply (nat_case n)
  [intro.reflexivity
  |intro. apply (nat_case m)
    [intro.apply False_ind.apply H.reflexivity
    |intros.reflexivity
    ]
  ]
qed.

theorem sigma_p_OZ:
\forall p: nat \to bool.\forall n.sigma_p n p (\lambda m.OZ) = OZ.
intros.elim n
  [reflexivity
  |apply (bool_elim ? (p n1));intro
    [rewrite > true_to_sigma_p_Sn
      [rewrite > sym_Zplus. 
       rewrite > Zplus_z_OZ. 
       assumption
      |assumption
      ]
    |rewrite > false_to_sigma_p_Sn
      [assumption
      |assumption
      ]
    ]
  ]
qed.

theorem dirichlet_product_is_one_r: 
\forall f:nat\to Z.\forall n:nat.
  dirichlet_product f is_one n = f n.
intros.
elim n
  [unfold dirichlet_product.
   rewrite > true_to_sigma_p_Sn
    [rewrite > Ztimes_Zone_r.
     rewrite > Zplus_z_OZ.
     reflexivity
    |reflexivity
    ]
  |unfold dirichlet_product.
   rewrite > true_to_sigma_p_Sn
    [rewrite > div_n_n
      [rewrite > Ztimes_Zone_r.
       rewrite < Zplus_z_OZ in \vdash (? ? ? %).
       apply eq_f2
        [reflexivity
        |apply (trans_eq ? ? (sigma_p (S n1) 
          (\lambda d:nat.divides_b d (S n1)) (\lambda d:nat.OZ)))
          [apply eq_sigma_p1;intros
            [reflexivity
            |rewrite > is_one_OZ
              [apply Ztimes_z_OZ
              |unfold Not.intro.
               apply (lt_to_not_le ? ? H1).
               rewrite > (times_n_SO x).
               rewrite > sym_times.
               rewrite < H3.
               rewrite > (div_mod ? x) in \vdash (? % ?)
                [rewrite > divides_to_mod_O
                  [rewrite < plus_n_O.
                   apply le_n
                  |apply (divides_b_true_to_lt_O ? ? ? H2).
                   apply lt_O_S
                  |apply divides_b_true_to_divides.
                   assumption
                  ]
                |apply (divides_b_true_to_lt_O ? ? ? H2).
                 apply lt_O_S
                ]
              ]
            ]
          |apply sigma_p_OZ
          ]
        ]
      |apply lt_O_S
      ]
    |apply divides_to_divides_b_true
      [apply lt_O_S
      |apply divides_n_n
      ]
    ]
  ]
qed.           

theorem commutative_dirichlet_product: \forall f,g:nat \to Z.\forall n. O < n \to 
dirichlet_product f g n = dirichlet_product g f n.
intros.
unfold dirichlet_product.
apply (trans_eq ? ?
  (sigma_p (S n) (\lambda d:nat.divides_b d n)
  (\lambda d:nat.g (n/d) * f (n/(n/d)))))
  [apply eq_sigma_p1;intros
    [reflexivity
    |rewrite > div_div
      [apply sym_Ztimes.
      |assumption
      |apply divides_b_true_to_divides.
       assumption
      ]
    ]
  |apply (eq_sigma_p_gh ? (\lambda d.(n/d)) (\lambda d.(n/d))) 
    [intros.
     apply divides_b_div_true;assumption
    |intros.
     apply div_div
      [assumption
      |apply divides_b_true_to_divides.
       assumption
      ]
    |intros.
     apply le_S_S.
     apply le_div.
     apply (divides_b_true_to_lt_O ? ? H H2)
    |intros.
     apply divides_b_div_true;assumption
    |intros.
     apply div_div
      [assumption
      |apply divides_b_true_to_divides.
       assumption
      ]
    |intros.
     apply le_S_S.
     apply le_div.
     apply (divides_b_true_to_lt_O ? ? H H2)
    ]
  ]
qed.

theorem dirichlet_product_is_one_l: 
\forall f:nat\to Z.\forall n:nat.
O < n \to dirichlet_product is_one f n = f n.
intros.
rewrite > commutative_dirichlet_product.
apply dirichlet_product_is_one_r.
assumption.
qed.

theorem dirichlet_product_one_r: 
\forall f:nat\to Z.\forall n:nat. O < n \to 
dirichlet_product f (\lambda n.Zone) n = 
sigma_p (S n) (\lambda d.divides_b d n) f.
intros.
unfold dirichlet_product.
apply eq_sigma_p;intros
  [reflexivity
  |simplify in \vdash (? ? (? ? %) ?).
   apply Ztimes_Zone_r
  ]
qed.
              
theorem dirichlet_product_one_l: 
\forall f:nat\to Z.\forall n:nat. O < n \to 
dirichlet_product (\lambda n.Zone) f n = 
sigma_p (S n) (\lambda d.divides_b d n) f. 
intros.
rewrite > commutative_dirichlet_product
  [apply dirichlet_product_one_r.
   assumption
  |assumption
  ]
qed.
