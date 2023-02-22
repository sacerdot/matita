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

include "Z/dirichlet_product.ma".
include "Z/moebius.ma".

definition sigma_div: (nat \to Z) \to nat \to Z \def
\lambda f.\lambda n. sigma_p (S n) (\lambda d.divides_b d n) f.

theorem sigma_div_moebius:
\forall n:nat. O < n \to sigma_div moebius n = is_one n.
intros.elim H
  [reflexivity
  |rewrite > is_one_OZ  
    [unfold sigma_div.
     apply sigma_p_moebius.
     apply le_S_S.
     assumption
    |unfold Not.intro.
     apply (lt_to_not_eq ? ? H1).
     apply injective_S.
     apply sym_eq.
     assumption
    ]
  ]
qed.
  
(* moebius inversion theorem *)
theorem inversion: \forall f:nat \to Z.\forall n:nat.O < n \to
dirichlet_product moebius (sigma_div f) n = f n.
intros.
rewrite > commutative_dirichlet_product
  [apply (trans_eq ? ? (dirichlet_product (dirichlet_product f (\lambda n.Zone)) moebius n))
    [unfold dirichlet_product.
     apply eq_sigma_p1;intros
      [reflexivity
      |apply eq_f2
        [apply sym_eq.
         unfold sigma_div.
         apply dirichlet_product_one_r.
         apply (divides_b_true_to_lt_O ? ? H H2)
        |reflexivity
        ]
      ]
    |rewrite > associative_dirichlet_product
      [apply (trans_eq ? ? (dirichlet_product f (sigma_div moebius) n))
        [unfold dirichlet_product.
         apply eq_sigma_p1;intros
          [reflexivity
          |apply eq_f2
            [reflexivity
            |unfold sigma_div.
             apply dirichlet_product_one_l.
             apply (lt_times_n_to_lt x)
              [apply (divides_b_true_to_lt_O ? ? H H2)
              |rewrite > divides_to_div
                [assumption
                |apply (divides_b_true_to_divides ? ? H2)
                ]
              ]
            ]
          ]
        |apply (trans_eq ? ? (dirichlet_product f is_one n))
          [unfold dirichlet_product.
           apply eq_sigma_p1;intros
            [reflexivity
            |apply eq_f2
              [reflexivity
              |apply sigma_div_moebius.
               apply (lt_times_n_to_lt x)
                [apply (divides_b_true_to_lt_O ? ? H H2)
                |rewrite > divides_to_div
                  [assumption
                  |apply (divides_b_true_to_divides ? ? H2)
                  ]
                ]
              ]
            ]
          |apply dirichlet_product_is_one_r
          ]
        ]
      |assumption
      ]
    ]
  |assumption
  ]
qed.
        
