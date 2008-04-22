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

include "nat/binomial.ma".
include "nat/sqrt.ma".

theorem le_times_SSO_n_exp_SSO_n: \forall n. 
2*n \le exp 2 n.
intro.cases n
  [apply le_O_n
  |elim n1
    [apply le_n
    |rewrite > times_SSO.
     change in ⊢ (? % ?) with (2 + (2*(S n2))).
     change in ⊢ (? ? %) with (exp 2 (S n2)+(exp 2 (S n2) + O)).
     rewrite < plus_n_O.
     apply le_plus
      [rewrite > exp_n_SO in ⊢ (? % ?).
       apply le_exp
        [apply lt_O_S
        |apply le_S_S.apply le_O_n
        ]
      |assumption
      ]
    ]
  ]
qed.

theorem le_times_n_exp: \forall a,n. exp 2 a \le n \to 
exp 2 a*n \le exp 2 n.
intros.elim H
  [rewrite < exp_plus_times.
   apply le_exp
    [apply lt_O_S
    |rewrite > plus_n_O in ⊢ (? (? ? %) ?).
     change in ⊢ (? % ?) with (2*a).
     apply le_times_SSO_n_exp_SSO_n
    ]
  |rewrite > sym_times.simplify.
   rewrite < plus_n_O.
   apply le_plus
    [apply (trans_le ? n1)
      [assumption
      |apply (trans_le ? (2*n1))
        [apply le_times_n.
         apply le_n_Sn
        |apply le_times_SSO_n_exp_SSO_n
        ]
      ]
    |rewrite > sym_times.
     assumption
    ]
  ]
qed.     

theorem lt_times_SSO_n_exp_SSO_n: \forall n. 2 < n \to
2*n < exp 2 n.
intros.elim H
  [apply leb_true_to_le.reflexivity.
  |rewrite > times_SSO.
   change in ⊢ (? % ?) with (2 + (2*n1)).
   simplify in ⊢ (? ? %).
   rewrite < plus_n_O.
   apply (lt_to_le_to_lt ? (2+(exp 2 n1)))
    [apply lt_plus_r.assumption
    |apply le_plus_l.
     rewrite > exp_n_SO in ⊢ (? % ?).
     apply le_exp
      [apply lt_O_S
      |apply (trans_le ? 3)
        [apply le_S_S.apply le_O_n
        |assumption
        ]
      ]
    ]
  ]
qed.

theorem le_exp_n_SSO_exp_SSO_n:\forall n. 3 < n \to 
exp n 2 \le exp 2 n.
intros.elim H
  [simplify.apply le_n
  |simplify.
   rewrite < plus_n_O.
   rewrite < times_n_SO.
   rewrite < times_n_Sm.
   rewrite < assoc_plus.
   rewrite < sym_plus.
   rewrite > plus_n_Sm.
   apply le_plus
    [rewrite < exp_SSO.
     assumption
    |rewrite > plus_n_O in ⊢ (? (? (? ? %)) ?).
     change in ⊢ (? (? %) ?) with (2*n1).
     apply lt_times_SSO_n_exp_SSO_n.
     apply lt_to_le.
     assumption
    ]
  ]
qed.

(* a variant *)
theorem le_exp_n_SSO_exp_SSO_n1:\forall n. S O < n \to
exp (4*n) 2 \le exp 2 (3*n).
intros.elim H
  [apply leb_true_to_le.reflexivity
  |cut (exp (S n1) 2 \le 3*(exp n1 2))
    [apply (trans_le ? (3*exp (4*n1) 2))
      [rewrite < times_exp.
       rewrite < times_exp.
       rewrite < assoc_times.
       rewrite > sym_times in ⊢ (? ? (? % ?)).
       rewrite > assoc_times.
       apply le_times_r.
       assumption
      |apply (trans_le ? (8*exp 2 (3*n1)))
        [apply le_times
          [apply leb_true_to_le.reflexivity
          |assumption
          ]
        |change in ⊢ (? (? % ?) ?) with (exp 2 3).
         rewrite < exp_plus_times.
         apply le_exp
          [apply lt_O_S
          |simplify.rewrite < plus_n_Sm.
           rewrite < plus_n_Sm.rewrite < plus_n_Sm.
           apply le_n
          ]
        ]
      ]
    |rewrite > exp_Sn_SSO.
     change in ⊢ (? ? %) with ((exp n1 2) + ((exp n1 2) + ((exp n1 2) + O))).
     rewrite < plus_n_O.
     rewrite > plus_n_SO.
     rewrite > assoc_plus.
     apply le_plus_r.
     apply le_plus
      [rewrite > exp_SSO.
       apply le_times_l.
       assumption
      |apply lt_O_exp.
       apply lt_to_le.assumption
      ]
    ]
  ]
qed.

(* a strict version *)
theorem lt_exp_n_SSO_exp_SSO_n:\forall n. 4 < n \to 
exp n 2 < exp 2 n.
intros.elim H
  [apply leb_true_to_le.reflexivity.
  |simplify.
   rewrite < plus_n_O.
   rewrite < times_n_SO.
   rewrite < times_n_Sm.
   rewrite < assoc_plus.
   rewrite < sym_plus.
   rewrite > plus_n_Sm.
   apply (lt_to_le_to_lt ? ((exp 2 n1)+S (n1+n1)))
    [apply lt_plus_l.
     rewrite < exp_SSO.
     assumption
    |apply le_plus_r.
     rewrite > plus_n_O in ⊢ (? (? (? ? %)) ?).
     change in ⊢ (? (? %) ?) with (2*n1).
     apply lt_times_SSO_n_exp_SSO_n.
     apply lt_to_le.apply lt_to_le.
     assumption
    ]
  ]
qed.

theorem le_times_exp_n_SSO_exp_SSO_n:\forall a,n. 1 < a \to 4*a \le n \to 
exp 2 a*exp n 2 \le exp 2 n.
intros.elim H1
  [apply (trans_le ? ((exp 2 a)*(exp 2 (3*a))))
    [apply le_times_r.
     apply le_exp_n_SSO_exp_SSO_n1.
     assumption
    |rewrite < exp_plus_times.
     apply le_exp
      [apply lt_O_S
      |apply le_n
      ]
    ]
  |apply (trans_le ? ((exp 2 a)*(2*(exp n1 2))))
    [apply le_times_r.
     simplify.
     rewrite < times_n_SO.
     rewrite < sym_times.simplify.
     rewrite < plus_n_O.
     rewrite < assoc_plus.
     rewrite < sym_plus.
     rewrite > plus_n_Sm.
     apply le_plus_r.
     apply (trans_le ? (3*n1))
      [simplify.rewrite > plus_n_SO.
       rewrite > assoc_plus.
       apply le_plus_r.
       apply le_plus_r.
       rewrite < plus_n_O.
       apply (trans_le ? (4*2))
        [apply leb_true_to_le.reflexivity
        |apply (trans_le ? (4*a))
          [apply le_times_r.assumption
          |assumption
          ]
        ]
      |apply le_times_l.
       apply (trans_le ? (4*2))
        [apply leb_true_to_le.reflexivity
        |apply (trans_le ? (4*a))
          [apply le_times_r.assumption
          |assumption
          ]
        ]
      ]
    |rewrite < assoc_times.
     rewrite < sym_times in ⊢ (? (? % ?) ?).
     rewrite > assoc_times.
     change in ⊢ (? ? %) with (2*exp 2 n1).
     apply le_times_r.
     assumption
    ]
  ]
qed.

(* the same for log and sqrt 
theorem le_times_log_sqrt:\forall a,n. 1 < a \to exp 2 (8*a) \le n \to 
exp 2 a*log 2 n \le sqrt n.
intros.unfold sqrt.
apply f_m_to_le_max
  [
  |apply le_to_leb_true.
   rewrite < exp_SSO.
   rewrite < times_exp.
   rewrite > exp_exp_times.
   apply (trans_le ? (exp 2 (log 2 n)))
    [apply le_times_exp_n_SSO_exp_SSO_n.
*)

         

