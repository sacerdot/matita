(**************************************************************************)
(*       ___	                                                            *)
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

include "nat/div_and_mod.ma".
include "nat/lt_arith.ma".

let rec exp n m on m\def 
 match m with 
 [ O \Rightarrow (S O)
 | (S p) \Rightarrow (times n (exp n p)) ].

interpretation "natural exponent" 'exp a b = (exp a b).

theorem exp_plus_times : \forall n,p,q:nat. 
n \sup (p + q) = (n \sup p) * (n \sup q).
intros.elim p.
simplify.rewrite < plus_n_O.reflexivity.
simplify.rewrite > H.symmetry.
apply assoc_times.
qed.

theorem exp_n_O : \forall n:nat. S O = n \sup O.
intro.simplify.reflexivity.
qed.

theorem exp_n_SO : \forall n:nat. n = n \sup (S O).
intro.simplify.rewrite < times_n_SO.reflexivity.
qed.

theorem exp_SO_n : \forall n:nat. S O = (S O) \sup n.
intro.elim n
  [reflexivity
  |simplify.rewrite < plus_n_O.assumption
  ]
qed.

theorem exp_SSO: \forall n. exp n (S(S O)) = n*n.
intro.simplify.
rewrite < times_n_SO.
reflexivity.
qed.

theorem exp_exp_times : \forall n,p,q:nat. 
(n \sup p) \sup q = n \sup (p * q).
intros.
elim q.simplify.rewrite < times_n_O.simplify.reflexivity.
simplify.rewrite > H.rewrite < exp_plus_times.
rewrite < times_n_Sm.reflexivity.
qed.

theorem lt_O_exp: \forall n,m:nat. O < n \to O < n \sup m. 
intros.elim m.simplify.unfold lt.apply le_n.
simplify.unfold lt.rewrite > times_n_SO.
apply le_times.assumption.assumption.
qed.

theorem lt_m_exp_nm: \forall n,m:nat. (S O) < n \to m < n \sup m.
intros.elim m.simplify.unfold lt.apply le_n.
simplify.unfold lt.
apply (trans_le ? ((S(S O))*(S n1))).
simplify.
rewrite < plus_n_Sm.apply le_S_S.apply le_S_S.
rewrite < sym_plus.
apply le_plus_n.
apply le_times.assumption.assumption.
qed.

theorem exp_to_eq_O: \forall n,m:nat. (S O) < n 
\to n \sup m = (S O) \to m = O.
intros.apply antisym_le.apply le_S_S_to_le.
rewrite < H1.change with (m < n \sup m).
apply lt_m_exp_nm.assumption.
apply le_O_n.
qed.

theorem injective_exp_r: \forall n:nat. (S O) < n \to 
injective nat nat (\lambda m:nat. n \sup m).
simplify.intros 4.
apply (nat_elim2 (\lambda x,y.n \sup x = n \sup y \to x = y)).
intros.apply sym_eq.apply (exp_to_eq_O n).assumption.
rewrite < H1.reflexivity.
intros.apply (exp_to_eq_O n).assumption.assumption.
intros.apply eq_f.
apply H1.
(* esprimere inj_times senza S *)
cut (\forall a,b:nat.O < n \to n*a=n*b \to a=b).
apply Hcut.simplify.unfold lt.apply le_S_S_to_le. apply le_S. assumption.
assumption.
intros 2.
apply (nat_case n).
intros.apply False_ind.apply (not_le_Sn_O O H3).
intros.
apply (inj_times_r m1).assumption.
qed.

variant inj_exp_r: \forall p:nat. (S O) < p \to \forall n,m:nat.
p \sup n = p \sup m \to n = m \def
injective_exp_r.

theorem le_exp: \forall n,m,p:nat. O < p \to n \le m \to exp p n \le exp p m.
apply nat_elim2
  [intros.
   apply lt_O_exp.assumption
  |intros.
   apply False_ind.
   apply (le_to_not_lt ? ? ? H1).
   apply le_O_n
  |intros.
   simplify.
   apply le_times
    [apply le_n
    |apply H[assumption|apply le_S_S_to_le.assumption]
    ]
  ]
qed.

theorem lt_exp: \forall n,m,p:nat. S O < p \to n < m \to exp p n < exp p m.
apply nat_elim2
  [intros.
   apply (lt_O_n_elim ? H1).intro.
   simplify.unfold lt.
   rewrite > times_n_SO.
   apply le_times
    [assumption
    |apply lt_O_exp.
     apply (trans_lt ? (S O))[apply le_n|assumption]
    ]
  |intros.
   apply False_ind.
   apply (le_to_not_lt ? ? ? H1).
   apply le_O_n
  |intros.simplify.
   apply lt_times_r1
    [apply (trans_lt ? (S O))[apply le_n|assumption]
    |apply H
      [apply H1
      |apply le_S_S_to_le.assumption
      ]
    ]
  ]
qed.

theorem lt_exp1: \forall n,m,p:nat. O < p \to n < m \to exp n p < exp m p.
intros.
elim H
  [rewrite < exp_n_SO.rewrite < exp_n_SO.assumption
  |simplify.
   apply lt_times;assumption
  ]
qed.

theorem le_exp_to_le: 
\forall a,n,m. S O < a \to exp a n \le exp a m \to n \le m.
intro.
apply nat_elim2;intros
  [apply le_O_n
  |apply False_ind.
   apply (le_to_not_lt ? ? H1).
   simplify.
   rewrite > times_n_SO.
   apply lt_to_le_to_lt_times
    [assumption
    |apply lt_O_exp.apply lt_to_le.assumption
    |apply lt_O_exp.apply lt_to_le.assumption
    ]
  |simplify in H2.
   apply le_S_S.
   apply H
    [assumption
    |apply (le_times_to_le a)
      [apply lt_to_le.assumption|assumption]
    ]
  ]
qed.

theorem le_exp_to_le1 : \forall n,m,p.O < p \to exp n p \leq exp m p \to n \leq m.
intros;apply not_lt_to_le;intro;apply (lt_to_not_le ? ? ? H1);
apply lt_exp1;assumption.
qed.
     
theorem lt_exp_to_lt: 
\forall a,n,m. S O < a \to exp a n < exp a m \to n < m.
intros.
elim (le_to_or_lt_eq n m)
  [assumption
  |apply False_ind.
   apply (lt_to_not_eq ? ? H1).
   rewrite < H2.
   reflexivity
  |apply (le_exp_to_le a)
    [assumption
    |apply lt_to_le.
     assumption
    ]
  ]
qed.

theorem lt_exp_to_lt1: 
\forall a,n,m. O < a \to exp n a < exp m a \to n < m.
intros.
elim (le_to_or_lt_eq n m)
  [assumption
  |apply False_ind.
   apply (lt_to_not_eq ? ? H1).
   rewrite < H2.
   reflexivity
  |apply (le_exp_to_le1 ? ? a)
    [assumption
    |apply lt_to_le.
     assumption
    ]
  ]
qed.
     
theorem times_exp: 
\forall n,m,p. exp n p * exp m p = exp (n*m) p.
intros.elim p
  [simplify.reflexivity
  |simplify.
   rewrite > assoc_times.
   rewrite < assoc_times in ⊢ (? ? (? ? %) ?).
   rewrite < sym_times in ⊢ (? ? (? ? (? % ?)) ?).
   rewrite > assoc_times in ⊢ (? ? (? ? %) ?).
   rewrite < assoc_times.
   rewrite < H.
   reflexivity
  ]
qed.

theorem monotonic_exp1: \forall n.
monotonic nat le (\lambda x.(exp x n)).
unfold monotonic. intros.
simplify.elim n
  [apply le_n
  |simplify.
   apply le_times;assumption
  ]
qed.
  
   
   