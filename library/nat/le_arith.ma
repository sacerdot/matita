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



include "nat/times.ma".
include "nat/orders.ma".

(* plus *)
theorem monotonic_le_plus_r: 
\forall n:nat.monotonic nat le (\lambda m.n + m).
simplify.intros.elim n
  [simplify.assumption.
  |simplify.apply le_S_S.assumption
  ]
qed.

theorem le_plus_r: \forall p,n,m:nat. n \le m \to p + n \le p + m
\def monotonic_le_plus_r.

theorem monotonic_le_plus_l: 
\forall m:nat.monotonic nat le (\lambda n.n + m).
simplify.intros.
rewrite < sym_plus.rewrite < (sym_plus m).
apply le_plus_r.assumption.
qed.

theorem le_plus_l: \forall p,n,m:nat. n \le m \to n + p \le m + p
\def monotonic_le_plus_l.

theorem le_plus: \forall n1,n2,m1,m2:nat. n1 \le n2  \to m1 \le m2 
\to n1 + m1 \le n2 + m2.
intros.
(**
auto.
*)
apply (transitive_le (plus n1 m1) (plus n1 m2) (plus n2 m2) ? ?);
  [apply (monotonic_le_plus_r n1 m1 m2 ?).
   apply (H1).
  |apply (monotonic_le_plus_l m2 n1 n2 ?).
   apply (H).
  ]
(* end auto($Revision$) proof: TIME=0.61 SIZE=100 DEPTH=100 *)
(*
apply (trans_le ? (n2 + m1)).
apply le_plus_l.assumption.
apply le_plus_r.assumption.
*)
qed.

theorem le_plus_n :\forall n,m:nat. m \le n + m.
intros.change with (O+m \le n+m).
apply le_plus_l.apply le_O_n.
qed.

theorem le_plus_n_r :\forall n,m:nat. m \le m + n.
intros.rewrite > sym_plus.
apply le_plus_n.
qed.

theorem eq_plus_to_le: \forall n,m,p:nat.n=m+p \to m \le n.
intros.rewrite > H.
rewrite < sym_plus.
apply le_plus_n.
qed.

theorem le_plus_to_le: 
\forall a,n,m. a + n \le a + m \to n \le m.
intro.
elim a
  [assumption
  |apply H.
   apply le_S_S_to_le.assumption
  ]
qed.

(* times *)
theorem monotonic_le_times_r: 
\forall n:nat.monotonic nat le (\lambda m. n * m).
simplify.intros.elim n.
simplify.apply le_O_n.
simplify.apply le_plus.
assumption.
assumption.
qed.

theorem le_times_r: \forall p,n,m:nat. n \le m \to p*n \le p*m
\def monotonic_le_times_r.

theorem monotonic_le_times_l: 
\forall m:nat.monotonic nat le (\lambda n.n*m).
simplify.intros.
rewrite < sym_times.rewrite < (sym_times m).
apply le_times_r.assumption.
qed.

theorem le_times_l: \forall p,n,m:nat. n \le m \to n*p \le m*p
\def monotonic_le_times_l.

theorem le_times: \forall n1,n2,m1,m2:nat. n1 \le n2  \to m1 \le m2 
\to n1*m1 \le n2*m2.
intros.
apply (trans_le ? (n2*m1)).
apply le_times_l.assumption.
apply le_times_r.assumption.
qed.

theorem le_times_n: \forall n,m:nat.(S O) \le n \to m \le n*m.
intros.elim H.simplify.
elim (plus_n_O ?).apply le_n.
simplify.rewrite < sym_plus.apply le_plus_n.
qed.

theorem le_times_to_le: 
\forall a,n,m. S O \le a \to a * n \le a * m \to n \le m.
intro.
apply nat_elim2;intros
  [apply le_O_n
  |apply False_ind.
   rewrite < times_n_O in H1.
   generalize in match H1.
   apply (lt_O_n_elim ? H).
   intros.
   simplify in H2.
   apply (le_to_not_lt ? ? H2).
   apply lt_O_S
  |apply le_S_S.
   apply H
    [assumption
    |rewrite < times_n_Sm in H2.
     rewrite < times_n_Sm in H2.
     apply (le_plus_to_le a).
     assumption
    ]
  ]
qed.

theorem le_S_times_SSO: \forall n,m.O < m \to
n \le m \to S n \le (S(S O))*m.
intros.
simplify.
rewrite > plus_n_O.
simplify.rewrite > plus_n_Sm.
apply le_plus
  [assumption
  |rewrite < plus_n_O.
   assumption
  ]
qed.
(*0 and times *)
theorem O_lt_const_to_le_times_const:  \forall a,c:nat.
O \lt c \to a \le a*c.
intros.
rewrite > (times_n_SO a) in \vdash (? % ?).
apply le_times
[ apply le_n
| assumption
]
qed.
