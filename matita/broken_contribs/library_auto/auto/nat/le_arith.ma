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

set "baseuri" "cic:/matita/library_autobatch/nat/le_arith".

include "auto/nat/times.ma".
include "auto/nat/orders.ma".

(* plus *)
theorem monotonic_le_plus_r: 
\forall n:nat.monotonic nat le (\lambda m.n + m).
simplify.intros.
elim n;simplify
[ assumption
| autobatch
  (*apply le_S_S.assumption*)
]
qed.

theorem le_plus_r: \forall p,n,m:nat. n \le m \to p + n \le p + m
\def monotonic_le_plus_r.

theorem monotonic_le_plus_l: 
\forall m:nat.monotonic nat le (\lambda n.n + m).
simplify.intros.
 (*rewrite < sym_plus.
 rewrite < (sym_plus m).*)
 applyS le_plus_r.
 assumption.
qed.

(* IN ALTERNATIVA:

theorem monotonic_le_plus_l: 
\forall m:nat.monotonic nat le (\lambda n.n + m).
simplify.intros.
 rewrite < sym_plus.
 rewrite < (sym_plus m).
 autobatch.
qed.
*)
theorem le_plus_l: \forall p,n,m:nat. n \le m \to n + p \le m + p
\def monotonic_le_plus_l.

theorem le_plus: \forall n1,n2,m1,m2:nat. n1 \le n2  \to m1 \le m2 
\to n1 + m1 \le n2 + m2.
intros.
autobatch.
(*apply (trans_le ? (n2 + m1)).
apply le_plus_l.assumption.
apply le_plus_r.assumption.*)
qed.

theorem le_plus_n :\forall n,m:nat. m \le n + m.
intros.
change with (O+m \le n+m).
autobatch.
(*apply le_plus_l.
  apply le_O_n.*)
qed.

theorem eq_plus_to_le: \forall n,m,p:nat.n=m+p \to m \le n.
intros.
rewrite > H.
rewrite < sym_plus.
apply le_plus_n. (* a questo punto funziona anche: autobatch.*)
qed.

(* times *)
theorem monotonic_le_times_r: 
\forall n:nat.monotonic nat le (\lambda m. n * m).
simplify.intros.elim n;simplify
[ apply le_O_n.
| autobatch.
(*apply le_plus;
  assumption. *) (* chiudo entrambi i goal attivi in questo modo*)
]
qed.

theorem le_times_r: \forall p,n,m:nat. n \le m \to p*n \le p*m
\def monotonic_le_times_r.

theorem monotonic_le_times_l: 
\forall m:nat.monotonic nat le (\lambda n.n*m).
simplify.intros.
(*rewrite < sym_times.
  rewrite < (sym_times m).
*)
applyS le_times_r.
assumption.
qed.

(* IN ALTERNATIVA:
theorem monotonic_le_times_l: 
\forall m:nat.monotonic nat le (\lambda n.n*m).
simplify.intros.
rewrite < sym_times.
rewrite < (sym_times m).
autobatch.
qed.
*)

theorem le_times_l: \forall p,n,m:nat. n \le m \to n*p \le m*p
\def monotonic_le_times_l.

theorem le_times: \forall n1,n2,m1,m2:nat. n1 \le n2  \to m1 \le m2 
\to n1*m1 \le n2*m2.
intros.
autobatch.
(*apply (trans_le ? (n2*m1)).
apply le_times_l.assumption.
apply le_times_r.assumption.*)
qed.

theorem le_times_n: \forall n,m:nat.(S O) \le n \to m \le n*m.
intros.elim H;simplify
[ autobatch
  (*elim (plus_n_O ?).
  apply le_n....*)
| autobatch
  (*rewrite < sym_plus.
  apply le_plus_n.*)
]
qed.
