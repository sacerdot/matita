(**************************************************************************)
(*       __                                                               *)
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
include "nat/minus.ma".
include "nat/gcd.ma". 
(* if gcd is compiled before this, the applys will take too much *)

theorem times_plus_l: \forall n,m,p:nat. (n+m)*p = n*p + m*p.
intros.
apply (trans_eq ? ? (p*(n+m))).
apply sym_times.
apply (trans_eq ? ? (p*n+p*m)).
apply distr_times_plus.
apply eq_f2.
apply sym_times.
apply sym_times.
qed.

theorem times_minus_l: \forall n,m,p:nat. (n-m)*p = n*p - m*p.
intros.
apply (trans_eq ? ? (p*(n-m))).
apply sym_times.
apply (trans_eq ? ? (p*n-p*m)).
apply distr_times_minus.
apply eq_f2.
apply sym_times.
apply sym_times.
qed.

theorem times_plus_plus: \forall n,m,p,q:nat. (n + m)*(p + q) =
n*p + n*q + m*p + m*q.
intros.
apply (trans_eq nat ? ((n*(p+q) + m*(p+q)))).
apply times_plus_l.
rewrite > distr_times_plus.
rewrite > distr_times_plus.
rewrite < assoc_plus.reflexivity.
qed.

theorem eq_pred_to_eq:
 ∀n,m. O < n → O < m → pred n = pred m → n = m.
intros;
generalize in match (eq_f ? ? S ? ? H2);
intro;
rewrite < S_pred in H3;
rewrite < S_pred in H3;
assumption.
qed.
