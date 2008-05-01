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

set "baseuri" "cic:/matita/library_autobatch/nat/relevant_equations".

include "auto/nat/times.ma".
include "auto/nat/minus.ma".
include "auto/nat/gcd.ma". 
(* if gcd is compiled before this, the applys will take too much *)

theorem times_plus_l: \forall n,m,p:nat. (n+m)*p = n*p + m*p.
intros.
apply (trans_eq ? ? (p*(n+m)))
[ apply sym_times
| apply (trans_eq ? ? (p*n+p*m));autobatch
  (*[ apply distr_times_plus
  | apply eq_f2;
      apply sym_times    
  ]*)
]
qed.

theorem times_minus_l: \forall n,m,p:nat. (n-m)*p = n*p - m*p.
intros.
apply (trans_eq ? ? (p*(n-m)))
[ apply sym_times
| apply (trans_eq ? ? (p*n-p*m));autobatch
  (*[ apply distr_times_minus
  | apply eq_f2;
      apply sym_times
  ]*)
]
qed.

theorem times_plus_plus: \forall n,m,p,q:nat. (n + m)*(p + q) =
n*p + n*q + m*p + m*q.
intros.
autobatch.
(*apply (trans_eq nat ? ((n*(p+q) + m*(p+q))))
[ apply times_plus_l
| rewrite > distr_times_plus.
  rewrite > distr_times_plus.
  rewrite < assoc_plus.
  reflexivity
]*)
qed.
