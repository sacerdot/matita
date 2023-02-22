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

set "baseuri" "cic:/matita/library_autobatch/nat/factorial".

include "auto/nat/le_arith.ma".

let rec fact n \def
  match n with 
  [ O \Rightarrow (S O)
  | (S m) \Rightarrow (S m)*(fact m)].

interpretation "factorial" 'fact n = (fact n).

theorem le_SO_fact : \forall n. (S O) \le n!.
intro.
elim n
[ autobatch
  (*simplify.
  apply le_n*)
| change with ((S O) \le (S n1)*n1!).
  autobatch
  (*apply (trans_le ? ((S n1)*(S O)))
  [ simplify.
    apply le_S_S.
    apply le_O_n
  | apply le_times_r.
    assumption
  ]*)
]
qed.

theorem le_SSO_fact : \forall n. (S O) < n \to (S(S O)) \le n!.
intro.
apply (nat_case n)
[ intro.
  autobatch
  (*apply False_ind.
  apply (not_le_Sn_O (S O) H).*)
| intros.
  change with ((S (S O)) \le (S m)*m!).
  apply (trans_le ? ((S(S O))*(S O)));autobatch
  (*[ apply le_n
  | apply le_times
    [ exact H
    | apply le_SO_fact
    ]
  ]*)
]
qed.

theorem le_n_fact_n: \forall n. n \le n!.
intro.
elim n
[ apply le_O_n
| change with (S n1 \le (S n1)*n1!).
  apply (trans_le ? ((S n1)*(S O)));autobatch 
  (*[ rewrite < times_n_SO.
    apply le_n
  | apply le_times.
    apply le_n.
    apply le_SO_fact
  ]*)
]
qed.

theorem lt_n_fact_n: \forall n. (S(S O)) < n \to n < n!.
intro.
apply (nat_case n)
[ intro.
  autobatch
  (*apply False_ind.
  apply (not_le_Sn_O (S(S O)) H)*)
| intros.
  change with ((S m) < (S m)*m!).
  apply (lt_to_le_to_lt ? ((S m)*(S (S O))))
  [ rewrite < sym_times.
    simplify.
    unfold lt.
    apply le_S_S.
    autobatch
    (*rewrite < plus_n_O.
    apply le_plus_n*)
  | apply le_times_r.
    autobatch
    (*apply le_SSO_fact.
    simplify.
    unfold lt.
    apply le_S_S_to_le.
    exact H*)
  ]
]
qed.

