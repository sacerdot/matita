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

set "baseuri" "cic:/matita/library_autobatch/nat/lt_arith".

include "auto/nat/div_and_mod.ma".

(* plus *)
theorem monotonic_lt_plus_r: 
\forall n:nat.monotonic nat lt (\lambda m.n+m).
simplify.intros.
elim n;simplify
[ assumption
| autobatch. 
  (*unfold lt.
  apply le_S_S.
  assumption.*)
]
qed.

variant lt_plus_r: \forall n,p,q:nat. p < q \to n + p < n + q \def
monotonic_lt_plus_r.

theorem monotonic_lt_plus_l: 
\forall n:nat.monotonic nat lt (\lambda m.m+n).
simplify.
intros.
(*rewrite < sym_plus. 
 rewrite < (sym_plus n).*)
applyS lt_plus_r.assumption.
qed.
(* IN ALTERNATIVA: mantengo le 2 rewrite, e concludo con autobatch. *)

variant lt_plus_l: \forall n,p,q:nat. p < q \to p + n < q + n \def
monotonic_lt_plus_l.

theorem lt_plus: \forall n,m,p,q:nat. n < m \to p < q \to n + p < m + q.
intros.
autobatch.
(*apply (trans_lt ? (n + q)).
apply lt_plus_r.assumption.
apply lt_plus_l.assumption.*)
qed.

theorem lt_plus_to_lt_l :\forall n,p,q:nat. p+n < q+n \to p<q.
intro.elim n
[ rewrite > plus_n_O.
  rewrite > (plus_n_O q).
  assumption.
| apply H.
  unfold lt.
  apply le_S_S_to_le.
  rewrite > plus_n_Sm.
  rewrite > (plus_n_Sm q).
  exact H1.
]
qed.

theorem lt_plus_to_lt_r :\forall n,p,q:nat. n+p < n+q \to p<q.
intros.
apply (lt_plus_to_lt_l n). 
rewrite > sym_plus.
rewrite > (sym_plus q).
assumption.
qed.

(* times and zero *)
theorem lt_O_times_S_S: \forall n,m:nat.O < (S n)*(S m).
intros.
autobatch.
(*simplify.
unfold lt.
apply le_S_S.
apply le_O_n.*)
qed.

(* times *)
theorem monotonic_lt_times_r: 
\forall n:nat.monotonic nat lt (\lambda m.(S n)*m).
simplify.
intros.elim n
[ autobatch
  (*simplify.
  rewrite < plus_n_O.
  rewrite < plus_n_O.
  assumption.*)
| apply lt_plus;assumption (* chiudo con assumption entrambi i sottogoal attivi*)
]
qed.

theorem lt_times_r: \forall n,p,q:nat. p < q \to (S n) * p < (S n) * q
\def monotonic_lt_times_r.

theorem monotonic_lt_times_l: 
\forall m:nat.monotonic nat lt (\lambda n.n * (S m)).
simplify.
intros.
(*rewrite < sym_times.
 rewrite < (sym_times (S m)).*)
applyS lt_times_r.assumption.
qed.

(* IN ALTERNATIVA: mantengo le 2 rewrite, e concludo con autobatch. *)


variant lt_times_l: \forall n,p,q:nat. p<q \to p*(S n) < q*(S n)
\def monotonic_lt_times_l.

theorem lt_times:\forall n,m,p,q:nat. n<m \to p<q \to n*p < m*q.
intro.
elim n
[ apply (lt_O_n_elim m H).
  intro.
  cut (lt O q)
  [ apply (lt_O_n_elim q Hcut).
    intro.
    autobatch
    (*change with (O < (S m1)*(S m2)).
    apply lt_O_times_S_S.*)
  | apply (ltn_to_ltO p q H1). (*funziona anche autobatch*)
  ]
| apply (trans_lt ? ((S n1)*q))
  [ autobatch
    (*apply lt_times_r.
    assumption.*)
  | cut (lt O q)
    [ apply (lt_O_n_elim q Hcut).
      intro.
      autobatch
      (*apply lt_times_l.
      assumption.*)
    |apply (ltn_to_ltO p q H2). (*funziona anche autobatch*)
    ]
  ]
]
qed.

theorem lt_times_to_lt_l: 
\forall n,p,q:nat. p*(S n) < q*(S n) \to p < q.
intros.
cut (p < q \lor p \nlt q)
[ elim Hcut
  [ assumption
  | absurd (p * (S n) < q * (S n))
    [ assumption
    | apply le_to_not_lt.
      autobatch
      (*apply le_times_l.
      apply not_lt_to_le.
      assumption.*)
    ]
  ]
|exact (decidable_lt p q).
]
qed.

theorem lt_times_to_lt_r: 
\forall n,p,q:nat. (S n)*p < (S n)*q \to lt p q.
intros.
apply (lt_times_to_lt_l n).
rewrite < sym_times.
rewrite < (sym_times (S n)).
assumption.
qed.

theorem nat_compare_times_l : \forall n,p,q:nat. 
nat_compare p q = nat_compare ((S n) * p) ((S n) * q).
intros.
apply nat_compare_elim
[ intro.
  apply nat_compare_elim
  [ intro.
    reflexivity
  | intro.
    absurd (p=q)
    [ autobatch.
      (*apply (inj_times_r n).
      assumption*)
    | autobatch
      (*apply lt_to_not_eq. 
      assumption*)
    ]
  | intro.
    absurd (q<p)
    [ autobatch.
      (*apply (lt_times_to_lt_r n).
      assumption.*)
    | autobatch
      (*apply le_to_not_lt.
      apply lt_to_le.
      assumption*)
    ]
  ]. 
| intro.
  autobatch
  (*rewrite < H.
  rewrite > nat_compare_n_n.
  reflexivity*)
| intro.
  apply nat_compare_elim
  [ intro.
    absurd (p<q)
    [ autobatch
      (*apply (lt_times_to_lt_r n).
      assumption.*)
    | autobatch 
      (*apply le_to_not_lt.
      apply lt_to_le. 
      assumption.*)
    ]
  | intro.
    absurd (q=p)
    [ autobatch. 
      (*symmetry.
      apply (inj_times_r n).
      assumption*)
    | autobatch
      (*apply lt_to_not_eq.
      assumption*)
    ]
  | intro.
    reflexivity
  ]
].
qed.

(* div *) 

theorem eq_mod_O_to_lt_O_div: \forall n,m:nat. O < m \to O < n\to n \mod m = O \to O < n / m. 
intros 4.
apply (lt_O_n_elim m H).
intros.
apply (lt_times_to_lt_r m1).
rewrite < times_n_O.
rewrite > (plus_n_O ((S m1)*(n / (S m1)))).
rewrite < H2.
rewrite < sym_times.
rewrite < div_mod
[ rewrite > H2.
  assumption.
| autobatch
  (*unfold lt.
  apply le_S_S.
  apply le_O_n.*)
]
qed.

theorem lt_div_n_m_n: \forall n,m:nat. (S O) < m \to O < n \to n / m \lt n.
intros.
apply (nat_case1 (n / m))
[ intro.
  assumption
| intros.
  rewrite < H2.
  rewrite > (div_mod n m) in \vdash (? ? %)
  [ apply (lt_to_le_to_lt ? ((n / m)*m))
    [ apply (lt_to_le_to_lt ? ((n / m)*(S (S O))))
      [ rewrite < sym_times.
        rewrite > H2.
        simplify.
        unfold lt.
        autobatch.
        (*rewrite < plus_n_O.
        rewrite < plus_n_Sm.
        apply le_S_S.
        apply le_S_S.
        apply le_plus_n*)
      | autobatch 
        (*apply le_times_r.
        assumption*)
      ]
    | autobatch
      (*rewrite < sym_plus.
      apply le_plus_n*)
    ]
  | autobatch
    (*apply (trans_lt ? (S O)).
    unfold lt. 
    apply le_n.
    assumption*)
  ]
]
qed.

(* general properties of functions *)
theorem monotonic_to_injective: \forall f:nat\to nat.
monotonic nat lt f \to injective nat nat f.
unfold injective.intros.
apply (nat_compare_elim x y)
[ intro.
  apply False_ind.
  apply (not_le_Sn_n (f x)).
  rewrite > H1 in \vdash (? ? %).
  change with (f x < f y).
  autobatch
  (*apply H.
  apply H2*)
| intros.
  assumption
| intro.
  apply False_ind.
  apply (not_le_Sn_n (f y)).
  rewrite < H1 in \vdash (? ? %).
  change with (f y < f x).
  autobatch
  (*apply H.
  apply H2*)
]
qed.

theorem increasing_to_injective: \forall f:nat\to nat.
increasing f \to injective nat nat f.
intros.
autobatch.
(*apply monotonic_to_injective.
apply increasing_to_monotonic.
assumption.*)
qed.
