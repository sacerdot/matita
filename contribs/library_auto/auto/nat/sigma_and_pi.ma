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

set "baseuri" "cic:/matita/library_autobatch/nat/sigma_and_pi".

include "auto/nat/factorial.ma".
include "auto/nat/exp.ma".
include "auto/nat/lt_arith.ma".

let rec sigma n f m \def
  match n with 
  [ O \Rightarrow (f m)
  | (S p) \Rightarrow (f (S p+m))+(sigma p f m)].

let rec pi n f m \def
  match n with 
  [ O \Rightarrow f m
  | (S p) \Rightarrow (f (S p+m))*(pi p f m)].
  
theorem eq_sigma: \forall f,g:nat \to nat.
\forall n,m:nat.
(\forall i:nat. m \le i \to i \le m+n \to f i = g i) \to
(sigma n f m) = (sigma n g m).
intros 3.
elim n
[ simplify.
  autobatch
  (*apply H
  [ apply le_n
  | rewrite < plus_n_O.
    apply le_n
  ]*)
| simplify.
  apply eq_f2
  [ apply H1
    [ autobatch
      (*change with (m \le (S n1)+m).
      apply le_plus_n*)
    | autobatch
      (*rewrite > (sym_plus m).
      apply le_n*)
    ]
  | apply H.
    intros.
    apply H1
    [ assumption
    | autobatch
      (*rewrite < plus_n_Sm.
      apply le_S.
      assumption*)
    ]
  ]
]
qed.

theorem eq_pi: \forall f,g:nat \to nat.
\forall n,m:nat.
(\forall i:nat. m \le i \to i \le m+n \to f i = g i) \to
(pi n f m) = (pi n g m).
intros 3.
elim n
[ simplify.
  autobatch
  (*apply H
  [ apply le_n
  | rewrite < plus_n_O.
    apply le_n
  ] *) 
| simplify.
  apply eq_f2
  [ apply H1
    [ autobatch
      (*change with (m \le (S n1)+m).
      apply le_plus_n*)
    | autobatch
      (*rewrite > (sym_plus m).
      apply le_n*)
    ]
  | apply H.
    intros.
    apply H1
    [ assumption
    | autobatch
      (*rewrite < plus_n_Sm.
      apply le_S.
      assumption*)
    ]
  ]
]
qed.

theorem eq_fact_pi: \forall n. (S n)! = pi n (\lambda m.m) (S O).
intro.
elim n
[ autobatch
  (*simplify.
  reflexivity*)
| change with ((S(S n1))*(S n1)! = ((S n1)+(S O))*(pi n1 (\lambda m.m) (S O))).
  rewrite < plus_n_Sm.
  rewrite < plus_n_O.
  autobatch
  (*apply eq_f.
  assumption*)
]
qed.

theorem exp_pi_l: \forall f:nat\to nat.\forall n,m,a:nat.
(exp a (S n))*pi n f m= pi n (\lambda p.a*(f p)) m.
intros.
elim n
[ autobatch
  (*simplify.
  rewrite < times_n_SO.
  reflexivity*)
| simplify.
  rewrite < H.
  rewrite > assoc_times. 
  rewrite > assoc_times in\vdash (? ?  ? %).
  apply eq_f.
  rewrite < assoc_times. 
  rewrite < assoc_times.
  autobatch 
  (*apply eq_f2
  [ apply sym_times
  | reflexivity
  ]*)
]
qed.
