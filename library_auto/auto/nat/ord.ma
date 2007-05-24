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

set "baseuri" "cic:/matita/library_autobatch/nat/ord".

include "datatypes/constructors.ma".
include "auto/nat/exp.ma".
include "auto/nat/gcd.ma".
include "auto/nat/relevant_equations.ma". (* required by autobatch paramod *)

(* this definition of log is based on pairs, with a remainder *)

let rec p_ord_aux p n m \def
  match n \mod m with
  [ O \Rightarrow 
    match p with
      [ O \Rightarrow pair nat nat O n
      | (S p) \Rightarrow 
       match (p_ord_aux p (n / m) m) with
       [ (pair q r) \Rightarrow pair nat nat (S q) r] ]
  | (S a) \Rightarrow pair nat nat O n].
  
(* p_ord n m = <q,r> if m divides n q times, with remainder r *)
definition p_ord \def \lambda n,m:nat.p_ord_aux n n m.

theorem p_ord_aux_to_Prop: \forall p,n,m. O < m \to
  match p_ord_aux p n m with
  [ (pair q r) \Rightarrow n = m \sup q *r ].
intro.
elim p
[ simplify.
  apply (nat_case (n \mod m))
  [ simplify.
    apply plus_n_O
  | intros.
    simplify.
    apply plus_n_O
  ]
| simplify. 
  apply (nat_case1 (n1 \mod m))
  [ intro.
    simplify.
    generalize in match (H (n1 / m) m).
    elim (p_ord_aux n (n1 / m) m).
    simplify.
    rewrite > assoc_times.
    rewrite < H3
    [ rewrite > (plus_n_O (m*(n1 / m))).
      rewrite < H2.
      rewrite > sym_times.
      autobatch
      (*rewrite < div_mod
      [ reflexivity
      | assumption
      ]*)
    | assumption
    ]
  | intros.
    simplify.
    apply plus_n_O
  ]
]
qed.

theorem p_ord_aux_to_exp: \forall p,n,m,q,r. O < m \to
  (pair nat nat q r) = p_ord_aux p n m \to n = m \sup q * r.
intros.
change with 
match (pair nat nat q r) with
  [ (pair q r) \Rightarrow n = m \sup q * r ].
rewrite > H1.
apply p_ord_aux_to_Prop.
assumption.
qed.

(* questo va spostato in primes1.ma *)
theorem p_ord_exp: \forall n,m,i. O < m \to n \mod m \neq O \to
\forall p. i \le p \to p_ord_aux p (m \sup i * n) m = pair nat nat i n.
intros 5.
elim i
[ simplify.
  rewrite < plus_n_O.
  apply (nat_case p)
  [ simplify.
    elim (n \mod m);autobatch
    (*[ simplify.
      reflexivity
    | simplify.
      reflexivity
    ]*)
  | intro.
    simplify.
    cut (O < n \mod m \lor O = n \mod m)
    [ elim Hcut
      [ apply (lt_O_n_elim (n \mod m) H3).
        intros.autobatch
        (*simplify.
        reflexivity*)
      | apply False_ind.autobatch
        (*apply H1.
        apply sym_eq.
        assumption*)
      ]
    | autobatch
      (*apply le_to_or_lt_eq.
      apply le_O_n*)
    ]  
  ]
| generalize in match H3.
  apply (nat_case p)
  [ intro.
    apply False_ind.
    apply (not_le_Sn_O n1 H4)
  | intros.
    simplify.
    fold simplify (m \sup (S n1)).
    cut (((m \sup (S n1)*n) \mod m) = O)
    [ rewrite > Hcut.
      simplify.
      fold simplify (m \sup (S n1)). 
      cut ((m \sup (S n1) *n) / m = m \sup n1 *n)
      [ rewrite > Hcut1.
        rewrite > (H2 m1);autobatch
        (*[ simplify.
          reflexivity
        | apply le_S_S_to_le.
          assumption
        ]*)
      | (* div_exp *)
        simplify.
        rewrite > assoc_times.
        apply (lt_O_n_elim m H).
        intro.
        apply div_times
      ]
    | (* mod_exp = O *)
      apply divides_to_mod_O
      [ assumption
      | simplify.autobatch
        (*rewrite > assoc_times.
        apply (witness ? ? (m \sup n1 *n)).
        reflexivity*)
      ]
    ]
  ]
]
qed.

theorem p_ord_aux_to_Prop1: \forall p,n,m. (S O) < m \to O < n \to n \le p \to
  match p_ord_aux p n m with
  [ (pair q r) \Rightarrow r \mod m \neq O].
intro.
elim p
[ absurd (O < n);autobatch
  (*[ assumption
  | apply le_to_not_lt.
    assumption
  ]*)
| simplify.
  apply (nat_case1 (n1 \mod m))
  [ intro.
    generalize in match (H (n1 / m) m).
    elim (p_ord_aux n (n1 / m) m).
    apply H5
    [ assumption
    | autobatch
      (*apply eq_mod_O_to_lt_O_div
      [ apply (trans_lt ? (S O))
        [ unfold lt.
          apply le_n
        | assumption
        ]
      | assumption
      | assumption
      ]*)
    | apply le_S_S_to_le.autobatch
      (*apply (trans_le ? n1)
      [ change with (n1 / m < n1).
        apply lt_div_n_m_n;assumption        
      | assumption
      ]*)
    ]
  | intros.
    simplify.autobatch
    (*rewrite > H4.    
    unfold Not.
    intro.
    apply (not_eq_O_S m1).
    rewrite > H5.
    reflexivity.*)
  ]
]
qed.

theorem p_ord_aux_to_not_mod_O: \forall p,n,m,q,r. (S O) < m \to O < n \to n \le p \to
 pair nat nat q r = p_ord_aux p n m \to r \mod m \neq O.
intros.
change with 
  match (pair nat nat q r) with
  [ (pair q r) \Rightarrow r \mod m \neq O].
rewrite > H3. 
apply p_ord_aux_to_Prop1;
  assumption.
qed.

axiom not_eq_to_le_to_lt: ∀n,m. n≠m → n≤m → n<m.

theorem p_ord_exp1: \forall p,n,q,r. O < p \to \lnot p \divides r \to
n = p \sup q * r \to p_ord n p = pair nat nat q r.
intros.
unfold p_ord.
rewrite > H2.
apply p_ord_exp
[ assumption
| unfold.
  intro.
  autobatch
  (*apply H1.
  apply mod_O_to_divides
  [ assumption
  | assumption
  ]*)
| apply (trans_le ? (p \sup q))
  [ cut ((S O) \lt p)
    [ autobatch
      (*elim q
      [ simplify.
        apply le_n_Sn
      | simplify.
        generalize in match H3.
        apply (nat_case n1)
        [ simplify.
          rewrite < times_n_SO.
          intro.
          assumption
        | intros.
          apply (trans_le ? (p*(S m)))
          [ apply (trans_le ? ((S (S O))*(S m)))
            [ simplify.
              rewrite > plus_n_Sm.
              rewrite < plus_n_O.
              apply le_plus_n
            | apply le_times_l.
              assumption
            ]
          | apply le_times_r.
            assumption
          ]
        ]
      ]*)
    | apply not_eq_to_le_to_lt
      [ unfold.
        intro.
        autobatch
        (*apply H1.
        rewrite < H3.
        apply (witness ? r r ?).
        simplify.
        apply plus_n_O*)
      | assumption
      ]
    ]
  | rewrite > times_n_SO in \vdash (? % ?).
    apply le_times_r.
    change with (O \lt r).
    apply not_eq_to_le_to_lt
    [ unfold.
      intro.autobatch
      (*apply H1.rewrite < H3.
      apply (witness ? ? O ?).rewrite < times_n_O.
      reflexivity*)
    | apply le_O_n
    ]
  ]
]
qed.

theorem p_ord_to_exp1: \forall p,n,q,r. (S O) \lt p \to O \lt n \to p_ord n p = pair nat nat q r\to 
\lnot p \divides r \land n = p \sup q * r.
intros.
unfold p_ord in H2.
split
[ unfold.intro.
  apply (p_ord_aux_to_not_mod_O n n p q r);autobatch
  (*[ assumption
  | assumption
  | apply le_n
  | symmetry.
    assumption
  | apply divides_to_mod_O
    [ apply (trans_lt ? (S O))
      [ unfold.
        apply le_n
      | assumption         
      ]
    | assumption
    ]
  ]*)
| apply (p_ord_aux_to_exp n);autobatch
  (*[ apply (trans_lt ? (S O))
    [ unfold.
      apply le_n
    | assumption
    ]
  | symmetry.
    assumption
  ]*)
]
qed.

theorem p_ord_times: \forall p,a,b,qa,ra,qb,rb. prime p 
\to O \lt a \to O \lt b 
\to p_ord a p = pair nat nat qa ra  
\to p_ord b p = pair nat nat qb rb
\to p_ord (a*b) p = pair nat nat (qa + qb) (ra*rb).
intros.
cut ((S O) \lt p)
[ elim (p_ord_to_exp1 ? ? ? ? Hcut H1 H3).
  elim (p_ord_to_exp1 ? ? ? ? Hcut H2 H4).
  apply p_ord_exp1
  [ autobatch
    (*apply (trans_lt ? (S O))
    [ unfold.
      apply le_n
    | assumption
    ]*)
  | unfold.
    intro.
    elim (divides_times_to_divides ? ? ? H H9);autobatch
    (*[ apply (absurd ? ? H10 H5)
    | apply (absurd ? ? H10 H7)
    ]*)
  | (* rewrite > H6.
    rewrite > H8. *)
    autobatch paramodulation
  ]
| unfold prime in H. 
  elim H. 
  assumption
]
qed.

theorem fst_p_ord_times: \forall p,a,b. prime p 
\to O \lt a \to O \lt b 
\to fst ? ? (p_ord (a*b) p) = (fst ? ? (p_ord a p)) + (fst ? ? (p_ord b p)).
intros.
rewrite > (p_ord_times p a b (fst ? ? (p_ord a p)) (snd ? ? (p_ord a p))
(fst ? ? (p_ord b p)) (snd ? ? (p_ord b p)) H H1 H2);autobatch.
(*[ simplify.
  reflexivity
| apply eq_pair_fst_snd
| apply eq_pair_fst_snd
]*)
qed.

theorem p_ord_p : \forall p:nat. (S O) \lt p \to p_ord p p = pair ? ? (S O) (S O).
intros.
apply p_ord_exp1
[ autobatch
  (*apply (trans_lt ? (S O))
  [ unfold.
    apply le_n
  | assumption
  ]*)
| unfold.
  intro.
  apply (absurd ? ? H).autobatch
  (*apply le_to_not_lt.
  apply divides_to_le
  [ unfold.
    apply le_n
  | assumption
  ]*)
| autobatch
  (*rewrite < times_n_SO.
  apply exp_n_SO*)
]
qed.
