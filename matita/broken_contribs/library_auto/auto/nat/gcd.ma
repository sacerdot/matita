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

set "baseuri" "cic:/matita/library_autobatch/nat/gcd".

include "auto/nat/primes.ma".

let rec gcd_aux p m n: nat \def
match divides_b n m with
[ true \Rightarrow n
| false \Rightarrow 
  match p with
  [O \Rightarrow n
  |(S q) \Rightarrow gcd_aux q n (m \mod n)]].
  
definition gcd : nat \to nat \to nat \def
\lambda n,m:nat.
  match leb n m with
  [ true \Rightarrow 
    match n with 
    [ O \Rightarrow m
    | (S p) \Rightarrow gcd_aux (S p) m (S p) ]
  | false \Rightarrow 
    match m with 
    [ O \Rightarrow n
    | (S p) \Rightarrow gcd_aux (S p) n (S p) ]].

theorem divides_mod: \forall p,m,n:nat. O < n \to p \divides m \to p \divides n \to
p \divides (m \mod n).
intros.elim H1.elim H2.
apply (witness ? ? (n2 - n1*(m / n))).
(*apply witness[|*)
  rewrite > distr_times_minus.
  rewrite < H3 in \vdash (? ? ? (? % ?)).
  rewrite < assoc_times.
  rewrite < H4 in \vdash (? ? ? (? ? (? % ?))).
  apply sym_eq.
  apply plus_to_minus.
  rewrite > sym_times.
  autobatch.
  (*letin x \def div.
  rewrite < (div_mod ? ? H).
  reflexivity.*)
(*]*)
qed.

theorem divides_mod_to_divides: \forall p,m,n:nat. O < n \to
p \divides (m \mod n) \to p \divides n \to p \divides m. 
intros.
elim H1.
elim H2.
apply (witness p m ((n1*(m / n))+n2)).
rewrite > distr_times_plus.
rewrite < H3.
rewrite < assoc_times.
rewrite < H4.
rewrite < sym_times.
autobatch.
(*apply div_mod.
assumption.*)
qed.


theorem divides_gcd_aux_mn: \forall p,m,n. O < n \to n \le m \to n \le p \to
gcd_aux p m n \divides m \land gcd_aux p m n \divides n. 
intro.
elim p
[ absurd (O < n);autobatch
  (*[ assumption
  | apply le_to_not_lt.
    assumption
  ]*)
| cut ((n1 \divides m) \lor (n1 \ndivides m))
  [ simplify.
    elim Hcut
    [ rewrite > divides_to_divides_b_true
      [ simplify.
        autobatch
        (*split
        [ assumption
        | apply (witness n1 n1 (S O)).
          apply times_n_SO
        ]*)
      | assumption
      | assumption
    ]
    | rewrite > not_divides_to_divides_b_false
      [ simplify.
        cut (gcd_aux n n1 (m \mod n1) \divides n1 \land
        gcd_aux n n1 (m \mod n1) \divides mod m n1)
        [ elim Hcut1.
          autobatch width = 4.
          (*split
          [ apply (divides_mod_to_divides ? ? n1);assumption           
          | assumption
          ]*)
        | apply H
          [ cut (O \lt m \mod n1 \lor O = mod m n1)
            [ elim Hcut1
              [ assumption
              | apply False_ind.
                autobatch
                (*apply H4.
                apply mod_O_to_divides
                [ assumption
                | apply sym_eq.
                  assumption
                ]*)
              ]
            | autobatch
              (*apply le_to_or_lt_eq.
              apply le_O_n*)
            ]
          | autobatch
            (*apply lt_to_le.
            apply lt_mod_m_m.
            assumption*)
          | apply le_S_S_to_le.
            apply (trans_le ? n1);autobatch
            (*[ autobatch.change with (m \mod n1 < n1).
              apply lt_mod_m_m.
              assumption
            | assumption
            ]*)
          ]
        ]
      | assumption
      | assumption
      ]
    ]
  | autobatch
    (*apply (decidable_divides n1 m).
    assumption*)
  ]
]
qed.

theorem divides_gcd_nm: \forall n,m.
gcd n m \divides m \land gcd n m \divides n.
intros.
(*CSC: simplify simplifies too much because of a redex in gcd *)
change with
(match leb n m with
  [ true \Rightarrow 
    match n with 
    [ O \Rightarrow m
    | (S p) \Rightarrow gcd_aux (S p) m (S p) ]
  | false \Rightarrow 
    match m with 
    [ O \Rightarrow n
    | (S p) \Rightarrow gcd_aux (S p) n (S p) ] ] \divides m
\land
match leb n m with
  [ true \Rightarrow 
    match n with 
    [ O \Rightarrow m
    | (S p) \Rightarrow gcd_aux (S p) m (S p) ]
  | false \Rightarrow 
    match m with 
    [ O \Rightarrow n
    | (S p) \Rightarrow gcd_aux (S p) n (S p) ] ] \divides n). 
apply (leb_elim n m)
[ apply (nat_case1 n)
  [ simplify.
    intros.
    autobatch
    (*split
    [ apply (witness m m (S O)).
      apply times_n_SO
    | apply (witness m O O).
      apply times_n_O
    ]*)
  | intros.
    change with
    (gcd_aux (S m1) m (S m1) \divides m
    \land 
    gcd_aux (S m1) m (S m1) \divides (S m1)).
    autobatch
    (*apply divides_gcd_aux_mn
    [ unfold lt.
      apply le_S_S.
      apply le_O_n
    | assumption
    | apply le_n
    ]*)
  ]
| simplify.
  intro.
  apply (nat_case1 m)
  [ simplify.
    intros.
    autobatch
    (*split
    [ apply (witness n O O).
      apply times_n_O
    | apply (witness n n (S O)).
      apply times_n_SO
    ]*)
  | intros.
    change with
    (gcd_aux (S m1) n (S m1) \divides (S m1)
    \land 
    gcd_aux (S m1) n (S m1) \divides n).
    cut (gcd_aux (S m1) n (S m1) \divides n
    \land 
    gcd_aux (S m1) n (S m1) \divides S m1)
    [ elim Hcut.
      autobatch
      (*split;assumption*)
    | apply divides_gcd_aux_mn
      [ autobatch
        (*unfold lt.
        apply le_S_S.
        apply le_O_n*)
      | apply not_lt_to_le.
        unfold Not. 
        unfold lt.
        intro.
        apply H.
        rewrite > H1.
        autobatch
        (*apply (trans_le ? (S n))
        [ apply le_n_Sn
        | assumption
        ]*)
      | apply le_n
      ]
    ]
  ]
]
qed.

theorem divides_gcd_n: \forall n,m. gcd n m \divides n.
intros. 
exact (proj2  ? ? (divides_gcd_nm n m)). (*autobatch non termina la dimostrazione*)
qed.

theorem divides_gcd_m: \forall n,m. gcd n m \divides m.
intros. 
exact (proj1 ? ? (divides_gcd_nm n m)). (*autobatch non termina la dimostrazione*)
qed.

theorem divides_gcd_aux: \forall p,m,n,d. O < n \to n \le m \to n \le p \to
d \divides m \to d \divides n \to d \divides gcd_aux p m n. 
intro.
elim p
[ absurd (O < n);autobatch
  (*[ assumption
  | apply le_to_not_lt.
    assumption
  ]*)
| simplify.
  cut (n1 \divides m \lor n1 \ndivides m)
  [ elim Hcut.
    rewrite > divides_to_divides_b_true;
    simplify; autobatch.
    (*[ simplify.
      assumption.
    | assumption. 
    | assumption.
    ]*) 
    rewrite > not_divides_to_divides_b_false
    [ simplify.
      apply H
      [ cut (O \lt m \mod n1 \lor O = m \mod n1)
        [ elim Hcut1
          [ assumption
          | 
            absurd (n1 \divides m);autobatch
            (*[ apply mod_O_to_divides
              [ assumption.
              | apply sym_eq.assumption.
              ]
            | assumption
            ]*)
          ]
        | autobatch 
          (*apply le_to_or_lt_eq.
          apply le_O_n*)        
        ]
      | autobatch
        (*apply lt_to_le.
        apply lt_mod_m_m.
        assumption*)
      | apply le_S_S_to_le.
        autobatch
        (*apply (trans_le ? n1)
        [ change with (m \mod n1 < n1).
          apply lt_mod_m_m.
          assumption
        | assumption
        ]*)
      | assumption
      | autobatch 
        (*apply divides_mod;
        assumption*)
      ]
    | assumption
    | assumption
    ]
  | autobatch 
    (*apply (decidable_divides n1 m).
    assumption*)
  ]
]qed.

theorem divides_d_gcd: \forall m,n,d. 
d \divides m \to d \divides n \to d \divides gcd n m. 
intros.
(*CSC: here simplify simplifies too much because of a redex in gcd *)
change with
(d \divides
match leb n m with
  [ true \Rightarrow 
    match n with 
    [ O \Rightarrow m
    | (S p) \Rightarrow gcd_aux (S p) m (S p) ]
  | false \Rightarrow 
    match m with 
    [ O \Rightarrow n
    | (S p) \Rightarrow gcd_aux (S p) n (S p) ]]).
apply (leb_elim n m)
[ apply (nat_case1 n)
  [ simplify.
    intros.
    assumption
  | intros.
    change with (d \divides gcd_aux (S m1) m (S m1)).
    apply divides_gcd_aux      
    [ unfold lt.autobatch
      (*apply le_S_S.
      apply le_O_n.*)
    | assumption.
    | apply le_n. (*chiude il goal anche con autobatch*)
    | assumption.
    | rewrite < H2.
      assumption
    ]
  ]
| apply (nat_case1 m)
  [ simplify.
    intros.
    assumption
  | intros.
    change with (d \divides gcd_aux (S m1) n (S m1)).
    apply divides_gcd_aux
    [ unfold lt.autobatch
      (*apply le_S_S.
      apply le_O_n*)
    | autobatch
      (*apply lt_to_le.
      apply not_le_to_lt.
      assumption*)
    | apply le_n (*chiude il goal anche con autobatch*)
    | assumption
    | rewrite < H2.
      assumption
    ]
  ]
]
qed.

theorem eq_minus_gcd_aux: \forall p,m,n.O < n \to n \le m \to n \le p \to
\exists a,b. a*n - b*m = gcd_aux p m n \lor b*m - a*n = gcd_aux p m n.
intro.
elim p
[ absurd (O < n);autobatch
  (*[ assumption
  | apply le_to_not_lt
    assumption.
  ]*)
| cut (O < m)
  [ cut (n1 \divides m \lor  n1 \ndivides m)
    [ simplify.
      elim Hcut1
      [ rewrite > divides_to_divides_b_true
        [ simplify.
          apply (ex_intro ? ? (S O)).
          apply (ex_intro ? ? O).
          autobatch
          (*left.
          simplify.
          rewrite < plus_n_O.
          apply sym_eq.apply minus_n_O*)
        | assumption
        | assumption
        ]
      | rewrite > not_divides_to_divides_b_false
        [ change with
          (\exists a,b.
          a*n1 - b*m = gcd_aux n n1 (m \mod n1)
          \lor 
          b*m - a*n1 = gcd_aux n n1 (m \mod n1)).
          cut   
          (\exists a,b.
          a*(m \mod n1) - b*n1= gcd_aux n n1 (m \mod n1)
          \lor
          b*n1 - a*(m \mod n1) = gcd_aux n n1 (m \mod n1))
          [ elim Hcut2.
            elim H5.
            elim H6
            [ (* first case *)
              rewrite < H7.
              apply (ex_intro ? ? (a1+a*(m / n1))).
              apply (ex_intro ? ? a).
              right.
              rewrite < sym_plus.
              rewrite < (sym_times n1).
              rewrite > distr_times_plus.
              rewrite > (sym_times n1).
              rewrite > (sym_times n1).
              rewrite > (div_mod m n1) in \vdash (? ? (? % ?) ?);autobatch
              (*[ rewrite > assoc_times.
                rewrite < sym_plus.
                rewrite > distr_times_plus.
                rewrite < eq_minus_minus_minus_plus.
                rewrite < sym_plus.autobatch.
                rewrite < plus_minus
                [ rewrite < minus_n_n.
                  reflexivity
                | apply le_n
                ]
              | assumption
              ]*)
            | (* second case *)
              rewrite < H7.
              apply (ex_intro ? ? (a1+a*(m / n1))).
              apply (ex_intro ? ? a).
              left.
              (* clear Hcut2.clear H5.clear H6.clear H. *)
              rewrite > sym_times.
              rewrite > distr_times_plus.
              rewrite > sym_times.
              rewrite > (sym_times n1).
              rewrite > (div_mod m n1) in \vdash (? ? (? ? %) ?)
              [ rewrite > distr_times_plus.
                rewrite > assoc_times.
                rewrite < eq_minus_minus_minus_plus.
                autobatch
                (*rewrite < sym_plus.
                rewrite < plus_minus
                [ rewrite < minus_n_n.
                  reflexivity
                | apply le_n
                ]*)
              | assumption
              ]
            ]
          | apply (H n1 (m \mod n1))
            [ cut (O \lt m \mod n1 \lor O = m \mod n1)
              [ elim Hcut2
                [ assumption 
                | absurd (n1 \divides m);autobatch
                  (*[ apply mod_O_to_divides
                    [ assumption
                    | symmetry.
                      assumption
                    ]
                  | assumption
                  ]*)
                ]
              | autobatch
                (*apply le_to_or_lt_eq.
                apply le_O_n*)
              ]
            | autobatch
              (*apply lt_to_le.
              apply lt_mod_m_m.
              assumption*)
            | apply le_S_S_to_le.
              autobatch
              (*apply (trans_le ? n1)
              [ change with (m \mod n1 < n1).
                apply lt_mod_m_m.
                assumption
              | assumption
              ]*)
            ]
          ]
        | assumption
        | assumption
        ]
      ]
    | autobatch
      (*apply (decidable_divides n1 m).
      assumption*)
    ]
  | autobatch
    (*apply (lt_to_le_to_lt ? n1);assumption *)   
  ]
]
qed.

theorem eq_minus_gcd:
 \forall m,n.\exists a,b.a*n - b*m = (gcd n m) \lor b*m - a*n = (gcd n m).
intros.
unfold gcd.
apply (leb_elim n m)
[ apply (nat_case1 n)
  [ simplify.
    intros.
    apply (ex_intro ? ? O).
    apply (ex_intro ? ? (S O)).
    autobatch
    (*right.simplify.
    rewrite < plus_n_O.
    apply sym_eq.
    apply minus_n_O*)
  | intros.
    change with 
    (\exists a,b.
    a*(S m1) - b*m = (gcd_aux (S m1) m (S m1)) 
    \lor b*m - a*(S m1) = (gcd_aux (S m1) m (S m1))).
    autobatch
    (*apply eq_minus_gcd_aux
    [ unfold lt. 
      apply le_S_S.
      apply le_O_n
    | assumption
    | apply le_n
    ]*)
  ]  
| apply (nat_case1 m)
  [ simplify.
    intros.
    apply (ex_intro ? ? (S O)).
    apply (ex_intro ? ? O).
    autobatch
    (*left.simplify.
    rewrite < plus_n_O.
    apply sym_eq.
    apply minus_n_O*)
  | intros.
    change with 
    (\exists a,b.
    a*n - b*(S m1) = (gcd_aux (S m1) n (S m1)) 
    \lor b*(S m1) - a*n = (gcd_aux (S m1) n (S m1))).
    cut 
    (\exists a,b.
    a*(S m1) - b*n = (gcd_aux (S m1) n (S m1))
    \lor
    b*n - a*(S m1) = (gcd_aux (S m1) n (S m1)))
    [ elim Hcut.
      elim H2.
      elim H3;apply (ex_intro ? ? a1);autobatch
      (*[ apply (ex_intro ? ? a1).
        apply (ex_intro ? ? a).
        right.
        assumption
      | apply (ex_intro ? ? a1).        
        apply (ex_intro ? ? a).
        left.
        assumption
      ]*)
    | apply eq_minus_gcd_aux;autobatch
      (*[ unfold lt. 
        apply le_S_S.
        apply le_O_n
      | autobatch.apply lt_to_le.
        apply not_le_to_lt.
        assumption
      | apply le_n.
      ]*)
    ]
  ]
]
qed.

(* some properties of gcd *)

theorem gcd_O_n: \forall n:nat. gcd O n = n.
autobatch.
(*intro.simplify.reflexivity.*)
qed.

theorem gcd_O_to_eq_O:\forall m,n:nat. (gcd m n) = O \to
m = O \land n = O.
intros.
cut (O \divides n \land O \divides m)
[ elim Hcut.
  autobatch size = 7;
  (*
  split; 
    [ apply antisymmetric_divides
      [ apply divides_n_O
      | assumption
      ]
    | apply antisymmetric_divides
      [ apply divides_n_O
      | assumption
      ]
    ]*)
| rewrite < H.
  apply divides_gcd_nm
]
qed.

theorem lt_O_gcd:\forall m,n:nat. O < n \to O < gcd m n.
intros.
autobatch.
(*
apply (divides_to_lt_O (gcd m n) n ? ?);
  [apply (H).
  |apply (divides_gcd_m m n).
  ]
*)
qed.

theorem gcd_n_n: \forall n.gcd n n = n.
intro.
autobatch.
(*
apply (antisymmetric_divides (gcd n n) n ? ?);
  [apply (divides_gcd_n n n).
  |apply (divides_d_gcd n n n ? ?);
    [apply (reflexive_divides n).
    |apply (reflexive_divides n).
    ]
  ]
*)
qed.

theorem gcd_SO_to_lt_O: \forall i,n. (S O) < n \to gcd i n = (S O) \to
O < i.
intros.
elim (le_to_or_lt_eq ? ? (le_O_n i))
[ assumption
| absurd ((gcd i n) = (S O))
  [ assumption
  | rewrite < H2.
    simplify.
    unfold.
    intro.
    apply (lt_to_not_eq (S O) n H).
    autobatch
    (*apply sym_eq.
    assumption*)
  ]
]
qed.

theorem gcd_SO_to_lt_n: \forall i,n. (S O) < n \to i \le n \to gcd i n = (S O) \to
i < n.
intros.
elim (le_to_or_lt_eq ? ? H1)
  [assumption
  |absurd ((gcd i n) = (S O))
    [assumption
    |rewrite > H3.
     rewrite > gcd_n_n.
     unfold.intro.
     apply (lt_to_not_eq (S O) n H).
     apply sym_eq.assumption
    ]
  ]
qed.

theorem  gcd_n_times_nm: \forall n,m. O < m \to gcd n (n*m) = n.
intro.apply (nat_case n)
  [intros.reflexivity
  |intros.
   apply le_to_le_to_eq
    [apply divides_to_le
      [apply lt_O_S|apply divides_gcd_n]
    |apply divides_to_le
      [apply lt_O_gcd.rewrite > (times_n_O O).
       apply lt_times[apply lt_O_S|assumption]
      |apply divides_d_gcd
        [apply (witness ? ? m1).reflexivity
        |apply divides_n_n
        ]
      ]
    ]
  ]
qed.

theorem symmetric_gcd: symmetric nat gcd.
(*CSC: bug here: unfold symmetric does not work *)
change with 
(\forall n,m:nat. gcd n m = gcd m n).
intros.
autobatch size = 7.
(*
apply (antisymmetric_divides (gcd n m) (gcd m n) ? ?);
  [apply (divides_d_gcd n m (gcd n m) ? ?);
    [apply (divides_gcd_n n m).
    |apply (divides_gcd_m n m).
    ]
  |apply (divides_d_gcd m n (gcd m n) ? ?);
    [apply (divides_gcd_n m n).
    |apply (divides_gcd_m m n).
    ]
  ]
*)
qed.

variant sym_gcd: \forall n,m:nat. gcd n m = gcd m n \def
symmetric_gcd.

theorem le_gcd_times: \forall m,n,p:nat. O< p \to gcd m n \le gcd m (n*p).
intros.
apply (nat_case n)
[ apply le_n
| intro.
  apply divides_to_le
  [ apply lt_O_gcd.
    autobatch
    (*rewrite > (times_n_O O).
    apply lt_times
    [ autobatch.unfold lt.
      apply le_S_S.
      apply le_O_n
    | assumption
    ]*)
  | apply divides_d_gcd;autobatch
    (*[ apply (transitive_divides ? (S m1))
      [ apply divides_gcd_m
      | apply (witness ? ? p).
        reflexivity
      ]
    | apply divides_gcd_n
    ]*)
  ]
]
qed.

theorem gcd_times_SO_to_gcd_SO: \forall m,n,p:nat. O < n \to O < p \to 
gcd m (n*p) = (S O) \to gcd m n = (S O).
intros.
apply antisymmetric_le
[ rewrite < H2.
  autobatch
  (*apply le_gcd_times.
  assumption*)
| autobatch
  (*change with (O < gcd m n). 
  apply lt_O_gcd.
  assumption*)
]
qed.

(* for the "converse" of the previous result see the end  of this development *)

theorem eq_gcd_SO_to_not_divides: \forall n,m. (S O) < n \to 
(gcd n m) = (S O) \to \lnot (divides n m).
intros.unfold.intro.
elim H2.
generalize in match H1.
rewrite > H3.
intro.
cut (O < n2)
[ elim (gcd_times_SO_to_gcd_SO n n n2 ? ? H4)
  [ cut (gcd n (n*n2) = n);autobatch
    (*[ autobatch.apply (lt_to_not_eq (S O) n)
      [ assumption
      | rewrite < H4.
        assumption
      ]
    | apply gcd_n_times_nm.
      assumption
    ]*)
  | autobatch
    (*apply (trans_lt ? (S O))
    [ apply le_n
    | assumption
    ]*)
  | assumption
  ]
| elim (le_to_or_lt_eq O n2 (le_O_n n2))
  [ assumption
  | apply False_ind.
    apply (le_to_not_lt n (S O))
    [ rewrite < H4.
      apply divides_to_le;autobatch
      (*[ rewrite > H4.
        apply lt_O_S
      | apply divides_d_gcd
        [ apply (witness ? ? n2).
          reflexivity
        | apply divides_n_n
        ]
      ]*)
    | assumption
    ]
  ]
]
qed.

theorem gcd_SO_n: \forall n:nat. gcd (S O) n = (S O).
intro.
autobatch.
(*
apply (symmetric_eq nat (S O) (gcd (S O) n) ?).
apply (antisymmetric_divides (S O) (gcd (S O) n) ? ?);
  [apply (divides_SO_n (gcd (S O) n)).
  |apply (divides_gcd_n (S O) n).
  ]
*)
qed.

theorem divides_gcd_mod: \forall m,n:nat. O < n \to
divides (gcd m n) (gcd n (m \mod n)).
intros.
autobatch width = 4.
(*apply divides_d_gcd
[ apply divides_mod
  [ assumption
  | apply divides_gcd_n
  | apply divides_gcd_m
  ]
| apply divides_gcd_m.
]*)
qed.

theorem divides_mod_gcd: \forall m,n:nat. O < n \to
divides (gcd n (m \mod n)) (gcd m n) .
intros.
autobatch.
(*apply divides_d_gcd
[ apply divides_gcd_n
| apply (divides_mod_to_divides ? ? n)
  [ assumption
  | apply divides_gcd_m
  | apply divides_gcd_n
  ]
]*)
qed.

theorem gcd_mod: \forall m,n:nat. O < n \to
(gcd n (m \mod n)) = (gcd m n) .
intros.
autobatch.
(*apply antisymmetric_divides
[ apply divides_mod_gcd.
  assumption
| apply divides_gcd_mod.
  assumption
]*)
qed.

(* gcd and primes *)

theorem prime_to_gcd_SO: \forall n,m:nat. prime n \to n \ndivides m \to
gcd n m = (S O).
intros.unfold prime in H.
elim H.
apply antisym_le
[ apply not_lt_to_le.unfold Not.unfold lt.
  intro.
  apply H1.
  rewrite < (H3 (gcd n m));
  [autobatch|autobatch| unfold lt; autobatch]
  (*[ apply divides_gcd_m
  | apply divides_gcd_n
  | assumption
  ]*)
| cut (O < gcd n m \lor O = gcd n m)
  [ elim Hcut
    [ assumption
    | apply False_ind.
      apply (not_le_Sn_O (S O)).
      cut (n=O \land m=O)
      [ elim Hcut1.
        rewrite < H5 in \vdash (? ? %).
        assumption
      | autobatch
        (*apply gcd_O_to_eq_O.
        apply sym_eq.
        assumption*)
      ]
    ]
  | autobatch
    (*apply le_to_or_lt_eq.
    apply le_O_n*)
  ]
]
qed.

theorem divides_times_to_divides: \forall n,p,q:nat.prime n \to n \divides p*q \to
n \divides p \lor n \divides q.
intros.
cut (n \divides p \lor n \ndivides p)
[elim Hcut
    [left.assumption
    |right.
     cut (\exists a,b. a*n - b*p = (S O) \lor b*p - a*n = (S O))
       [elim Hcut1.elim H3.elim H4
         [(* first case *)
          rewrite > (times_n_SO q).rewrite < H5.
          rewrite > distr_times_minus.
          rewrite > (sym_times q (a1*p)).
          rewrite > (assoc_times a1).
          elim H1.          
          (*
             rewrite > H6.
             applyS (witness n (n*(q*a-a1*n2)) (q*a-a1*n2))
             reflexivity. *)
          applyS (witness n ? ? (refl_eq ? ?)) (* timeout=50 *)          
          (*
          rewrite < (sym_times n).rewrite < assoc_times.
          rewrite > (sym_times q).rewrite > assoc_times.
          rewrite < (assoc_times a1).rewrite < (sym_times n).
          rewrite > (assoc_times n).
          rewrite < distr_times_minus.
          apply (witness ? ? (q*a-a1*n2)).reflexivity
          *)
         |(* second case *)
          rewrite > (times_n_SO q).rewrite < H5.
          rewrite > distr_times_minus.
          rewrite > (sym_times q (a1*p)).
          rewrite > (assoc_times a1).
          elim H1.
          autobatch
          (*rewrite > H6.
          rewrite < sym_times.rewrite > assoc_times.
          rewrite < (assoc_times q).
          rewrite < (sym_times n).
          rewrite < distr_times_minus.
          apply (witness ? ? (n2*a1-q*a)).
          reflexivity*)
        ](* end second case *)
     | rewrite < (prime_to_gcd_SO n p);autobatch
      (* [ apply eq_minus_gcd
       | assumption
       | assumption
       ]*)
     ]
   ]
 | apply (decidable_divides n p).
   apply (trans_lt ? (S O))
    [ autobatch
      (*unfold lt.
      apply le_n*)
    | unfold prime in H.
      elim H. 
      assumption
    ]
  ]
qed.

theorem eq_gcd_times_SO: \forall m,n,p:nat. O < n \to O < p \to
gcd m n = (S O) \to gcd m p = (S O) \to gcd m (n*p) = (S O).
intros.
apply antisymmetric_le
[ apply not_lt_to_le.
  unfold Not.intro.
  cut (divides (smallest_factor (gcd m (n*p))) n \lor 
       divides (smallest_factor (gcd m (n*p))) p)
  [ elim Hcut
    [ apply (not_le_Sn_n (S O)).
      change with ((S O) < (S O)).
      rewrite < H2 in \vdash (? ? %).
      apply (lt_to_le_to_lt ? (smallest_factor (gcd m (n*p))))
      [ autobatch
        (*apply lt_SO_smallest_factor.
        assumption*)
      | apply divides_to_le; 
        [ autobatch |   
        apply divides_d_gcd
         [ assumption
         | apply (transitive_divides ? (gcd m (n*p)))
           [ autobatch.
           | autobatch.
           ]
         ]
        ]
        (*[ rewrite > H2.
          unfold lt.
          apply le_n
        | apply divides_d_gcd
          [ assumption
          | apply (transitive_divides ? (gcd m (n*p)))
            [ apply divides_smallest_factor_n.
              apply (trans_lt ? (S O))
              [ unfold lt.
                apply le_n
              | assumption
              ]
            | apply divides_gcd_n
            ]
          ]         
        ]*)
      ]
    | apply (not_le_Sn_n (S O)).
      change with ((S O) < (S O)).
      rewrite < H3 in \vdash (? ? %).
      apply (lt_to_le_to_lt ? (smallest_factor (gcd m (n*p))))
      [ apply lt_SO_smallest_factor.
        assumption
      | apply divides_to_le; 
        [ autobatch |
        apply divides_d_gcd
         [ assumption
         | apply (transitive_divides ? (gcd m (n*p)))
           [ autobatch.
           | autobatch.
           ]
         ]
        ]
        (*[ rewrite > H3.
          unfold lt.
          apply le_n
        | apply divides_d_gcd
          [ assumption
          | apply (transitive_divides ? (gcd m (n*p)))
            [ apply divides_smallest_factor_n.
              apply (trans_lt ? (S O))
              [  unfold lt. 
                apply le_n
              | assumption
              ]
            | apply divides_gcd_n
            ]
          ]
        ]*)
      ]
    ]
  | apply divides_times_to_divides;
    [ autobatch | 
      apply (transitive_divides ? (gcd m (n*p)))
           [ autobatch.
           | autobatch.
           ]
         ]
        ]
    (*[ apply prime_smallest_factor_n.
      assumption
    | autobatch.apply (transitive_divides ? (gcd m (n*p)))
      [ apply divides_smallest_factor_n.
        apply (trans_lt ? (S O))
        [ unfold lt. 
          apply le_n
        | assumption
        ]
      | apply divides_gcd_m
      ]
    ]*)
| autobatch
  (*change with (O < gcd m (n*p)).
  apply lt_O_gcd.
  rewrite > (times_n_O O).
  apply lt_times;assumption.*)
]
qed.

theorem gcd_SO_to_divides_times_to_divides: \forall m,n,p:nat. O < n \to
gcd n m = (S O) \to n \divides (m*p) \to n \divides p.
intros.
cut (n \divides p \lor n \ndivides p)
[ elim Hcut
  [ assumption
  | cut (\exists a,b. a*n - b*m = (S O) \lor b*m - a*n = (S O))
    [ elim Hcut1.elim H4.elim H5         
      [(* first case *)
        rewrite > (times_n_SO p).rewrite < H6.
        rewrite > distr_times_minus.
        rewrite > (sym_times p (a1*m)).
        rewrite > (assoc_times a1).
        elim H2.
        applyS (witness n ? ? (refl_eq ? ?)) (* timeout=50 *).
      |(* second case *)
        rewrite > (times_n_SO p).rewrite < H6.
        rewrite > distr_times_minus.
        rewrite > (sym_times p (a1*m)).
        rewrite > (assoc_times a1).
        elim H2.
        applyS (witness n ? ? (refl_eq ? ?)).
      ](* end second case *)
    | rewrite < H1.
      apply eq_minus_gcd
    ]
  ]
| autobatch
  (*apply (decidable_divides n p).
  assumption.*)
]
qed.