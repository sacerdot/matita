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

set "baseuri" "cic:/matita/library_autobatch/nat/primes".

include "auto/nat/div_and_mod.ma".
include "auto/nat/minimization.ma".
include "auto/nat/sigma_and_pi.ma".
include "auto/nat/factorial.ma".

inductive divides (n,m:nat) : Prop \def
witness : \forall p:nat.m = times n p \to divides n m.

interpretation "divides" 'divides n m = (divides n m).
interpretation "not divides" 'ndivides n m = (Not (divides n m)).

theorem reflexive_divides : reflexive nat divides.
unfold reflexive.
intros.
exact (witness x x (S O) (times_n_SO x)).
qed.

theorem divides_to_div_mod_spec :
\forall n,m. O < n \to n \divides m \to div_mod_spec m n (m / n) O.
intros.
elim H1.
rewrite > H2.
constructor 1
[ assumption
| apply (lt_O_n_elim n H).
  intros.
  autobatch
  (*rewrite < plus_n_O.
  rewrite > div_times.
  apply sym_times*)
]
qed.

theorem div_mod_spec_to_divides :
\forall n,m,p. div_mod_spec m n p O \to n \divides m.
intros.
elim H.
autobatch.
(*apply (witness n m p).
rewrite < sym_times.
rewrite > (plus_n_O (p*n)).
assumption*)
qed.

theorem divides_to_mod_O:
\forall n,m. O < n \to n \divides m \to (m \mod n) = O.
intros.
apply (div_mod_spec_to_eq2 m n (m / n) (m \mod n) (m / n) O)
[ autobatch
  (*apply div_mod_spec_div_mod.
  assumption*)
| autobatch
  (*apply divides_to_div_mod_spec;assumption*)
]
qed.

theorem mod_O_to_divides:
\forall n,m. O< n \to (m \mod n) = O \to  n \divides m.
intros.
apply (witness n m (m / n)).
rewrite > (plus_n_O (n * (m / n))).
rewrite < H1.
rewrite < sym_times.
autobatch.
(* Andrea: perche' hint non lo trova ?*)
(*apply div_mod.
assumption.*)
qed.

theorem divides_n_O: \forall n:nat. n \divides O.
intro.
autobatch.
(*apply (witness n O O).
apply times_n_O.*)
qed.

theorem divides_n_n: \forall n:nat. n \divides n.
autobatch.
(*intro.
apply (witness n n (S O)).
apply times_n_SO.*)
qed.

theorem divides_SO_n: \forall n:nat. (S O) \divides n.
intro.
autobatch.
(*apply (witness (S O) n n).
simplify.
apply plus_n_O.*)
qed.

theorem divides_plus: \forall n,p,q:nat. 
n \divides p \to n \divides q \to n \divides p+q.
intros.
elim H.
elim H1.
apply (witness n (p+q) (n2+n1)).
autobatch.
(*rewrite > H2.
rewrite > H3.
apply sym_eq.
apply distr_times_plus.*)
qed.

theorem divides_minus: \forall n,p,q:nat. 
divides n p \to divides n q \to divides n (p-q).
intros.
elim H.
elim H1.
apply (witness n (p-q) (n2-n1)).
autobatch.
(*rewrite > H2.
rewrite > H3.
apply sym_eq.
apply distr_times_minus.*)
qed.

theorem divides_times: \forall n,m,p,q:nat. 
n \divides p \to m \divides q \to n*m \divides p*q.
intros.
elim H.
elim H1.
apply (witness (n*m) (p*q) (n2*n1)).
rewrite > H2.
rewrite > H3.
apply (trans_eq nat ? (n*(m*(n2*n1))))
[ apply (trans_eq nat ? (n*(n2*(m*n1))))
  [ apply assoc_times
  | apply eq_f.
    apply (trans_eq nat ? ((n2*m)*n1))
    [ autobatch
      (*apply sym_eq. 
      apply assoc_times*)
    | rewrite > (sym_times n2 m).
      apply assoc_times
    ]
  ]
| autobatch
  (*apply sym_eq. 
  apply assoc_times*)
]
qed.

theorem transitive_divides: transitive ? divides.
unfold.
intros.
elim H.
elim H1.
apply (witness x z (n2*n)).
autobatch.
(*rewrite > H3.
rewrite > H2.
apply assoc_times.*)
qed.

variant trans_divides: \forall n,m,p. 
 n \divides m \to m \divides p \to n \divides p \def transitive_divides.

theorem eq_mod_to_divides:\forall n,m,p. O< p \to
mod n p = mod m p \to divides p (n-m).
intros.
cut (n \le m \or \not n \le m)
[ elim Hcut
  [ cut (n-m=O)
    [ autobatch
      (*rewrite > Hcut1.
      apply (witness p O O).
      apply times_n_O*)
    | autobatch
      (*apply eq_minus_n_m_O.
      assumption*)
    ]
  | apply (witness p (n-m) ((div n p)-(div m p))).
    rewrite > distr_times_minus.
    rewrite > sym_times.
    rewrite > (sym_times p).
    cut ((div n p)*p = n - (mod n p))
    [ rewrite > Hcut1.
      rewrite > eq_minus_minus_minus_plus.
      rewrite > sym_plus.
      rewrite > H1.
      autobatch
      (*rewrite < div_mod
      [ reflexivity
      | assumption
      ]*)
    | apply sym_eq.
      apply plus_to_minus.
      rewrite > sym_plus.
      autobatch
      (*apply div_mod.
      assumption*)
    ]
  ]
| apply (decidable_le n m)
]
qed.

theorem antisymmetric_divides: antisymmetric nat divides.
unfold antisymmetric.
intros.
elim H.
elim H1.
apply (nat_case1 n2)
[ intro.
  rewrite > H3.
  rewrite > H2.
  rewrite > H4.  
  rewrite < times_n_O.
  reflexivity
| intros.
  apply (nat_case1 n)
  [ intro.
    rewrite > H2.
    rewrite > H3.
    rewrite > H5.
    autobatch
    (*rewrite < times_n_O.
    reflexivity*)
  | intros.
    apply antisymmetric_le
    [ rewrite > H2.
      rewrite > times_n_SO in \vdash (? % ?).
      apply le_times_r.
      rewrite > H4.
      autobatch
      (*apply le_S_S.
      apply le_O_n*)
    | rewrite > H3.
      rewrite > times_n_SO in \vdash (? % ?).
      apply le_times_r.
      rewrite > H5.
      autobatch
      (*apply le_S_S.
      apply le_O_n*)
    ]
  ]
]
qed.

(* divides le *)
theorem divides_to_le : \forall n,m. O < m \to n \divides m \to n \le m.
intros.
elim H1.
rewrite > H2.
cut (O < n2)
[ apply (lt_O_n_elim n2 Hcut).
  intro.
  autobatch
  (*rewrite < sym_times.
  simplify.
  rewrite < sym_plus.
  apply le_plus_n*)
| elim (le_to_or_lt_eq O n2)
  [ assumption
  | absurd (O<m)
    [ assumption
    | rewrite > H2.
      rewrite < H3.
      rewrite < times_n_O.
      apply (not_le_Sn_n O)
    ]
  | apply le_O_n
  ]
]
qed.

theorem divides_to_lt_O : \forall n,m. O < m \to n \divides m \to O < n.
intros.
elim H1.
elim (le_to_or_lt_eq O n (le_O_n n))
[ assumption
| rewrite < H3.
  absurd (O < m)
  [ assumption
  | rewrite > H2.
    rewrite < H3.
    autobatch
    (*simplify.
    exact (not_le_Sn_n O)*)
  ]
]
qed.

(* boolean divides *)
definition divides_b : nat \to nat \to bool \def
\lambda n,m :nat. (eqb (m \mod n) O).
  
theorem divides_b_to_Prop :
\forall n,m:nat. O < n \to
match divides_b n m with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m].
intros.
unfold divides_b.
apply eqb_elim
[ intro.
  simplify.
  autobatch
  (*apply mod_O_to_divides;assumption*)
| intro.
  simplify.
  unfold Not.
  intro.
  autobatch
  (*apply H1.
  apply divides_to_mod_O;assumption*)
]
qed.

theorem divides_b_true_to_divides :
\forall n,m:nat. O < n \to
(divides_b n m = true ) \to n \divides m.
intros.
change with 
match true with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m].
rewrite < H1.
apply divides_b_to_Prop.
assumption.
qed.

theorem divides_b_false_to_not_divides :
\forall n,m:nat. O < n \to
(divides_b n m = false ) \to n \ndivides m.
intros.
change with 
match false with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m].
rewrite < H1.
apply divides_b_to_Prop.
assumption.
qed.

theorem decidable_divides: \forall n,m:nat.O < n \to
decidable (n \divides m).
intros.
unfold decidable.
cut 
(match divides_b n m with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m] \to n \divides m \lor n \ndivides m)
[ apply Hcut.
  apply divides_b_to_Prop.
  assumption
| elim (divides_b n m)
  [ left.
    (*qui autobatch non chiude il goal, chiuso dalla sola apply H1*)
    apply H1
  | right.
    (*qui autobatch non chiude il goal, chiuso dalla sola apply H1*)
    apply H1
  ]
]
qed.

theorem divides_to_divides_b_true : \forall n,m:nat. O < n \to
n \divides m \to divides_b n m = true.
intros.
cut (match (divides_b n m) with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m] \to ((divides_b n m) = true))
[ apply Hcut.
  apply divides_b_to_Prop.
  assumption
| elim (divides_b n m)
  [ reflexivity
  | absurd (n \divides m)
    [ assumption
    | (*qui autobatch non chiude il goal, chiuso dalla sola applicazione di assumption*)
      assumption
    ]
  ]
]
qed.

theorem not_divides_to_divides_b_false: \forall n,m:nat. O < n \to
\lnot(n \divides m) \to (divides_b n m) = false.
intros.
cut (match (divides_b n m) with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m] \to ((divides_b n m) = false))
[ apply Hcut.
  apply divides_b_to_Prop.
  assumption
| elim (divides_b n m)
  [ absurd (n \divides m)
    [ (*qui autobatch non chiude il goal, chiuso dalla sola tattica assumption*)
      assumption
    | assumption
    ]
  | reflexivity
  ]
]
qed.

(* divides and pi *)
theorem divides_f_pi_f : \forall f:nat \to nat.\forall n,m,i:nat. 
m \le i \to i \le n+m \to f i \divides pi n f m.
intros 5.
elim n
[ simplify.
  cut (i = m)
  [ autobatch
    (*rewrite < Hcut.
    apply divides_n_n*)
  | apply antisymmetric_le
    [ assumption
    | assumption
    ]
  ]
| simplify.
  cut (i < S n1+m \lor i = S n1 + m)
  [ elim Hcut
    [ apply (transitive_divides ? (pi n1 f m))
      [ apply H1.
        autobatch
        (*apply le_S_S_to_le.
        assumption*)
      | autobatch
        (*apply (witness ? ? (f (S n1+m))).
        apply sym_times*)
      ]
    | autobatch
      (*rewrite > H3.
      apply (witness ? ? (pi n1 f m)).
      reflexivity*)
    ]
  | autobatch
    (*apply le_to_or_lt_eq.
    assumption*)
  ]
]
qed.

(*
theorem mod_S_pi: \forall f:nat \to nat.\forall n,i:nat. 
i < n \to (S O) < (f i) \to (S (pi n f)) \mod (f i) = (S O).
intros.cut (pi n f) \mod (f i) = O.
rewrite < Hcut.
apply mod_S.apply trans_lt O (S O).apply le_n (S O).assumption.
rewrite > Hcut.assumption.
apply divides_to_mod_O.apply trans_lt O (S O).apply le_n (S O).assumption.
apply divides_f_pi_f.assumption.
qed.
*)

(* divides and fact *)
theorem divides_fact : \forall n,i:nat. 
O < i \to i \le n \to i \divides n!.
intros 3.
elim n
[ absurd (O<i)
  [ assumption
  | autobatch
    (*apply (le_n_O_elim i H1).
    apply (not_le_Sn_O O)*)
  ]
| change with (i \divides (S n1)*n1!).
  apply (le_n_Sm_elim i n1 H2)
  [ intro.
    apply (transitive_divides ? n1!)
    [ autobatch
      (*apply H1.
      apply le_S_S_to_le. 
      assumption*)
    | autobatch
      (*apply (witness ? ? (S n1)).
      apply sym_times*)
    ]
  | intro.
    autobatch
    (*rewrite > H3.
    apply (witness ? ? n1!).
    reflexivity*)
  ]
]
qed.

theorem mod_S_fact: \forall n,i:nat. 
(S O) < i \to i \le n \to (S n!) \mod i = (S O).
intros.
cut (n! \mod i = O)
[ rewrite < Hcut.
  apply mod_S
  [ autobatch
    (*apply (trans_lt O (S O))
    [ apply (le_n (S O))
    | assumption
    ]*)
  | rewrite > Hcut.
    assumption
  ]
| autobatch(*
  apply divides_to_mod_O
  [ apply ltn_to_ltO [| apply H]
  | apply divides_fact
    [ apply ltn_to_ltO [| apply H]
    | assumption
    ]
  ]*)
] 
qed.

theorem not_divides_S_fact: \forall n,i:nat. 
(S O) < i \to i \le n \to i \ndivides S n!.
intros.
apply divides_b_false_to_not_divides
[ autobatch
  (*apply (trans_lt O (S O))
  [ apply (le_n (S O))
  | assumption
  ]*)
| unfold divides_b.
  rewrite > mod_S_fact;autobatch
  (*[ simplify.
    reflexivity
  | assumption
  | assumption
  ]*)
]
qed.

(* prime *)
definition prime : nat \to  Prop \def
\lambda n:nat. (S O) < n \land 
(\forall m:nat. m \divides n \to (S O) < m \to  m = n).

theorem not_prime_O: \lnot (prime O).
unfold Not.
unfold prime.
intro.
elim H.
apply (not_le_Sn_O (S O) H1).
qed.

theorem not_prime_SO: \lnot (prime (S O)).
unfold Not.
unfold prime.
intro.
elim H.
apply (not_le_Sn_n (S O) H1).
qed.

(* smallest factor *)
definition smallest_factor : nat \to nat \def
\lambda n:nat. 
match n with
[ O \Rightarrow O
| (S p) \Rightarrow 
  match p with
  [ O \Rightarrow (S O)
  | (S q) \Rightarrow min_aux q (S(S q)) (\lambda m.(eqb ((S(S q)) \mod m) O))]].

(* it works ! 
theorem example1 : smallest_prime_factor (S(S(S O))) = (S(S(S O))).
normalize.reflexivity.
qed.

theorem example2: smallest_prime_factor (S(S(S(S O)))) = (S(S O)).
normalize.reflexivity.
qed.

theorem example3 : smallest_prime_factor (S(S(S(S(S(S(S O))))))) = (S(S(S(S(S(S(S O))))))).
simplify.reflexivity.
qed. *)

theorem lt_SO_smallest_factor: 
\forall n:nat. (S O) < n \to (S O) < (smallest_factor n).
intro.
apply (nat_case n)
[ autobatch
  (*intro.
  apply False_ind.
  apply (not_le_Sn_O (S O) H)*)
| intro.
  apply (nat_case m)
  [ autobatch
    (*intro. apply False_ind.
    apply (not_le_Sn_n (S O) H)*)  
  | intros.
    change with 
    (S O < min_aux m1 (S(S m1)) (\lambda m.(eqb ((S(S m1)) \mod m) O))).
    apply (lt_to_le_to_lt ? (S (S O)))
    [ apply (le_n (S(S O)))
    | cut ((S(S O)) = (S(S m1)) - m1)
      [ rewrite > Hcut.
        apply le_min_aux
      | apply sym_eq.
        apply plus_to_minus.
        autobatch
        (*rewrite < sym_plus.
        simplify.
        reflexivity*)        
      ]
    ]
  ]
]
qed.

theorem lt_O_smallest_factor: \forall n:nat. O < n \to O < (smallest_factor n).
intro.
apply (nat_case n)
[ autobatch
  (*intro.
  apply False_ind.
  apply (not_le_Sn_n O H)*)
| intro.
  apply (nat_case m)
  [ autobatch
    (*intro.
    simplify.
    unfold lt.
    apply le_n*)
  | intros.
    apply (trans_lt ? (S O))
    [ autobatch
      (*unfold lt.
      apply le_n*)
    | apply lt_SO_smallest_factor.
      unfold lt.autobatch
      (*apply le_S_S.
      apply le_S_S.
      apply le_O_n*)     
    ]
  ]
]
qed.

theorem divides_smallest_factor_n : 
\forall n:nat. O < n \to smallest_factor n \divides n.
intro.
apply (nat_case n)
[ intro.
  autobatch
  (*apply False_ind.
  apply (not_le_Sn_O O H)*)
| intro.
  apply (nat_case m)
  [ intro.
    autobatch
    (*simplify.
    apply (witness ? ? (S O)). 
    simplify.
    reflexivity*)
  | intros.
    apply divides_b_true_to_divides
    [ apply (lt_O_smallest_factor ? H)
    | change with 
       (eqb ((S(S m1)) \mod (min_aux m1 (S(S m1)) 
       (\lambda m.(eqb ((S(S m1)) \mod m) O)))) O = true).
      apply f_min_aux_true.
      apply (ex_intro nat ? (S(S m1))).
      split
      [ autobatch
        (*split
        [ apply le_minus_m
        | apply le_n
        ]*)
      | autobatch
        (*rewrite > mod_n_n
        [ reflexivity
        | apply (trans_lt ? (S O))
          [ apply (le_n (S O))
          | unfold lt.
            apply le_S_S.
            apply le_S_S.
            apply le_O_n
          ]
        ]*)
      ]
    ]
  ]
]
qed.
  
theorem le_smallest_factor_n : 
\forall n:nat. smallest_factor n \le n.
intro.
apply (nat_case n)
[ autobatch
  (*simplify.
  apply le_n*)
| intro.
  autobatch
  (*apply (nat_case m)
  [ simplify.
    apply le_n
  | intro.
    apply divides_to_le
    [ unfold lt.
      apply le_S_S.
      apply le_O_n
    | apply divides_smallest_factor_n.
      unfold lt.
      apply le_S_S.
      apply le_O_n
    ]
  ]*)
]
qed.

theorem lt_smallest_factor_to_not_divides: \forall n,i:nat. 
(S O) < n \to (S O) < i \to i < (smallest_factor n) \to i \ndivides n.
intros 2.
apply (nat_case n)
[ intro.
  apply False_ind.
  apply (not_le_Sn_O (S O) H)
| intro.
  apply (nat_case m)
  [ intro.
    apply False_ind.
    apply (not_le_Sn_n (S O) H)
  | intros.
    apply divides_b_false_to_not_divides
    [ autobatch
      (*apply (trans_lt O (S O))
      [ apply (le_n (S O))
      | assumption
      ]*)
    | unfold divides_b.
      apply (lt_min_aux_to_false 
      (\lambda i:nat.eqb ((S(S m1)) \mod i) O) (S(S m1)) m1 i)
      [ cut ((S(S O)) = (S(S m1)-m1))
        [ rewrite < Hcut.
          exact H1
        | apply sym_eq.        
          apply plus_to_minus.
          autobatch
          (*rewrite < sym_plus.
          simplify.
          reflexivity*)
        ]
      | exact H2
      ]
    ]
  ]
]
qed.

theorem prime_smallest_factor_n : 
\forall n:nat. (S O) < n \to prime (smallest_factor n).
intro.
change with ((S(S O)) \le n \to (S O) < (smallest_factor n) \land 
(\forall m:nat. m \divides smallest_factor n \to (S O) < m \to  m = (smallest_factor n))).
intro.
split
[ apply lt_SO_smallest_factor.
  assumption
| intros.
  cut (le m (smallest_factor n))
  [ elim (le_to_or_lt_eq m (smallest_factor n) Hcut)
    [ absurd (m \divides n)
      [ apply (transitive_divides m (smallest_factor n))
        [ assumption
        | apply divides_smallest_factor_n.
          autobatch
          (*apply (trans_lt ? (S O))
          [ unfold lt. 
            apply le_n
          | exact H
          ]*)
        ]
      | apply lt_smallest_factor_to_not_divides;autobatch      
        (*[ exact H
        | assumption
        | assumption
        ]*)
      ]
    | assumption
    ]
  | apply divides_to_le
    [ apply (trans_lt O (S O))
      [ apply (le_n (S O))
      | apply lt_SO_smallest_factor.      
        exact H
      ]
    | assumption
    ]
  ]
]
qed.

theorem prime_to_smallest_factor: \forall n. prime n \to
smallest_factor n = n.
intro.
apply (nat_case n)
[ intro.
  autobatch
  (*apply False_ind.
  apply (not_prime_O H)*)
| intro.
  apply (nat_case m)
  [ intro.
    autobatch
    (*apply False_ind.
    apply (not_prime_SO H)*)
  | intro.
    change with 
     ((S O) < (S(S m1)) \land 
     (\forall m:nat. m \divides S(S m1) \to (S O) < m \to  m = (S(S m1))) \to 
    smallest_factor (S(S m1)) = (S(S m1))).
    intro.
    elim H.
    autobatch
    (*apply H2
    [ apply divides_smallest_factor_n.
      apply (trans_lt ? (S O))
      [ unfold lt. 
        apply le_n
      | assumption
      ]
    | apply lt_SO_smallest_factor.
      assumption
    ]*)
  ]
]
qed.

(* a number n > O is prime iff its smallest factor is n *)
definition primeb \def \lambda n:nat.
match n with
[ O \Rightarrow false
| (S p) \Rightarrow
  match p with
  [ O \Rightarrow false
  | (S q) \Rightarrow eqb (smallest_factor (S(S q))) (S(S q))]].

(* it works! 
theorem example4 : primeb (S(S(S O))) = true.
normalize.reflexivity.
qed.

theorem example5 : primeb (S(S(S(S(S(S O)))))) = false.
normalize.reflexivity.
qed.

theorem example6 : primeb (S(S(S(S((S(S(S(S(S(S(S O)))))))))))) = true.
normalize.reflexivity.
qed.

theorem example7 : primeb (S(S(S(S(S(S((S(S(S(S((S(S(S(S(S(S(S O))))))))))))))))))) = true.
normalize.reflexivity.
qed. *)

theorem primeb_to_Prop: \forall n.
match primeb n with
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)].
intro.
apply (nat_case n)
[ simplify.
  autobatch
  (*unfold Not.
  unfold prime.
  intro.
  elim H.
  apply (not_le_Sn_O (S O) H1)*)
| intro.
  apply (nat_case m)
  [ simplify.
    autobatch
    (*unfold Not.
    unfold prime.
    intro.
    elim H.
    apply (not_le_Sn_n (S O) H1)*)
  | intro.
    change with 
    match eqb (smallest_factor (S(S m1))) (S(S m1)) with
    [ true \Rightarrow prime (S(S m1))
    | false \Rightarrow \lnot (prime (S(S m1)))].
    apply (eqb_elim (smallest_factor (S(S m1))) (S(S m1)))
    [ intro.
      simplify.
      rewrite < H.
      apply prime_smallest_factor_n.
      unfold lt.autobatch
      (*apply le_S_S.
      apply le_S_S.
      apply le_O_n*)
    | intro.
      simplify.
      change with (prime (S(S m1)) \to False).
      intro.
      autobatch      
      (*apply H.
      apply prime_to_smallest_factor.
      assumption*)
    ]
  ]
]
qed.

theorem primeb_true_to_prime : \forall n:nat.
primeb n = true \to prime n.
intros.
change with
match true with 
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)].
rewrite < H.
(*qui autobatch non chiude il goal*)
apply primeb_to_Prop.
qed.

theorem primeb_false_to_not_prime : \forall n:nat.
primeb n = false \to \lnot (prime n).
intros.
change with
match false with 
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)].
rewrite < H.
(*qui autobatch non chiude il goal*)
apply primeb_to_Prop.
qed.

theorem decidable_prime : \forall n:nat.decidable (prime n).
intro.
unfold decidable.
cut 
(match primeb n with
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)] \to (prime n) \lor \lnot (prime n))
[ apply Hcut.
  (*qui autobatch non chiude il goal*)
  apply primeb_to_Prop
| elim (primeb n)
  [ left.
    (*qui autobatch non chiude il goal*)
    apply H
  | right.
    (*qui autobatch non chiude il goal*)
    apply H
  ]
]
qed.

theorem prime_to_primeb_true: \forall n:nat. 
prime n \to primeb n = true.
intros.
cut (match (primeb n) with
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)] \to ((primeb n) = true))
[ apply Hcut.
  (*qui autobatch non chiude il goal*)
  apply primeb_to_Prop
| elim (primeb n)
  [ reflexivity.
  | absurd (prime n)
    [ assumption
    | (*qui autobatch non chiude il goal*)
      assumption
    ]
  ]
]
qed.

theorem not_prime_to_primeb_false: \forall n:nat. 
\lnot(prime n) \to primeb n = false.
intros.
cut (match (primeb n) with
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)] \to ((primeb n) = false))
[ apply Hcut.
  (*qui autobatch non chiude il goal*)
  apply primeb_to_Prop
| elim (primeb n)
  [ absurd (prime n)
    [ (*qui autobatch non chiude il goal*)
      assumption
    | assumption
    ]
  | reflexivity
  ]
]
qed.

