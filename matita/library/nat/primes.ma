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

include "nat/div_and_mod.ma".
include "nat/minimization.ma".
include "nat/sigma_and_pi.ma".
include "nat/factorial.ma".

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
intros.elim H1.rewrite > H2.
constructor 1.assumption.
apply (lt_O_n_elim n H).intros.
rewrite < plus_n_O.
rewrite > div_times.apply sym_times.
qed.

theorem div_mod_spec_to_divides :
\forall n,m,p. div_mod_spec m n p O \to n \divides m.
intros.elim H.
apply (witness n m p).
rewrite < sym_times.
rewrite > (plus_n_O (p*n)).assumption.
qed.

theorem divides_to_mod_O:
\forall n,m. O < n \to n \divides m \to (m \mod n) = O.
intros.apply (div_mod_spec_to_eq2 m n (m / n) (m \mod n) (m / n) O).
apply div_mod_spec_div_mod.assumption.
apply divides_to_div_mod_spec.assumption.assumption.
qed.

theorem mod_O_to_divides:
\forall n,m. O< n \to (m \mod n) = O \to  n \divides m.
intros.
apply (witness n m (m / n)).
rewrite > (plus_n_O (n * (m / n))).
rewrite < H1.
rewrite < sym_times.
(* Andrea: perche' hint non lo trova ?*)
apply div_mod.
assumption.
qed.

theorem divides_n_O: \forall n:nat. n \divides O.
intro. apply (witness n O O).apply times_n_O.
qed.

theorem divides_n_n: \forall n:nat. n \divides n.
intro. apply (witness n n (S O)).apply times_n_SO.
qed.

theorem divides_SO_n: \forall n:nat. (S O) \divides n.
intro. apply (witness (S O) n n). simplify.apply plus_n_O.
qed.

theorem divides_plus: \forall n,p,q:nat. 
n \divides p \to n \divides q \to n \divides p+q.
intros.
elim H.elim H1. apply (witness n (p+q) (n1+n2)).
rewrite > H2.rewrite > H3.apply sym_eq.apply distr_times_plus.
qed.

theorem divides_minus: \forall n,p,q:nat. 
divides n p \to divides n q \to divides n (p-q).
intros.
elim H.elim H1. apply (witness n (p-q) (n1-n2)).
rewrite > H2.rewrite > H3.apply sym_eq.apply distr_times_minus.
qed.

theorem divides_times: \forall n,m,p,q:nat. 
n \divides p \to m \divides q \to n*m \divides p*q.
intros.
elim H.elim H1. apply (witness (n*m) (p*q) (n1*n2)).
rewrite > H2.rewrite > H3.
apply (trans_eq nat ? (n*(m*(n1*n2)))).
apply (trans_eq nat ? (n*(n1*(m*n2)))).
apply assoc_times.
apply eq_f.
apply (trans_eq nat ? ((n1*m)*n2)).
apply sym_eq. apply assoc_times.
rewrite > (sym_times n1 m).apply assoc_times.
apply sym_eq. apply assoc_times.
qed.

theorem transitive_divides: transitive ? divides.
unfold.
intros.
elim H.elim H1. apply (witness x z (n1*n)).
rewrite > H3.rewrite > H2.
apply assoc_times.
qed.

variant trans_divides: \forall n,m,p. 
 n \divides m \to m \divides p \to n \divides p \def transitive_divides.

theorem eq_mod_to_divides:\forall n,m,p. O< p \to
mod n p = mod m p \to divides p (n-m).
intros.
cut (n \le m \or \not n \le m).
elim Hcut.
cut (n-m=O).
rewrite > Hcut1.
apply (witness p O O).
apply times_n_O.
apply eq_minus_n_m_O.
assumption.
apply (witness p (n-m) ((div n p)-(div m p))).
rewrite > distr_times_minus.
rewrite > sym_times.
rewrite > (sym_times p).
cut ((div n p)*p = n - (mod n p)).
rewrite > Hcut1.
rewrite > eq_minus_minus_minus_plus.
rewrite > sym_plus.
rewrite > H1.
rewrite < div_mod.reflexivity.
assumption.
apply sym_eq.
apply plus_to_minus.
rewrite > sym_plus.
apply div_mod.
assumption.
apply (decidable_le n m).
qed.

theorem antisymmetric_divides: antisymmetric nat divides.
unfold antisymmetric.intros.elim H. elim H1.
apply (nat_case1 n1).intro.
rewrite > H3.rewrite > H2.rewrite > H4.
rewrite < times_n_O.reflexivity.
intros.
apply (nat_case1 n).intro.
rewrite > H2.rewrite > H3.rewrite > H5.
rewrite < times_n_O.reflexivity.
intros.
apply antisymmetric_le.
rewrite > H2.rewrite > times_n_SO in \vdash (? % ?).
apply le_times_r.rewrite > H4.apply le_S_S.apply le_O_n.
rewrite > H3.rewrite > times_n_SO in \vdash (? % ?).
apply le_times_r.rewrite > H5.apply le_S_S.apply le_O_n.
qed.

(* divides le *)
theorem divides_to_le : \forall n,m. O < m \to n \divides m \to n \le m.
intros. elim H1.rewrite > H2.cut (O < n1).
apply (lt_O_n_elim n1 Hcut).intro.rewrite < sym_times.
simplify.rewrite < sym_plus.
apply le_plus_n.
elim (le_to_or_lt_eq O n1).
assumption.
absurd (O<m).assumption.
rewrite > H2.rewrite < H3.rewrite < times_n_O.
apply (not_le_Sn_n O).
apply le_O_n.
qed.

theorem divides_to_lt_O : \forall n,m. O < m \to n \divides m \to O < n.
intros.elim H1.
elim (le_to_or_lt_eq O n (le_O_n n)).
assumption.
rewrite < H3.absurd (O < m).assumption.
rewrite > H2.rewrite < H3.
simplify.exact (not_le_Sn_n O).
qed.

(*a variant of or_div_mod *)
theorem or_div_mod1: \forall n,q. O < q \to
(divides q (S n)) \land S n = (S (div n q)) * q \lor
(\lnot (divides q (S n)) \land S n= (div n q) * q + S (n\mod q)).
intros.elim (or_div_mod n q H);elim H1
  [left.split
    [apply (witness ? ? (S (n/q))).
     rewrite > sym_times.assumption
    |assumption
    ]
  |right.split
    [intro.
     apply (not_eq_O_S (n \mod q)).
     (* come faccio a fare unfold nelleipotesi ? *)
     cut ((S n) \mod q = O)
      [rewrite < Hcut.
       apply (div_mod_spec_to_eq2 (S n) q (div (S n) q) (mod (S n) q) (div n q) (S (mod n q)))
        [apply div_mod_spec_div_mod.
         assumption
        |apply div_mod_spec_intro;assumption
        ]
      |apply divides_to_mod_O;assumption
      ]
    |assumption
    ]
  ]
qed.

theorem divides_to_div: \forall n,m.divides n m \to m/n*n = m.
intro.
elim (le_to_or_lt_eq O n (le_O_n n))
  [rewrite > plus_n_O.
   rewrite < (divides_to_mod_O ? ? H H1).
   apply sym_eq.
   apply div_mod.
   assumption
  |elim H1.
   generalize in match H2.
   rewrite < H.
   simplify.
   intro.
   rewrite > H3.
   reflexivity
  ]
qed.

theorem divides_div: \forall d,n. divides d n \to divides (n/d) n.
intros.
apply (witness ? ? d).
apply sym_eq.
apply divides_to_div.
assumption.
qed.

theorem div_div: \forall n,d:nat. O < n \to divides d n \to 
n/(n/d) = d.
intros.
apply (inj_times_l1 (n/d))
  [apply (lt_times_n_to_lt d)
    [apply (divides_to_lt_O ? ? H H1).
    |rewrite > divides_to_div;assumption
    ]
  |rewrite > divides_to_div
    [rewrite > sym_times.
     rewrite > divides_to_div
      [reflexivity
      |assumption
      ]
    |apply (witness ? ? d).
     apply sym_eq.
     apply divides_to_div.
     assumption
    ]
  ]
qed.

theorem divides_to_eq_times_div_div_times: \forall a,b,c:nat.
O \lt b \to c \divides b \to a * (b /c) = (a*b)/c.
intros.
elim H1.
rewrite > H2.
rewrite > (sym_times c n1).
cut(O \lt c)
[ rewrite > (lt_O_to_div_times n1 c)
  [ rewrite < assoc_times.
    rewrite > (lt_O_to_div_times (a *n1) c)
    [ reflexivity
    | assumption
    ]
  | assumption
  ]  
| apply (divides_to_lt_O c b);
    assumption.
]
qed.

theorem eq_div_plus: \forall n,m,d. O < d \to
divides d n \to divides d m \to
(n + m ) / d = n/d + m/d.
intros.
elim H1.
elim H2.
rewrite > H3.rewrite > H4.
rewrite < distr_times_plus.
rewrite > sym_times.
rewrite > sym_times in ⊢ (? ? ? (? (? % ?) ?)).
rewrite > sym_times in ⊢ (? ? ? (? ? (? % ?))).
rewrite > lt_O_to_div_times
  [rewrite > lt_O_to_div_times
    [rewrite > lt_O_to_div_times
      [reflexivity
      |assumption
      ]
    |assumption
    ]
  |assumption
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
intros.unfold divides_b.
apply eqb_elim.
intro.simplify.apply mod_O_to_divides.assumption.assumption.
intro.simplify.unfold Not.intro.apply H1.apply divides_to_mod_O.assumption.assumption.
qed.

theorem divides_b_true_to_divides1:
\forall n,m:nat. O < n \to
(divides_b n m = true ) \to n \divides m.
intros.
change with 
match true with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m].
rewrite < H1.apply divides_b_to_Prop.
assumption.
qed.

theorem divides_b_true_to_divides:
\forall n,m:nat. divides_b n m = true \to n \divides m.
intros 2.apply (nat_case n)
  [apply (nat_case m)
    [intro.apply divides_n_n
    |simplify.intros.apply False_ind.
     apply not_eq_true_false.apply sym_eq.
     assumption
    ]
  |intros.
   apply divides_b_true_to_divides1
    [apply lt_O_S|assumption]
  ]
qed.

theorem divides_b_false_to_not_divides1:
\forall n,m:nat. O < n \to
(divides_b n m = false ) \to n \ndivides m.
intros.
change with 
match false with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m].
rewrite < H1.apply divides_b_to_Prop.
assumption.
qed.

theorem divides_b_false_to_not_divides:
\forall n,m:nat. divides_b n m = false \to n \ndivides m.
intros 2.apply (nat_case n)
  [apply (nat_case m)
    [simplify.unfold Not.intros.
     apply not_eq_true_false.assumption
    |unfold Not.intros.elim H1.
     apply (not_eq_O_S m1).apply sym_eq.
     assumption
    ]
  |intros.
   apply divides_b_false_to_not_divides1
    [apply lt_O_S|assumption]
  ]
qed.

theorem decidable_divides: \forall n,m:nat.O < n \to
decidable (n \divides m).
intros.unfold decidable.
cut 
(match divides_b n m with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m] \to n \divides m \lor n \ndivides m).
apply Hcut.apply divides_b_to_Prop.assumption.
elim (divides_b n m).left.apply H1.right.apply H1.
qed.

theorem divides_to_divides_b_true : \forall n,m:nat. O < n \to
n \divides m \to divides_b n m = true.
intros.
cut (match (divides_b n m) with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m] \to ((divides_b n m) = true)).
apply Hcut.apply divides_b_to_Prop.assumption.
elim (divides_b n m).reflexivity.
absurd (n \divides m).assumption.assumption.
qed.

theorem divides_to_divides_b_true1 : \forall n,m:nat.
O < m \to n \divides m \to divides_b n m = true.
intro.
elim (le_to_or_lt_eq O n (le_O_n n))
  [apply divides_to_divides_b_true
    [assumption|assumption]
  |apply False_ind.
   rewrite < H in H2.
   elim H2.
   simplify in H3.
   apply (not_le_Sn_O O).
   rewrite > H3 in H1.
   assumption
  ]
qed.

theorem not_divides_to_divides_b_false: \forall n,m:nat. O < n \to
\lnot(n \divides m) \to (divides_b n m) = false.
intros.
cut (match (divides_b n m) with
[ true \Rightarrow n \divides m
| false \Rightarrow n \ndivides m] \to ((divides_b n m) = false)).
apply Hcut.apply divides_b_to_Prop.assumption.
elim (divides_b n m).
absurd (n \divides m).assumption.assumption.
reflexivity.
qed.

theorem divides_b_div_true: 
\forall d,n. O < n \to 
  divides_b d n = true \to divides_b (n/d) n = true.
intros.
apply divides_to_divides_b_true1
  [assumption
  |apply divides_div.
   apply divides_b_true_to_divides.
   assumption
  ]
qed.

theorem divides_b_true_to_lt_O: \forall n,m. O < n \to divides_b m n = true \to O < m.
intros.
elim (le_to_or_lt_eq ? ? (le_O_n m))
  [assumption
  |apply False_ind.
   elim H1.
   rewrite < H2 in H1.
   simplify in H1.
   apply (lt_to_not_eq O n H).
   apply sym_eq.
   apply eqb_true_to_eq.
   assumption
  ]
qed.

(* divides and pi *)
theorem divides_f_pi_f : \forall f:nat \to nat.\forall n,m,i:nat. 
m \le i \to i \le n+m \to f i \divides pi n f m.
intros 5.elim n.simplify.
cut (i = m).rewrite < Hcut.apply divides_n_n.
apply antisymmetric_le.assumption.assumption.
simplify.
cut (i < S n1+m \lor i = S n1 + m).
elim Hcut.
apply (transitive_divides ? (pi n1 f m)).
apply H1.apply le_S_S_to_le. assumption.
apply (witness ? ? (f (S n1+m))).apply sym_times.
rewrite > H3.
apply (witness ? ? (pi n1 f m)).reflexivity.
apply le_to_or_lt_eq.assumption.
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
intros 3.elim n.absurd (O<i).assumption.apply (le_n_O_elim i H1).
apply (not_le_Sn_O O).
change with (i \divides (S n1)*n1!).
apply (le_n_Sm_elim i n1 H2).
intro.
apply (transitive_divides ? n1!).
apply H1.apply le_S_S_to_le. assumption.
apply (witness ? ? (S n1)).apply sym_times.
intro.
rewrite > H3.
apply (witness ? ? n1!).reflexivity.
qed.

theorem mod_S_fact: \forall n,i:nat. 
(S O) < i \to i \le n \to (S n!) \mod i = (S O).
intros.cut (n! \mod i = O).
rewrite < Hcut.
apply mod_S.apply (trans_lt O (S O)).apply (le_n (S O)).assumption.
rewrite > Hcut.assumption.
apply divides_to_mod_O.apply (trans_lt O (S O)).apply (le_n (S O)).assumption.
apply divides_fact.apply (trans_lt O (S O)).apply (le_n (S O)).assumption.
assumption.
qed.

theorem not_divides_S_fact: \forall n,i:nat. 
(S O) < i \to i \le n \to i \ndivides S n!.
intros.
apply divides_b_false_to_not_divides.
unfold divides_b.
rewrite > mod_S_fact[simplify.reflexivity|assumption|assumption].
qed.

(* prime *)
definition prime : nat \to  Prop \def
\lambda n:nat. (S O) < n \land 
(\forall m:nat. m \divides n \to (S O) < m \to  m = n).

theorem not_prime_O: \lnot (prime O).
unfold Not.unfold prime.intro.elim H.apply (not_le_Sn_O (S O) H1).
qed.

theorem not_prime_SO: \lnot (prime (S O)).
unfold Not.unfold prime.intro.elim H.apply (not_le_Sn_n (S O) H1).
qed.

theorem prime_to_lt_O: \forall p. prime p \to O < p.
intros.elim H.apply lt_to_le.assumption.
qed.

theorem prime_to_lt_SO: \forall p. prime p \to S O < p.
intros.elim H.
assumption.
qed.

(* smallest factor *)
definition smallest_factor : nat \to nat \def
\lambda n:nat. 
match n with
[ O \Rightarrow O
| (S p) \Rightarrow 
  match p with
  [ O \Rightarrow (S O)
  | (S q) \Rightarrow min_aux q (S (S O)) (\lambda m.(eqb ((S(S q)) \mod m) O))]].

(* it works !
theorem example1 : smallest_factor (S(S(S O))) = (S(S(S O))).
normalize.reflexivity.
qed.

theorem example2: smallest_factor (S(S(S(S O)))) = (S(S O)).
normalize.reflexivity.
qed.

theorem example3 : smallest_factor (S(S(S(S(S(S(S O))))))) = (S(S(S(S(S(S(S O))))))).
simplify.reflexivity.
qed. *)

theorem lt_SO_smallest_factor: 
\forall n:nat. (S O) < n \to (S O) < (smallest_factor n).
intro.
apply (nat_case n).intro.apply False_ind.apply (not_le_Sn_O (S O) H).
intro.apply (nat_case m).intro. apply False_ind.apply (not_le_Sn_n (S O) H).
intros.
change with 
(S O < min_aux m1 (S (S O)) (\lambda m.(eqb ((S(S m1)) \mod m) O))).
apply (lt_to_le_to_lt ? (S (S O))).
apply (le_n (S(S O))).
cut ((S(S O)) = (S(S m1)) - m1).
rewrite > Hcut.
apply le_min_aux.
apply sym_eq.apply plus_to_minus.
rewrite < sym_plus.simplify.reflexivity.
qed.

theorem lt_O_smallest_factor: \forall n:nat. O < n \to O < (smallest_factor n).
intro.
apply (nat_case n).intro.apply False_ind.apply (not_le_Sn_n O H).
intro.apply (nat_case m).intro.
simplify.unfold lt.apply le_n.
intros.apply (trans_lt ? (S O)).
unfold lt.apply le_n.
apply lt_SO_smallest_factor.unfold lt. apply le_S_S.
apply le_S_S.apply le_O_n.
qed.

theorem divides_smallest_factor_n : 
\forall n:nat. O < n \to smallest_factor n \divides n.
intro.
apply (nat_case n).intro.apply False_ind.apply (not_le_Sn_O O H).
intro.apply (nat_case m).intro. simplify.
apply (witness ? ? (S O)). simplify.reflexivity.
intros.
apply divides_b_true_to_divides.
change with 
(eqb ((S(S m1)) \mod (min_aux m1 (S (S O)) 
  (\lambda m.(eqb ((S(S m1)) \mod m) O)))) O = true).
apply f_min_aux_true.
apply (ex_intro nat ? (S(S m1))).
split.split.
apply (le_S_S_to_le (S (S O)) (S (S m1)) ?).
apply (minus_le_O_to_le (S (S (S O))) (S (S (S m1))) ?).
apply (le_n O).
rewrite < sym_plus. simplify. apply le_n.
apply (eq_to_eqb_true (mod (S (S m1)) (S (S m1))) O ?).
apply (mod_n_n (S (S m1)) ?).
apply (H).
qed.
  
theorem le_smallest_factor_n : 
\forall n:nat. smallest_factor n \le n.
intro.apply (nat_case n).simplify.apply le_n.
intro.apply (nat_case m).simplify.apply le_n.
intro.apply divides_to_le.
unfold lt.apply le_S_S.apply le_O_n.
apply divides_smallest_factor_n.
unfold lt.apply le_S_S.apply le_O_n.
qed.

theorem lt_smallest_factor_to_not_divides: \forall n,i:nat. 
(S O) < n \to (S O) < i \to i < (smallest_factor n) \to i \ndivides n.
intros 2.
apply (nat_case n).intro.apply False_ind.apply (not_le_Sn_O (S O) H).
intro.apply (nat_case m).intro. apply False_ind.apply (not_le_Sn_n (S O) H).
intros.
apply divides_b_false_to_not_divides.
apply (lt_min_aux_to_false 
(\lambda i:nat.eqb ((S(S m1)) \mod i) O) (S (S O)) m1 i).
assumption.
assumption.
qed.

theorem prime_smallest_factor_n : 
\forall n:nat. (S O) < n \to prime (smallest_factor n).
intro.change with ((S(S O)) \le n \to (S O) < (smallest_factor n) \land 
(\forall m:nat. m \divides smallest_factor n \to (S O) < m \to  m = (smallest_factor n))).
intro.split.
apply lt_SO_smallest_factor.assumption.
intros.
cut (le m (smallest_factor n)).
elim (le_to_or_lt_eq m (smallest_factor n) Hcut).
absurd (m \divides n).
apply (transitive_divides m (smallest_factor n)).
assumption.
apply divides_smallest_factor_n.
apply (trans_lt ? (S O)). unfold lt. apply le_n. exact H.
apply lt_smallest_factor_to_not_divides.
exact H.assumption.assumption.assumption.
apply divides_to_le.
apply (trans_lt O (S O)).
apply (le_n (S O)).
apply lt_SO_smallest_factor.
exact H.
assumption.
qed.

theorem prime_to_smallest_factor: \forall n. prime n \to
smallest_factor n = n.
intro.apply (nat_case n).intro.apply False_ind.apply (not_prime_O H).
intro.apply (nat_case m).intro.apply False_ind.apply (not_prime_SO H).
intro.
change with 
((S O) < (S(S m1)) \land 
(\forall m:nat. m \divides S(S m1) \to (S O) < m \to  m = (S(S m1))) \to 
smallest_factor (S(S m1)) = (S(S m1))).
intro.elim H.apply H2.
apply divides_smallest_factor_n.
apply (trans_lt ? (S O)).unfold lt. apply le_n.assumption.
apply lt_SO_smallest_factor.
assumption.
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
apply (nat_case n).simplify.unfold Not.unfold prime.intro.elim H.apply (not_le_Sn_O (S O) H1).
intro.apply (nat_case m).simplify.unfold Not.unfold prime.intro.elim H.apply (not_le_Sn_n (S O) H1).
intro.
change with 
match eqb (smallest_factor (S(S m1))) (S(S m1)) with
[ true \Rightarrow prime (S(S m1))
| false \Rightarrow \lnot (prime (S(S m1)))].
apply (eqb_elim (smallest_factor (S(S m1))) (S(S m1))).
intro.simplify.
rewrite < H.
apply prime_smallest_factor_n.
unfold lt.apply le_S_S.apply le_S_S.apply le_O_n.
intro.simplify.
change with (prime (S(S m1)) \to False).
intro.apply H.
apply prime_to_smallest_factor.
assumption.
qed.

theorem primeb_true_to_prime : \forall n:nat.
primeb n = true \to prime n.
intros.change with
match true with 
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)].
rewrite < H.
apply primeb_to_Prop.
qed.

theorem primeb_false_to_not_prime : \forall n:nat.
primeb n = false \to \lnot (prime n).
intros.change with
match false with 
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)].
rewrite < H.
apply primeb_to_Prop.
qed.

theorem decidable_prime : \forall n:nat.decidable (prime n).
intro.unfold decidable.
cut 
(match primeb n with
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)] \to (prime n) \lor \lnot (prime n)).
apply Hcut.apply primeb_to_Prop.
elim (primeb n).left.apply H.right.apply H.
qed.

theorem prime_to_primeb_true: \forall n:nat. 
prime n \to primeb n = true.
intros.
cut (match (primeb n) with
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)] \to ((primeb n) = true)).
apply Hcut.apply primeb_to_Prop.
elim (primeb n).reflexivity.
absurd (prime n).assumption.assumption.
qed.

theorem not_prime_to_primeb_false: \forall n:nat. 
\lnot(prime n) \to primeb n = false.
intros.
cut (match (primeb n) with
[ true \Rightarrow prime n
| false \Rightarrow \lnot (prime n)] \to ((primeb n) = false)).
apply Hcut.apply primeb_to_Prop.
elim (primeb n).
absurd (prime n).assumption.assumption.
reflexivity.
qed.

