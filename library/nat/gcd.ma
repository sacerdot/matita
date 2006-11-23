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

set "baseuri" "cic:/matita/nat/gcd".

include "nat/primes.ma".

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
(* apply (witness ? ? (n2 - n1*(m / n))). *)
apply witness[|
rewrite > distr_times_minus.
rewrite < H3 in \vdash (? ? ? (? % ?)).
rewrite < assoc_times.
rewrite < H4 in \vdash (? ? ? (? ? (? % ?))).
apply sym_eq.apply plus_to_minus.
rewrite > sym_times.
letin x \def div.
rewrite < (div_mod ? ? H).
reflexivity.
]
qed.

theorem divides_mod_to_divides: \forall p,m,n:nat. O < n \to
p \divides (m \mod n) \to p \divides n \to p \divides m. 
intros.elim H1.elim H2.
apply (witness p m ((n1*(m / n))+n2)).
rewrite > distr_times_plus.
rewrite < H3.
rewrite < assoc_times.
rewrite < H4.rewrite < sym_times.
apply div_mod.assumption.
qed.

theorem divides_gcd_aux_mn: \forall p,m,n. O < n \to n \le m \to n \le p \to
gcd_aux p m n \divides m \land gcd_aux p m n \divides n. 
intro.elim p.
absurd (O < n).assumption.apply le_to_not_lt.assumption.
cut ((n1 \divides m) \lor (n1 \ndivides m)).
simplify.
elim Hcut.rewrite > divides_to_divides_b_true.
simplify.
split.assumption.apply (witness n1 n1 (S O)).apply times_n_SO.
assumption.assumption.
rewrite > not_divides_to_divides_b_false.
simplify.
cut (gcd_aux n n1 (m \mod n1) \divides n1 \land
gcd_aux n n1 (m \mod n1) \divides mod m n1).
elim Hcut1.
split.apply (divides_mod_to_divides ? ? n1).
assumption.assumption.assumption.assumption.
apply H.
cut (O \lt m \mod n1 \lor O = mod m n1).
elim Hcut1.assumption.
apply False_ind.apply H4.apply mod_O_to_divides.
assumption.apply sym_eq.assumption.
apply le_to_or_lt_eq.apply le_O_n.
apply lt_to_le.
apply lt_mod_m_m.assumption.
apply le_S_S_to_le.
apply (trans_le ? n1).
change with (m \mod n1 < n1).
apply lt_mod_m_m.assumption.assumption.
assumption.assumption.
apply (decidable_divides n1 m).assumption.
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
apply (leb_elim n m).
apply (nat_case1 n).
simplify.intros.split.
apply (witness m m (S O)).apply times_n_SO.
apply (witness m O O).apply times_n_O.
intros.change with
(gcd_aux (S m1) m (S m1) \divides m
\land 
gcd_aux (S m1) m (S m1) \divides (S m1)).
apply divides_gcd_aux_mn.
unfold lt.apply le_S_S.apply le_O_n.
assumption.apply le_n.
simplify.intro.
apply (nat_case1 m).
simplify.intros.split.
apply (witness n O O).apply times_n_O.
apply (witness n n (S O)).apply times_n_SO.
intros.change with
(gcd_aux (S m1) n (S m1) \divides (S m1)
\land 
gcd_aux (S m1) n (S m1) \divides n).
cut (gcd_aux (S m1) n (S m1) \divides n
\land 
gcd_aux (S m1) n (S m1) \divides S m1).
elim Hcut.split.assumption.assumption.
apply divides_gcd_aux_mn.
unfold lt.apply le_S_S.apply le_O_n.
apply not_lt_to_le.unfold Not. unfold lt.intro.apply H.
rewrite > H1.apply (trans_le ? (S n)).
apply le_n_Sn.assumption.apply le_n.
qed.

theorem divides_gcd_n: \forall n,m. gcd n m \divides n.
intros. 
exact (proj2  ? ? (divides_gcd_nm n m)).
qed.

theorem divides_gcd_m: \forall n,m. gcd n m \divides m.
intros. 
exact (proj1 ? ? (divides_gcd_nm n m)).
qed.

theorem divides_gcd_aux: \forall p,m,n,d. O < n \to n \le m \to n \le p \to
d \divides m \to d \divides n \to d \divides gcd_aux p m n. 
intro.elim p.
absurd (O < n).assumption.apply le_to_not_lt.assumption.
simplify.
cut (n1 \divides m \lor n1 \ndivides m).
elim Hcut.
rewrite > divides_to_divides_b_true.
simplify.assumption.
assumption.assumption.
rewrite > not_divides_to_divides_b_false.
simplify.
apply H.
cut (O \lt m \mod n1 \lor O = m \mod n1).
elim Hcut1.assumption.
absurd (n1 \divides m).apply mod_O_to_divides.
assumption.apply sym_eq.assumption.assumption.
apply le_to_or_lt_eq.apply le_O_n.
apply lt_to_le.
apply lt_mod_m_m.assumption.
apply le_S_S_to_le.
apply (trans_le ? n1).
change with (m \mod n1 < n1).
apply lt_mod_m_m.assumption.assumption.
assumption.
apply divides_mod.assumption.assumption.assumption.
assumption.assumption.
apply (decidable_divides n1 m).assumption.
qed.

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
apply (leb_elim n m).
apply (nat_case1 n).simplify.intros.assumption.
intros.
change with (d \divides gcd_aux (S m1) m (S m1)).
apply divides_gcd_aux.
unfold lt.apply le_S_S.apply le_O_n.assumption.apply le_n.assumption.
rewrite < H2.assumption.
apply (nat_case1 m).simplify.intros.assumption.
intros.
change with (d \divides gcd_aux (S m1) n (S m1)).
apply divides_gcd_aux.
unfold lt.apply le_S_S.apply le_O_n.
apply lt_to_le.apply not_le_to_lt.assumption.apply le_n.assumption.
rewrite < H2.assumption.
qed.

theorem eq_minus_gcd_aux: \forall p,m,n.O < n \to n \le m \to n \le p \to
\exists a,b. a*n - b*m = gcd_aux p m n \lor b*m - a*n = gcd_aux p m n.
intro.
elim p.
absurd (O < n).assumption.apply le_to_not_lt.assumption.
cut (O < m).
cut (n1 \divides m \lor  n1 \ndivides m).
simplify.
elim Hcut1.
rewrite > divides_to_divides_b_true.
simplify.
apply (ex_intro ? ? (S O)).
apply (ex_intro ? ? O).
left.simplify.rewrite < plus_n_O.
apply sym_eq.apply minus_n_O.
assumption.assumption.
rewrite > not_divides_to_divides_b_false.
change with
(\exists a,b.
a*n1 - b*m = gcd_aux n n1 (m \mod n1)
\lor 
b*m - a*n1 = gcd_aux n n1 (m \mod n1)).
cut 
(\exists a,b.
a*(m \mod n1) - b*n1= gcd_aux n n1 (m \mod n1)
\lor
b*n1 - a*(m \mod n1) = gcd_aux n n1 (m \mod n1)).
elim Hcut2.elim H5.elim H6.
(* first case *)
rewrite < H7.
apply (ex_intro ? ? (a1+a*(m / n1))).
apply (ex_intro ? ? a).
right.
rewrite < sym_plus.
rewrite < (sym_times n1).
rewrite > distr_times_plus.
rewrite > (sym_times n1).
rewrite > (sym_times n1).
rewrite > (div_mod m n1) in \vdash (? ? (? % ?) ?).
rewrite > assoc_times.
rewrite < sym_plus.
rewrite > distr_times_plus.
rewrite < eq_minus_minus_minus_plus.
rewrite < sym_plus.
rewrite < plus_minus.
rewrite < minus_n_n.reflexivity.
apply le_n.
assumption.
(* second case *)
rewrite < H7.
apply (ex_intro ? ? (a1+a*(m / n1))).
apply (ex_intro ? ? a).
left.
(* clear Hcut2.clear H5.clear H6.clear H. *)
rewrite > sym_times.
rewrite > distr_times_plus.
rewrite > sym_times.
rewrite > (sym_times n1).
rewrite > (div_mod m n1) in \vdash (? ? (? ? %) ?).
rewrite > distr_times_plus.
rewrite > assoc_times.
rewrite < eq_minus_minus_minus_plus.
rewrite < sym_plus.
rewrite < plus_minus.
rewrite < minus_n_n.reflexivity.
apply le_n.
assumption.
apply (H n1 (m \mod n1)).
cut (O \lt m \mod n1 \lor O = m \mod n1).
elim Hcut2.assumption. 
absurd (n1 \divides m).apply mod_O_to_divides.
assumption.
symmetry.assumption.assumption.
apply le_to_or_lt_eq.apply le_O_n.
apply lt_to_le.
apply lt_mod_m_m.assumption.
apply le_S_S_to_le.
apply (trans_le ? n1).
change with (m \mod n1 < n1).
apply lt_mod_m_m.
assumption.assumption.assumption.assumption.
apply (decidable_divides n1 m).assumption.
apply (lt_to_le_to_lt ? n1).assumption.assumption.
qed.

theorem eq_minus_gcd:
 \forall m,n.\exists a,b.a*n - b*m = (gcd n m) \lor b*m - a*n = (gcd n m).
intros.
unfold gcd.
apply (leb_elim n m).
apply (nat_case1 n).
simplify.intros.
apply (ex_intro ? ? O).
apply (ex_intro ? ? (S O)).
right.simplify.
rewrite < plus_n_O.
apply sym_eq.apply minus_n_O.
intros.
change with 
(\exists a,b.
a*(S m1) - b*m = (gcd_aux (S m1) m (S m1)) 
\lor b*m - a*(S m1) = (gcd_aux (S m1) m (S m1))).
apply eq_minus_gcd_aux.
unfold lt. apply le_S_S.apply le_O_n.
assumption.apply le_n.
apply (nat_case1 m).
simplify.intros.
apply (ex_intro ? ? (S O)).
apply (ex_intro ? ? O).
left.simplify.
rewrite < plus_n_O.
apply sym_eq.apply minus_n_O.
intros.
change with 
(\exists a,b.
a*n - b*(S m1) = (gcd_aux (S m1) n (S m1)) 
\lor b*(S m1) - a*n = (gcd_aux (S m1) n (S m1))).
cut 
(\exists a,b.
a*(S m1) - b*n = (gcd_aux (S m1) n (S m1))
\lor
b*n - a*(S m1) = (gcd_aux (S m1) n (S m1))).
elim Hcut.elim H2.elim H3.
apply (ex_intro ? ? a1).
apply (ex_intro ? ? a).
right.assumption.
apply (ex_intro ? ? a1).
apply (ex_intro ? ? a).
left.assumption.
apply eq_minus_gcd_aux.
unfold lt. apply le_S_S.apply le_O_n.
apply lt_to_le.apply not_le_to_lt.assumption.
apply le_n.
qed.

(* some properties of gcd *)

theorem gcd_O_n: \forall n:nat. gcd O n = n.
intro.simplify.reflexivity.
qed.

theorem gcd_O_to_eq_O:\forall m,n:nat. (gcd m n) = O \to
m = O \land n = O.
intros.cut (O \divides n \land O \divides m).
elim Hcut.elim H2.split.
assumption.elim H1.assumption.
rewrite < H.
apply divides_gcd_nm.
qed.

theorem lt_O_gcd:\forall m,n:nat. O < n \to O < gcd m n.
intros.
apply (nat_case1 (gcd m n)).
intros.
generalize in match (gcd_O_to_eq_O m n H1).
intros.elim H2.
rewrite < H4 in \vdash (? ? %).assumption.
intros.unfold lt.apply le_S_S.apply le_O_n.
qed.

theorem symmetric_gcd: symmetric nat gcd.
(*CSC: bug here: unfold symmetric does not work *)
change with 
(\forall n,m:nat. gcd n m = gcd m n).
intros.
cut (O < (gcd n m) \lor O = (gcd n m)).
elim Hcut.
cut (O < (gcd m n) \lor O = (gcd m n)).
elim Hcut1.
apply antisym_le.
apply divides_to_le.assumption.
apply divides_d_gcd.apply divides_gcd_n.apply divides_gcd_m.
apply divides_to_le.assumption.
apply divides_d_gcd.apply divides_gcd_n.apply divides_gcd_m.
rewrite < H1.
cut (m=O \land n=O).
elim Hcut2.rewrite > H2.rewrite > H3.reflexivity.
apply gcd_O_to_eq_O.apply sym_eq.assumption.
apply le_to_or_lt_eq.apply le_O_n.
rewrite < H.
cut (n=O \land m=O).
elim Hcut1.rewrite > H1.rewrite > H2.reflexivity.
apply gcd_O_to_eq_O.apply sym_eq.assumption.
apply le_to_or_lt_eq.apply le_O_n.
qed.

variant sym_gcd: \forall n,m:nat. gcd n m = gcd m n \def
symmetric_gcd.

theorem le_gcd_times: \forall m,n,p:nat. O< p \to gcd m n \le gcd m (n*p).
intros.
apply (nat_case n).apply le_n.
intro.
apply divides_to_le.
apply lt_O_gcd.
rewrite > (times_n_O O).
apply lt_times.unfold lt.apply le_S_S.apply le_O_n.assumption.
apply divides_d_gcd.
apply (transitive_divides ? (S m1)).
apply divides_gcd_m.
apply (witness ? ? p).reflexivity.
apply divides_gcd_n.
qed.

theorem gcd_times_SO_to_gcd_SO: \forall m,n,p:nat. O < n \to O < p \to 
gcd m (n*p) = (S O) \to gcd m n = (S O).
intros.
apply antisymmetric_le.
rewrite < H2.
apply le_gcd_times.assumption.
change with (O < gcd m n). 
apply lt_O_gcd.assumption.
qed.

(* for the "converse" of the previous result see the end  of this development *)

theorem gcd_SO_n: \forall n:nat. gcd (S O) n = (S O).
intro.
apply antisym_le.apply divides_to_le.unfold lt.apply le_n.
apply divides_gcd_n.
cut (O < gcd (S O) n \lor O = gcd (S O) n).
elim Hcut.assumption.
apply False_ind.
apply (not_eq_O_S O).
cut ((S O)=O \land n=O).
elim Hcut1.apply sym_eq.assumption.
apply gcd_O_to_eq_O.apply sym_eq.assumption.
apply le_to_or_lt_eq.apply le_O_n.
qed.

theorem divides_gcd_mod: \forall m,n:nat. O < n \to
divides (gcd m n) (gcd n (m \mod n)).
intros.
apply divides_d_gcd.
apply divides_mod.assumption.
apply divides_gcd_n.
apply divides_gcd_m.
apply divides_gcd_m.
qed.

theorem divides_mod_gcd: \forall m,n:nat. O < n \to
divides (gcd n (m \mod n)) (gcd m n) .
intros.
apply divides_d_gcd.
apply divides_gcd_n.
apply (divides_mod_to_divides ? ? n).
assumption.
apply divides_gcd_m.
apply divides_gcd_n.
qed.

theorem gcd_mod: \forall m,n:nat. O < n \to
(gcd n (m \mod n)) = (gcd m n) .
intros.
apply antisymmetric_divides.
apply divides_mod_gcd.assumption.
apply divides_gcd_mod.assumption.
qed.

(* gcd and primes *)

theorem prime_to_gcd_SO: \forall n,m:nat. prime n \to n \ndivides m \to
gcd n m = (S O).
intros.unfold prime in H.
elim H.
apply antisym_le.
apply not_lt_to_le.unfold Not.unfold lt.
intro.
apply H1.rewrite < (H3 (gcd n m)).
apply divides_gcd_m.
apply divides_gcd_n.assumption.
cut (O < gcd n m \lor O = gcd n m).
elim Hcut.assumption.
apply False_ind.
apply (not_le_Sn_O (S O)).
cut (n=O \land m=O).
elim Hcut1.rewrite < H5 in \vdash (? ? %).assumption.
apply gcd_O_to_eq_O.apply sym_eq.assumption.
apply le_to_or_lt_eq.apply le_O_n.
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
          elim H1.rewrite > H6.
          (* applyS (witness n (n*(q*a-a1*n2)) (q*a-a1*n2))
             reflexivity. *);
          applyS (witness n ? ? (refl_eq ? ?)) timeout=50.
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
          elim H1.rewrite > H6.
          rewrite < sym_times.rewrite > assoc_times.
          rewrite < (assoc_times q).
          rewrite < (sym_times n).
          rewrite < distr_times_minus.
          apply (witness ? ? (n2*a1-q*a)).reflexivity
        ](* end second case *)
     |rewrite < (prime_to_gcd_SO n p)
       [apply eq_minus_gcd|assumption|assumption
       ]
     ]
   ]
 |apply (decidable_divides n p).
  apply (trans_lt ? (S O))
    [unfold lt.apply le_n
    |unfold prime in H.elim H. assumption
    ]
  ]
qed.

theorem eq_gcd_times_SO: \forall m,n,p:nat. O < n \to O < p \to
gcd m n = (S O) \to gcd m p = (S O) \to gcd m (n*p) = (S O).
intros.
apply antisymmetric_le.
apply not_lt_to_le.
unfold Not.intro.
cut (divides (smallest_factor (gcd m (n*p))) n \lor 
     divides (smallest_factor (gcd m (n*p))) p).
elim Hcut.
apply (not_le_Sn_n (S O)).
change with ((S O) < (S O)).
rewrite < H2 in \vdash (? ? %).
apply (lt_to_le_to_lt ? (smallest_factor (gcd m (n*p)))).
apply lt_SO_smallest_factor.assumption.
apply divides_to_le.
rewrite > H2.unfold lt.apply le_n.
apply divides_d_gcd.assumption.
apply (transitive_divides ? (gcd m (n*p))).
apply divides_smallest_factor_n.
apply (trans_lt ? (S O)). unfold lt. apply le_n. assumption.
apply divides_gcd_n.
apply (not_le_Sn_n (S O)).
change with ((S O) < (S O)).
rewrite < H3 in \vdash (? ? %).
apply (lt_to_le_to_lt ? (smallest_factor (gcd m (n*p)))).
apply lt_SO_smallest_factor.assumption.
apply divides_to_le.
rewrite > H3.unfold lt.apply le_n.
apply divides_d_gcd.assumption.
apply (transitive_divides ? (gcd m (n*p))).
apply divides_smallest_factor_n.
apply (trans_lt ? (S O)). unfold lt. apply le_n. assumption.
apply divides_gcd_n.
apply divides_times_to_divides.
apply prime_smallest_factor_n.
assumption.
apply (transitive_divides ? (gcd m (n*p))).
apply divides_smallest_factor_n.
apply (trans_lt ? (S O)).unfold lt. apply le_n. assumption.
apply divides_gcd_m.
change with (O < gcd m (n*p)).
apply lt_O_gcd.
rewrite > (times_n_O O).
apply lt_times.assumption.assumption.
qed.
