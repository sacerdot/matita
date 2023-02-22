(**************************************************************************)
(*       ___	                                                          *)
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

include "datatypes/bool.ma".
include "datatypes/compare.ma".
include "nat/orders.ma".

let rec eqb n m \def 
match n with 
  [ O \Rightarrow 
     match m with 
     [ O \Rightarrow true
	   | (S q) \Rightarrow false] 
  | (S p) \Rightarrow
	   match m with 
     [ O \Rightarrow false
	   | (S q) \Rightarrow eqb p q]].
	   
theorem eqb_to_Prop: \forall n,m:nat. 
match (eqb n m) with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m].
intros.
apply (nat_elim2
(\lambda n,m:nat.match (eqb n m) with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m])).
intro.elim n1.
simplify.reflexivity.
simplify.apply not_eq_O_S.
intro.
simplify.unfold Not.
intro. apply (not_eq_O_S n1).apply sym_eq.assumption.
intros.simplify.
generalize in match H.
elim ((eqb n1 m1)).
simplify.apply eq_f.apply H1.
simplify.unfold Not.intro.apply H1.apply inj_S.assumption.
qed.

theorem eqb_elim : \forall n,m:nat.\forall P:bool \to Prop.
(n=m \to (P true)) \to (n \neq m \to (P false)) \to (P (eqb n m)). 
intros.
cut 
(match (eqb n m) with
[ true  \Rightarrow n = m
| false \Rightarrow n \neq m] \to (P (eqb n m))).
apply Hcut.apply eqb_to_Prop.
elim (eqb n m).
apply ((H H2)).
apply ((H1 H2)).
qed.

theorem eqb_n_n: \forall n. eqb n n = true.
intro.elim n.simplify.reflexivity.
simplify.assumption.
qed.

theorem eqb_true_to_eq: \forall n,m:nat.
eqb n m = true \to n = m.
intros.
change with 
match true with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m].
rewrite < H.
apply eqb_to_Prop. 
qed.

theorem eqb_false_to_not_eq: \forall n,m:nat.
eqb n m = false \to n \neq m.
intros.
change with 
match false with
[ true  \Rightarrow n = m 
| false \Rightarrow n \neq m].
rewrite < H.
apply eqb_to_Prop. 
qed.

theorem eq_to_eqb_true: \forall n,m:nat.
n = m \to eqb n m = true.
intros.apply (eqb_elim n m).
intros. reflexivity.
intros.apply False_ind.apply (H1 H).
qed.

theorem not_eq_to_eqb_false: \forall n,m:nat.
\lnot (n = m) \to eqb n m = false.
intros.apply (eqb_elim n m).
intros. apply False_ind.apply (H H1).
intros.reflexivity.
qed.

let rec leb n m \def 
match n with 
    [ O \Rightarrow true
    | (S p) \Rightarrow
	match m with 
        [ O \Rightarrow false
	| (S q) \Rightarrow leb p q]].

theorem leb_elim: \forall n,m:nat. \forall P:bool \to Prop. 
(n \leq m \to (P true)) \to (n \nleq m \to (P false)) \to
P (leb n m).
apply nat_elim2; intros; simplify
  [apply H.apply le_O_n
  |apply H1.apply not_le_Sn_O.
  |apply H;intros
    [apply H1.apply le_S_S.assumption.
    |apply H2.unfold Not.intros.apply H3.apply le_S_S_to_le.assumption
    ]
  ]
qed.

theorem leb_true_to_le:\forall n,m.
leb n m = true \to (n \le m).
intros 2.
apply leb_elim
  [intros.assumption
  |intros.destruct H1.
  ]
qed.

theorem leb_false_to_not_le:\forall n,m.
leb n m = false \to \lnot (n \le m).
intros 2.
apply leb_elim
  [intros.destruct H1
  |intros.assumption
  ]
qed.
(*
theorem decidable_le: \forall n,m. n \leq m \lor n \nleq m. 
intros.
apply (leb_elim n m)
  [intro.left.assumption
  |intro.right.assumption
  ]
qed.
*)

theorem le_to_leb_true: \forall n,m. n \leq m \to leb n m = true.
intros.apply leb_elim;intros
  [reflexivity
  |apply False_ind.apply H1.apply H.
  ]
qed.

theorem lt_to_leb_false: \forall n,m. m < n \to leb n m = false.
intros.apply leb_elim;intros
  [apply False_ind.apply (le_to_not_lt ? ? H1). assumption
  |reflexivity
  ]
qed.

theorem leb_to_Prop: \forall n,m:nat. 
match (leb n m) with
[ true  \Rightarrow n \leq m 
| false \Rightarrow n \nleq m].
apply nat_elim2;simplify
  [exact le_O_n
  |exact not_le_Sn_O
  |intros 2.simplify.
   elim ((leb n m));simplify
    [apply le_S_S.apply H
    |unfold Not.intros.apply H.apply le_S_S_to_le.assumption
    ]
  ]
qed.

(*
theorem leb_elim: \forall n,m:nat. \forall P:bool \to Prop. 
(n \leq m \to (P true)) \to (n \nleq m \to (P false)) \to
P (leb n m).
intros.
cut 
(match (leb n m) with
[ true  \Rightarrow n \leq m
| false \Rightarrow n \nleq m] \to (P (leb n m))).
apply Hcut.apply leb_to_Prop.
elim (leb n m).
apply ((H H2)).
apply ((H1 H2)).
qed.
*)

definition ltb ≝λn,m. leb n m ∧ notb (eqb n m).

theorem ltb_to_Prop :
 ∀n,m.
  match ltb n m with
  [ true ⇒ n < m
  | false ⇒ n ≮ m
  ].
intros;
unfold ltb;
apply leb_elim;
apply eqb_elim;
intros;
simplify;
[ rewrite < H;
  apply le_to_not_lt;
  constructor 1
| apply (not_eq_to_le_to_lt ? ? H H1)
| rewrite < H;
  apply le_to_not_lt;
  constructor 1
| apply le_to_not_lt;
  generalize in match (not_le_to_lt ? ? H1);
  clear H1;
  intro;
  apply lt_to_le;
  assumption
].
qed.

theorem ltb_elim: ∀n,m:nat. ∀P:bool → Prop.
(n < m → (P true)) → (n ≮ m → (P false)) →
P (ltb n m).
intros.
cut
(match (ltb n m) with
[ true  ⇒ n < m
| false ⇒ n ≮ m] → (P (ltb n m))).
apply Hcut.apply ltb_to_Prop.
elim (ltb n m).
apply ((H H2)).
apply ((H1 H2)).
qed.

let rec nat_compare n m: compare \def
match n with
[ O \Rightarrow 
    match m with 
      [ O \Rightarrow EQ
      | (S q) \Rightarrow LT ]
| (S p) \Rightarrow 
    match m with 
      [ O \Rightarrow GT
      | (S q) \Rightarrow nat_compare p q]].

theorem nat_compare_n_n: \forall n:nat. nat_compare n n = EQ.
intro.elim n.
simplify.reflexivity.
simplify.assumption.
qed.

theorem nat_compare_S_S: \forall n,m:nat. 
nat_compare n m = nat_compare (S n) (S m).
intros.simplify.reflexivity.
qed.

theorem nat_compare_pred_pred: 
\forall n,m:nat.lt O n \to lt O m \to 
eq compare (nat_compare n m) (nat_compare (pred n) (pred m)).
intros.
apply (lt_O_n_elim n H).
apply (lt_O_n_elim m H1).
intros.
simplify.reflexivity.
qed.

theorem nat_compare_to_Prop: \forall n,m:nat. 
match (nat_compare n m) with
  [ LT \Rightarrow n < m
  | EQ \Rightarrow n=m
  | GT \Rightarrow m < n ].
intros.
apply (nat_elim2 (\lambda n,m.match (nat_compare n m) with
  [ LT \Rightarrow n < m
  | EQ \Rightarrow n=m
  | GT \Rightarrow m < n ])).
intro.elim n1.simplify.reflexivity.
simplify.unfold lt.apply le_S_S.apply le_O_n.
intro.simplify.unfold lt.apply le_S_S. apply le_O_n.
intros 2.simplify.elim ((nat_compare n1 m1)).
simplify. unfold lt. apply le_S_S.apply H.
simplify. apply eq_f. apply H.
simplify. unfold lt.apply le_S_S.apply H.
qed.

theorem nat_compare_n_m_m_n: \forall n,m:nat. 
nat_compare n m = compare_invert (nat_compare m n).
intros. 
apply (nat_elim2 (\lambda n,m. nat_compare n m = compare_invert (nat_compare m n))).
intros.elim n1.simplify.reflexivity.
simplify.reflexivity.
intro.elim n1.simplify.reflexivity.
simplify.reflexivity.
intros.simplify.elim H.reflexivity.
qed.
     
theorem nat_compare_elim : \forall n,m:nat. \forall P:compare \to Prop.
(n < m \to P LT) \to (n=m \to P EQ) \to (m < n \to P GT) \to 
(P (nat_compare n m)).
intros.
cut (match (nat_compare n m) with
[ LT \Rightarrow n < m
| EQ \Rightarrow n=m
| GT \Rightarrow m < n] \to
(P (nat_compare n m))).
apply Hcut.apply nat_compare_to_Prop.
elim ((nat_compare n m)).
apply ((H H3)).
apply ((H1 H3)).
apply ((H2 H3)).
qed.

inductive cmp_cases (n,m:nat) : CProp ≝
  | cmp_le : n ≤ m → cmp_cases n m
  | cmp_gt : m < n → cmp_cases n m.

lemma cmp_nat: ∀n,m.cmp_cases n m.
intros; generalize in match (nat_compare_to_Prop n m);
cases (nat_compare n m); intros;
[constructor 1;apply lt_to_le|constructor 1;rewrite > H|constructor 2]
try assumption; apply le_n;
qed.
