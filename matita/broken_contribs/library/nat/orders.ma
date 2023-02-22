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

include "nat/nat.ma".
include "higher_order_defs/ordering.ma".

(* definitions *)
inductive le (n:nat) : nat \to Prop \def
  | le_n : le n n
  | le_S : \forall m:nat. le n m \to le n (S m).

interpretation "natural 'less or equal to'" 'leq x y = (le x y).

interpretation "natural 'neither less nor equal to'" 'nleq x y = (Not (le x y)).

definition lt: nat \to nat \to Prop \def
\lambda n,m:nat.(S n) \leq m.

interpretation "natural 'less than'" 'lt x y = (lt x y).

interpretation "natural 'not less than'" 'nless x y = (Not (lt x y)).

definition ge: nat \to nat \to Prop \def
\lambda n,m:nat.m \leq n.

interpretation "natural 'greater or equal to'" 'geq x y = (ge x y).

definition gt: nat \to nat \to Prop \def
\lambda n,m:nat.m<n.

interpretation "natural 'greater than'" 'gt x y = (gt x y).

interpretation "natural 'not greater than'" 'ngtr x y = (Not (gt x y)).

theorem transitive_le : transitive nat le.
unfold transitive.intros.elim H1.
assumption.
apply le_S.assumption.
qed.

theorem trans_le: \forall n,m,p:nat. n \leq m \to m \leq p \to n \leq p
\def transitive_le.

theorem transitive_lt: transitive nat lt.
unfold transitive.unfold lt.intros.elim H1.
apply le_S. assumption.
apply le_S.assumption.
qed.

theorem trans_lt: \forall n,m,p:nat. lt n m \to lt m p \to lt n p
\def transitive_lt.

theorem le_S_S: \forall n,m:nat. n \leq m \to S n \leq S m.
intros.elim H.
apply le_n.
apply le_S.assumption.
qed.

theorem le_O_n : \forall n:nat. O \leq n.
intros.elim n.
apply le_n.apply 
le_S. assumption.
qed.

theorem le_n_Sn : \forall n:nat. n \leq S n.
intros. apply le_S.apply le_n.
qed.

theorem le_pred_n : \forall n:nat. pred n \leq n.
intros.elim n.
simplify.apply le_n.
simplify.apply le_n_Sn.
qed.

theorem le_S_S_to_le : \forall n,m:nat. S n \leq S m \to n \leq m.
intros.change with (pred (S n) \leq pred (S m)).
elim H.apply le_n.apply (trans_le ? (pred n1)).assumption.
apply le_pred_n.
qed.

theorem lt_S_S_to_lt: \forall n,m. 
  S n < S m \to n < m.
intros. apply le_S_S_to_le. assumption.
qed.

theorem lt_to_lt_S_S: ∀n,m. n < m → S n < S m.
intros;
unfold lt in H;
apply (le_S_S ? ? H).
qed.

theorem leS_to_not_zero : \forall n,m:nat. S n \leq m \to not_zero m.
intros.elim H.exact I.exact I.
qed.

(* not le *)
theorem not_le_Sn_O: \forall n:nat. S n \nleq O.
intros.unfold Not.simplify.intros.apply (leS_to_not_zero ? ? H).
qed.

theorem not_le_Sn_n: \forall n:nat. S n \nleq n.
intros.elim n.apply not_le_Sn_O.unfold Not.simplify.intros.cut (S n1 \leq n1).
apply H.assumption.
apply le_S_S_to_le.assumption.
qed.

theorem lt_pred: \forall n,m. 
  O < n \to n < m \to pred n < pred m. 
apply nat_elim2
  [intros.apply False_ind.apply (not_le_Sn_O ? H)
  |intros.apply False_ind.apply (not_le_Sn_O ? H1)
  |intros.simplify.unfold.apply le_S_S_to_le.assumption
  ]
qed.

theorem S_pred: \forall n:nat.lt O n \to eq nat n (S (pred n)).
intro.elim n.apply False_ind.exact (not_le_Sn_O O H).
apply eq_f.apply pred_Sn.
qed.

theorem le_pred_to_le:
 ∀n,m. O < m → pred n ≤ pred m → n ≤ m.
intros 2;
elim n;
[ apply le_O_n
| simplify in H2;
  rewrite > (S_pred m);
  [ apply le_S_S;
    assumption
  | assumption
  ]
].
qed.

theorem le_to_le_pred:
 ∀n,m. n ≤ m → pred n ≤ pred m.
intros 2;
elim n;
[ simplify;
  apply le_O_n
| simplify;
  elim m in H1 ⊢ %;
  [ elim (not_le_Sn_O ? H1)
  | simplify;
    apply le_S_S_to_le;
    assumption
  ]
].
qed.

(* le to lt or eq *)
theorem le_to_or_lt_eq : \forall n,m:nat. 
n \leq m \to n < m \lor n = m.
intros.elim H.
right.reflexivity.
left.unfold lt.apply le_S_S.assumption.
qed.

theorem Not_lt_n_n: ∀n. n ≮ n.
intro;
unfold Not;
intro;
unfold lt in H;
apply (not_le_Sn_n ? H).
qed.

(* not eq *)
theorem lt_to_not_eq : \forall n,m:nat. n<m \to n \neq m.
unfold Not.intros.cut ((le (S n) m) \to False).
apply Hcut.assumption.rewrite < H1.
apply not_le_Sn_n.
qed.

(*not lt*)
theorem eq_to_not_lt: \forall a,b:nat.
a = b \to a \nlt b.
intros.
unfold Not.
intros.
rewrite > H in H1.
apply (lt_to_not_eq b b)
[ assumption
| reflexivity
]
qed.

theorem lt_n_m_to_not_lt_m_Sn: ∀n,m. n < m → m ≮ S n.
intros;
unfold Not;
intro;
unfold lt in H;
unfold lt in H1;
generalize in match (le_S_S ? ? H);
intro;
generalize in match (transitive_le ? ? ? H2 H1);
intro;
apply (not_le_Sn_n ? H3).
qed.

(* le vs. lt *)
theorem lt_to_le : \forall n,m:nat. n<m \to n \leq m.
simplify.intros.unfold lt in H.elim H.
apply le_S. apply le_n.
apply le_S. assumption.
qed.

theorem lt_S_to_le : \forall n,m:nat. n < S m \to n \leq m.
simplify.intros.
apply le_S_S_to_le.assumption.
qed.

theorem not_le_to_lt: \forall n,m:nat. n \nleq m \to m<n.
intros 2.
apply (nat_elim2 (\lambda n,m.n \nleq m \to m<n)).
intros.apply (absurd (O \leq n1)).apply le_O_n.assumption.
unfold Not.unfold lt.intros.apply le_S_S.apply le_O_n.
unfold Not.unfold lt.intros.apply le_S_S.apply H.intros.apply H1.apply le_S_S.
assumption.
qed.

theorem lt_to_not_le: \forall n,m:nat. n<m \to m \nleq n.
unfold Not.unfold lt.intros 3.elim H.
apply (not_le_Sn_n n H1).
apply H2.apply lt_to_le. apply H3.
qed.

theorem not_lt_to_le: \forall n,m:nat. Not (lt n m) \to le m n.
simplify.intros.
apply lt_S_to_le.
apply not_le_to_lt.exact H.
qed.

theorem le_to_not_lt: \forall n,m:nat. le n m \to Not (lt m n).
intros.unfold Not.unfold lt.
apply lt_to_not_le.unfold lt.
apply le_S_S.assumption.
qed.

theorem not_eq_to_le_to_lt: ∀n,m. n≠m → n≤m → n<m.
intros;
elim (le_to_or_lt_eq ? ? H1);
[ assumption
| elim (H H2)
].
qed.

(* le elimination *)
theorem le_n_O_to_eq : \forall n:nat. n \leq O \to O=n.
intro.elim n.reflexivity.
apply False_ind.
apply not_le_Sn_O;
[2: apply H1 | skip].
qed.

theorem le_n_O_elim: \forall n:nat.n \leq O \to \forall P: nat \to Prop.
P O \to P n.
intro.elim n.
assumption.
apply False_ind.
apply  (not_le_Sn_O ? H1).
qed.

theorem le_n_Sm_elim : \forall n,m:nat.n \leq S m \to 
\forall P:Prop. (S n \leq S m \to P) \to (n=S m \to P) \to P.
intros 4.elim H.
apply H2.reflexivity.
apply H3. apply le_S_S. assumption.
qed.

(* le and eq *)
lemma le_to_le_to_eq: \forall n,m. n \le m \to m \le n \to n = m.
apply nat_elim2
  [intros.apply le_n_O_to_eq.assumption
  |intros.apply sym_eq.apply le_n_O_to_eq.assumption
  |intros.apply eq_f.apply H
    [apply le_S_S_to_le.assumption
    |apply le_S_S_to_le.assumption
    ]
  ]
qed.

(* lt and le trans *)
theorem lt_O_S : \forall n:nat. O < S n.
intro. unfold. apply le_S_S. apply le_O_n.
qed.

theorem lt_to_le_to_lt: \forall n,m,p:nat. lt n m \to le m p \to lt n p.
intros.elim H1.
assumption.unfold lt.apply le_S.assumption.
qed.

theorem le_to_lt_to_lt: \forall n,m,p:nat. le n m \to lt m p \to lt n p.
intros 4.elim H.
assumption.apply H2.unfold lt.
apply lt_to_le.assumption.
qed.

theorem lt_S_to_lt: \forall n,m. S n < m \to n < m.
intros.
apply (trans_lt ? (S n))
  [apply le_n|assumption]
qed.

theorem ltn_to_ltO: \forall n,m:nat. lt n m \to lt O m.
intros.apply (le_to_lt_to_lt O n).
apply le_O_n.assumption.
qed.

theorem lt_SO_n_to_lt_O_pred_n: \forall n:nat.
(S O) \lt n \to O \lt (pred n).
intros.
apply (ltn_to_ltO (pred (S O)) (pred n) ?).
 apply (lt_pred (S O) n);
 [ apply (lt_O_S O) 
 | assumption
 ]
qed.

theorem lt_O_n_elim: \forall n:nat. lt O n \to 
\forall P:nat\to Prop. (\forall m:nat.P (S m)) \to P n.
intro.elim n.apply False_ind.exact (not_le_Sn_O O H).
apply H2.
qed.

(* other abstract properties *)
theorem antisymmetric_le : antisymmetric nat le.
unfold antisymmetric.intros 2.
apply (nat_elim2 (\lambda n,m.(n \leq m \to m \leq n \to n=m))).
intros.apply le_n_O_to_eq.assumption.
intros.apply False_ind.apply (not_le_Sn_O ? H).
intros.apply eq_f.apply H.
apply le_S_S_to_le.assumption.
apply le_S_S_to_le.assumption.
qed.

theorem antisym_le: \forall n,m:nat. n \leq m \to m \leq n \to n=m
\def antisymmetric_le.

theorem le_n_m_to_lt_m_Sn_to_eq_n_m: ∀n,m. n ≤ m → m < S n → n=m.
intros;
unfold lt in H1;
generalize in match (le_S_S_to_le ? ? H1);
intro;
apply antisym_le;
assumption.
qed.

theorem decidable_le: \forall n,m:nat. decidable (n \leq m).
intros.
apply (nat_elim2 (\lambda n,m.decidable (n \leq m))).
intros.unfold decidable.left.apply le_O_n.
intros.unfold decidable.right.exact (not_le_Sn_O n1).
intros 2.unfold decidable.intro.elim H.
left.apply le_S_S.assumption.
right.unfold Not.intro.apply H1.apply le_S_S_to_le.assumption.
qed.

theorem decidable_lt: \forall n,m:nat. decidable (n < m).
intros.exact (decidable_le (S n) m).
qed.

(* well founded induction principles *)

theorem nat_elim1 : \forall n:nat.\forall P:nat \to Prop. 
(\forall m.(\forall p. (p \lt m) \to P p) \to P m) \to P n.
intros.cut (\forall q:nat. q \le n \to P q).
apply (Hcut n).apply le_n.
elim n.apply (le_n_O_elim q H1).
apply H.
intros.apply False_ind.apply (not_le_Sn_O p H2).
apply H.intros.apply H1.
cut (p < S n1).
apply lt_S_to_le.assumption.
apply (lt_to_le_to_lt p q (S n1) H3 H2).
qed.

(* some properties of functions *)

definition increasing \def \lambda f:nat \to nat. 
\forall n:nat. f n < f (S n).

theorem increasing_to_monotonic: \forall f:nat \to nat.
increasing f \to monotonic nat lt f.
unfold monotonic.unfold lt.unfold increasing.unfold lt.intros.elim H1.apply H.
apply (trans_le ? (f n1)).
assumption.apply (trans_le ? (S (f n1))).
apply le_n_Sn.
apply H.
qed.

theorem le_n_fn: \forall f:nat \to nat. (increasing f) 
\to \forall n:nat. n \le (f n).
intros.elim n.
apply le_O_n.
apply (trans_le ? (S (f n1))).
apply le_S_S.apply H1.
simplify in H. unfold increasing in H.unfold lt in H.apply H.
qed.

theorem increasing_to_le: \forall f:nat \to nat. (increasing f) 
\to \forall m:nat. \exists i. m \le (f i).
intros.elim m.
apply (ex_intro ? ? O).apply le_O_n.
elim H1.
apply (ex_intro ? ? (S a)).
apply (trans_le ? (S (f a))).
apply le_S_S.assumption.
simplify in H.unfold increasing in H.unfold lt in H.
apply H.
qed.

theorem increasing_to_le2: \forall f:nat \to nat. (increasing f) 
\to \forall m:nat. (f O) \le m \to 
\exists i. (f i) \le m \land m <(f (S i)).
intros.elim H1.
apply (ex_intro ? ? O).
split.apply le_n.apply H.
elim H3.elim H4.
cut ((S n1) < (f (S a)) \lor (S n1) = (f (S a))).
elim Hcut.
apply (ex_intro ? ? a).
split.apply le_S. assumption.assumption.
apply (ex_intro ? ? (S a)).
split.rewrite < H7.apply le_n.
rewrite > H7.
apply H.
apply le_to_or_lt_eq.apply H6.
qed.
