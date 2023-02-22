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

include "higher_order_defs/functions.ma".

inductive nat : Set \def
  | O : nat
  | S : nat \to nat.

interpretation "Natural numbers" 'N = nat.

default "natural numbers" cic:/matita/nat/nat/nat.ind.

alias num (instance 0) = "natural number".

definition pred: nat \to nat \def
 \lambda n:nat. match n with
 [ O \Rightarrow  O
 | (S p) \Rightarrow p ].

theorem pred_Sn : \forall n:nat.n=(pred (S n)).
 intros. simplify. reflexivity.
qed.

theorem injective_S : injective nat nat S.
 unfold injective.
 intros.
 rewrite > pred_Sn.
 rewrite > (pred_Sn y).
 apply eq_f. assumption.
qed.

theorem inj_S : \forall n,m:nat.(S n)=(S m) \to n=m \def
 injective_S.

theorem not_eq_S  : \forall n,m:nat. 
 \lnot n=m \to S n \neq S m.
 intros. unfold Not. intros.
 apply H. apply injective_S. assumption.
qed.

definition not_zero : nat \to Prop \def
 \lambda n: nat.
  match n with
  [ O \Rightarrow False
  | (S p) \Rightarrow True ].

theorem not_eq_O_S : \forall n:nat. O \neq S n.
 intros. unfold Not. intros.
 cut (not_zero O).
 exact Hcut.
 rewrite > H.exact I.
qed.

theorem not_eq_n_Sn : \forall n:nat. n \neq S n.
 intros.elim n.
 apply not_eq_O_S.
 apply not_eq_S.assumption.
qed.

theorem nat_case:
 \forall n:nat.\forall P:nat \to Prop. 
  P O \to  (\forall m:nat. P (S m)) \to P n.
intros.elim n
  [ assumption
  | apply H1 ]
qed.

theorem nat_case1:
 \forall n:nat.\forall P:nat \to Prop. 
  (n=O \to P O) \to  (\forall m:nat. (n=(S m) \to P (S m))) \to P n.
intros 2; elim n
  [ apply H;reflexivity
  | apply H2;reflexivity ]
qed.

theorem nat_elim2 :
 \forall R:nat \to nat \to Prop.
  (\forall n:nat. R O n) 
  \to (\forall n:nat. R (S n) O) 
  \to (\forall n,m:nat. R n m \to R (S n) (S m))
  \to \forall n,m:nat. R n m.
intros 5;elim n 
  [ apply H
  | apply (nat_case m)
    [ apply H1
    | intro; apply H2; apply H3 ] ]
qed.

theorem decidable_eq_nat : \forall n,m:nat.decidable (n=m).
 intros.unfold decidable.
 apply (nat_elim2 (\lambda n,m.(Or (n=m) ((n=m) \to False))))
 [ intro; elim n1
   [ left; reflexivity
   | right; apply not_eq_O_S ]
 | intro; right; intro; apply (not_eq_O_S n1); apply sym_eq; assumption
 | intros; elim H
   [ left; apply eq_f; assumption
   | right; intro; apply H1; apply inj_S; assumption ] ]
qed.
