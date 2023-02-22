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

inductive True: Prop \def
I : True.

default "true" cic:/matita/logic/connectives/True.ind.

inductive False: Prop \def .

default "false" cic:/matita/logic/connectives/False.ind.

definition Not: Prop \to Prop \def
\lambda A. (A \to False).

interpretation "logical not" 'not x = (Not x).

theorem absurd : \forall A,C:Prop. A \to \lnot A \to C.
intros. elim (H1 H).
qed.

default "absurd" cic:/matita/logic/connectives/absurd.con.

theorem not_to_not : \forall A,B:Prop. (A → B) \to ¬B →¬A.
intros.unfold.intro.apply H1.apply (H H2).
qed.

default "absurd" cic:/matita/logic/connectives/absurd.con.

inductive And (A,B:Prop) : Prop \def
    conj : A \to B \to (And A B).

interpretation "logical and" 'and x y = (And x y).

theorem proj1: \forall A,B:Prop. A \land B \to A.
intros. elim H. assumption.
qed.

theorem proj2: \forall A,B:Prop. A \land B \to B.
intros. elim H. assumption.
qed.

inductive Or (A,B:Prop) : Prop \def
     or_introl : A \to (Or A B)
   | or_intror : B \to (Or A B).

interpretation "logical or" 'or x y = (Or x y).

theorem Or_ind':
 \forall A,B:Prop.
  \forall P: A \lor B \to Prop.
   (\forall p:A. P (or_introl ? ? p)) \to
   (\forall q:B. P (or_intror ? ? q)) \to
    \forall p:A \lor B. P p.
 intros.
 apply
  (match p return \lambda p.P p with
    [(or_introl p) \Rightarrow H p
    |(or_intror q) \Rightarrow H1 q]).
qed.

definition decidable : Prop \to Prop \def \lambda A:Prop. A \lor \lnot A.

inductive ex (A:Type) (P:A \to Prop) : Prop \def
    ex_intro: \forall x:A. P x \to ex A P.

interpretation "exists" 'exists x = (ex ? x).

inductive ex2 (A:Type) (P,Q:A \to Prop) : Prop \def
    ex_intro2: \forall x:A. P x \to Q x \to ex2 A P Q.

definition iff :=
 \lambda A,B. (A -> B) \land (B -> A).
