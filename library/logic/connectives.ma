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

set "baseuri" "cic:/matita/logic/connectives/".

inductive True: Prop \def
I : True.

default "true" cic:/matita/logic/connectives/True.ind.

inductive False: Prop \def .

default "false" cic:/matita/logic/connectives/False.ind.

definition Not: Prop \to Prop \def
\lambda A. (A \to False).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "logical not" 'not x = (cic:/matita/logic/connectives/Not.con x).

theorem absurd : \forall A,C:Prop. A \to \lnot A \to C.
intros. elim (H1 H).
qed.

default "absurd" cic:/matita/logic/connectives/absurd.con.

inductive And (A,B:Prop) : Prop \def
    conj : A \to B \to (And A B).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "logical and" 'and x y = (cic:/matita/logic/connectives/And.ind#xpointer(1/1) x y).

theorem proj1: \forall A,B:Prop. A \land B \to A.
intros. elim H. assumption.
qed.

theorem proj2: \forall A,B:Prop. A \land B \to B.
intros. elim H. assumption.
qed.

inductive Or (A,B:Prop) : Prop \def
     or_introl : A \to (Or A B)
   | or_intror : B \to (Or A B).

(*CSC: the URI must disappear: there is a bug now *)
interpretation "logical or" 'or x y =
  (cic:/matita/logic/connectives/Or.ind#xpointer(1/1) x y).

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

(*CSC: the URI must disappear: there is a bug now *)
interpretation "exists" 'exists \eta.x =
  (cic:/matita/logic/connectives/ex.ind#xpointer(1/1) _ x).

notation < "hvbox(\exists ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'exists ${default
  @{\lambda ${ident i} : $ty. $p)}
  @{\lambda ${ident i} . $p}}}.

inductive ex2 (A:Type) (P,Q:A \to Prop) : Prop \def
    ex_intro2: \forall x:A. P x \to Q x \to ex2 A P Q.

