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

set "baseuri" "cic:/matita/datatypes/constructors/".
include "logic/equality.ma".

inductive void : Set \def.

inductive unit : Set ≝ something: unit.

inductive Prod (A,B:Type) : Type \def
pair : A \to B \to Prod A B.

interpretation "Pair construction" 'pair x y =
 (cic:/matita/datatypes/constructors/Prod.ind#xpointer(1/1/1) _ _ x y).

notation "hvbox(\langle x break , y \rangle )" with precedence 89
for @{ 'pair $x $y}.

interpretation "Product" 'product x y =
 (cic:/matita/datatypes/constructors/Prod.ind#xpointer(1/1) x y).

notation "hvbox(x break \times y)" with precedence 89
for @{ 'product $x $y}.

definition fst \def \lambda A,B:Type.\lambda p: Prod A B.
match p with
[(pair a b) \Rightarrow a]. 

definition snd \def \lambda A,B:Type.\lambda p: Prod A B.
match p with
[(pair a b) \Rightarrow b].

interpretation "First projection" 'fst x =
 (cic:/matita/datatypes/constructors/fst.con _ _ x).

notation "\fst x" with precedence 89
for @{ 'fst $x}.

interpretation "Second projection" 'snd x =
 (cic:/matita/datatypes/constructors/snd.con _ _ x).

notation "\snd x" with precedence 89
for @{ 'snd $x}.

theorem eq_pair_fst_snd: \forall A,B:Type.\forall p:Prod A B.
p = 〈 (\fst p), (\snd p) 〉.
intros.elim p.simplify.reflexivity.
qed.

inductive Sum (A,B:Type) : Type \def
  inl : A \to Sum A B
| inr : B \to Sum A B.

interpretation "Disjoint union" 'plus A B =
 (cic:/matita/datatypes/constructors/Sum.ind#xpointer(1/1) A B).

inductive option (A:Type) : Type ≝
   None : option A
 | Some : A → option A.