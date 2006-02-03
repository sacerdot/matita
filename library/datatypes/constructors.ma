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

inductive Prod (A,B:Set) : Set \def
pair : A \to B \to Prod A B.

definition fst \def \lambda A,B:Set.\lambda p: Prod A B.
match p with
[(pair a b) \Rightarrow a]. 

definition snd \def \lambda A,B:Set.\lambda p: Prod A B.
match p with
[(pair a b) \Rightarrow b].

theorem eq_pair_fst_snd: \forall A,B:Set.\forall p: Prod A B.
p = pair A B (fst A B p) (snd A B p).
intros.elim p.simplify.reflexivity.
qed.

inductive Sum (A,B:Set) : Set \def
  inl : A \to Sum A B
| inr : B \to Sum A B.
