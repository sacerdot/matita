(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "logic/connectives.ma".

inductive Or (A,B:Type) : Type ≝
   Left : A → Or A B
 | Right : B → Or A B.

interpretation "constructive or" 'or x y = (Or x y).

inductive And (A,B:Type) : Type ≝
 | Conj : A → B → And A B.
 
interpretation "constructive and" 'and x y = (And x y).

inductive exT (A:Type) (P:A→Type) : Type ≝
  ex_introT: ∀w:A. P w → exT A P.

inductive ex (A:Type) (P:A→Prop) : Type ≝
  ex_intro: ∀w:A. P w → ex A P.

(*
notation < "hvbox(Σ ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'sigma ${default
  @{\lambda ${ident i} : $ty. $p)}
  @{\lambda ${ident i} . $p}}}.
*)

interpretation "constructive exists" 'exists \eta.x = (ex ? x).
interpretation "constructive exists (Type)" 'exists \eta.x = (exT ? x).

alias id "False" = "cic:/matita/logic/connectives/False.ind#xpointer(1/1)".
definition Not ≝ λx:Type.x → False.

interpretation "constructive not" 'not x = (Not x).
