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

set "baseuri" "cic:/matita/constructive_connectives/".

inductive or (A,B:Type) : Type \def
   Left : A → or A B
 | Right : B → or A B.

interpretation "constructive or" 'or x y =
  (cic:/matita/constructive_connectives/or.ind#xpointer(1/1) x y).

inductive ex (A:Type) (P:A→Prop) : Type \def
  ex_intro: ∀w:A. P w → ex A P.

notation < "hvbox(Σ ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'exists ${default
  @{\lambda ${ident i} : $ty. $p)}
  @{\lambda ${ident i} . $p}}}.

interpretation "constructive exists" 'sigma \eta.x =
  (cic:/matita/constructive_connectives/ex.ind#xpointer(1/1) _ x).