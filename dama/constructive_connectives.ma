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

interpretation "classical or" 'or x y =
  (cic:/matita/constructive_connectives/or.ind#xpointer(1/1) x y).

