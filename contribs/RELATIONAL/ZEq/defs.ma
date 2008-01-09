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



include "datatypes/Zah.ma".
include "NPlus/defs.ma".

inductive ZEq: Zah \to Zah \to Prop :=
   | zeq: \forall m1,m2,m3,m4,n.
          (m1 + m4 == n) \to (m3 + m2 == n) \to
          ZEq \langle m1, m2 \rangle \langle m3, m4 \rangle
.

interpretation "integer equality" 'eq x y =
 (cic:/matita/RELATIONAL/ZEq/defs/ZEq.ind#xpointer(1/1) x y).

