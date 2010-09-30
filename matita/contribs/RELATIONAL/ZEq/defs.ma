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

inductive ZEq: Zah → Zah → Prop :=
   | zeq: ∀m1,m2,m3,m4,n. m1 ⊕ m4 ≍ n → m3 ⊕ m2 ≍ n →
          ZEq 〈m1,m2〉 〈m3, m4〉
.

interpretation "integer equality" 'napart x y = (ZEq x y).

