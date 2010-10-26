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

include "logic/pts.ma".

definition reflexive ≝ λT:Type[0].λP:T → T → CProp[0]. ∀x.P x x.
definition symmetric ≝ λT:Type[0].λP:T → T → CProp[0]. ∀x,y.P x y → P y x.
definition transitive ≝ λT:Type[0].λP:T → T → CProp[0]. ∀z,x,y. P x z → P z y → P x y.

record equivalence_relation (A:Type[0]) : Type[1] ≝
 { eq_rel:2> A → A → CProp[0];
   refl: reflexive ? eq_rel;
   sym: symmetric ? eq_rel;
   trans: transitive ? eq_rel
 }.
