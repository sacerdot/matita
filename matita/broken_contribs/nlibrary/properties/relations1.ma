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

ndefinition reflexive1 ≝ λT:Type[1].λP:T → T → CProp[1]. ∀x.P x x.
ndefinition symmetric1 ≝ λT:Type[1].λP:T → T → CProp[1]. ∀x,y.P x y → P y x.
ndefinition transitive1 ≝ λT:Type[1].λP:T → T → CProp[1]. ∀z,x,y. P x z → P z y → P x y.

nrecord equivalence_relation1 (A:Type[1]) : Type[2] ≝
 { eq_rel1:2> A → A → CProp[1];
   refl1: reflexive1 ? eq_rel1;
   sym1: symmetric1 ? eq_rel1;
   trans1: transitive1 ? eq_rel1
 }.
