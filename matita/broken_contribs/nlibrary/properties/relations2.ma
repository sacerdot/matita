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

ndefinition reflexive2 ≝ λT:Type[2].λP:T → T → CProp[2]. ∀x.P x x.
ndefinition symmetric2 ≝ λT:Type[2].λP:T → T → CProp[2]. ∀x,y.P x y → P y x.
ndefinition transitive2 ≝ λT:Type[2].λP:T → T → CProp[2]. ∀z,x,y. P x z → P z y → P x y.

nrecord equivalence_relation2 (A:Type[2]) : Type[3] ≝
 { eq_rel2:2> A → A → CProp[2];
   refl2: reflexive2 ? eq_rel2;
   sym2: symmetric2 ? eq_rel2;
   trans2: transitive2 ? eq_rel2
 }.
