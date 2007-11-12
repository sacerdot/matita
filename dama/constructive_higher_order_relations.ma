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

set "baseuri" "cic:/matita/constructive_higher_order_relations".

include "constructive_connectives.ma".

definition cotransitive ≝
 λC:Type.λlt:C→C→Type.∀x,y,z:C. lt x y → lt x z ∨ lt z y. 

definition coreflexive ≝ λC:Type.λlt:C→C→Type. ∀x:C. ¬ (lt x x).

definition antisymmetric ≝
 λC:Type.λle:C→C→Type.λeq:C→C→Type.∀x,y:C.le x y → le y x → eq x y.

definition symmetric ≝
 λC:Type.λle:C→C→Type.∀x,y:C.le x y → le y x.

definition transitive ≝
 λC:Type.λle:C→C→Type.∀x,y,z:C.le x y → le y z → le x z.
