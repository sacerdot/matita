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



include "constructive_connectives.ma".
include "higher_order_defs/relations.ma".

definition cotransitive ≝
 λC:Type.λlt:C→C→Type.∀x,y,z:C. lt x y → lt x z ∨ lt z y. 

definition coreflexive ≝ λC:Type.λlt:C→C→Type. ∀x:C. ¬ (lt x x).

definition antisymmetric ≝
 λC:Type.λle:C→C→Type.λeq:C→C→Type.∀x,y:C.le x y → le y x → eq x y.

definition symmetric ≝
 λC:Type.λle:C→C→Type.∀x,y:C.le x y → le y x.

definition transitive ≝
 λC:Type.λle:C→C→Type.∀x,y,z:C.le x y → le y z → le x z.

definition associative ≝
 λC:Type.λop:C→C→C.λeq:C→C→Type.∀x,y,z. eq (op x (op y z)) (op (op x y) z).

definition commutative ≝
 λC:Type.λop:C→C→C.λeq:C→C→Type.∀x,y. eq (op x y) (op y x).

alias id "antisymmetric" = "cic:/matita/higher_order_defs/relations/antisymmetric.con".
theorem antisimmetric_to_cotransitive_to_transitive:
 ∀C:Type.∀le:C→C→Prop. antisymmetric ? le → cotransitive ? le → transitive ? le.  
intros (T f Af cT); unfold transitive; intros (x y z fxy fyz);
lapply (cT ??z fxy) as H; cases H; [assumption] cases (Af ? ? fyz H1);
qed.

lemma Or_symmetric: symmetric ? Or.
unfold; intros (x y H); cases H; [right|left] assumption;
qed.

  
