(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/subsets/subset1.ma".
include "convergence/classes/class_struct.ma".
include "convergence/notation/functions/category_c0_p_0.ma".

(* CLASS ********************************************************************)

(* Postulates ***************************************************************)

record class_postulates (X:ℂ𝟬𝗌): Prop ≝
{ cls_E_refl (x):
  x ≍❪X❫ x
; cls_E_sym:
  ∀x1,x2. x1 ≍ x2 → x2 ≍❪X❫ x1
; cls_E_trans (x0):
  ∀x1. x1 ≍ x0 → ∀x2. x0 ≍ x2 → x1 ≍❪X❫ x2
}.

interpretation
  "postulates (class)"
  'CategoryC0_p = (class_postulates).

(* Corollaries **************************************************************)

lemma cls_E_canc_sx (X):
      X ϵ¹ ℂ𝟬𝗽 →
      ∀x0,x1. x0 ≍ x1 →
      ∀x2. x0 ≍ x2 → x1 ≍❪X❫ x2.
/3 width=4 by cls_E_trans, cls_E_sym/
qed-.

lemma cls_E_canc_dx (X):
      X ϵ¹ ℂ𝟬𝗽 →
      ∀x0,x1. x1 ≍ x0 →
      ∀x2. x2 ≍ x0 → x1 ≍❪X❫ x2.
/3 width=5 by cls_E_trans, cls_E_sym/
qed-.
