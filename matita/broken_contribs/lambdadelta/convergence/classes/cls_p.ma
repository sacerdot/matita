(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/subsets/subset1.ma".
include "convergence/classes/cls_s.ma".
include "convergence/notation/functions/category_c0_p_0.ma".

(* CLASS ********************************************************************)

(* Postulates ***************************************************************)

record cls_P (X:ℂ𝟬𝗌): Prop ≝
{ cls_pe_refl (x):
  x ≍❪X❫ x
; cls_pe_sym:
  ∀x1,x2. x1 ≍ x2 → x2 ≍❪X❫ x1
; cls_pe_trans (x0):
  ∀x1. x1 ≍ x0 → ∀x2. x0 ≍ x2 → x1 ≍❪X❫ x2
}.

interpretation
  "postulates (class)"
  'CategoryC0_p = (cls_P).

(* Corollaries **************************************************************)

lemma cls_pe_canc_sx (X):
      X ϵ¹ ℂ𝟬𝗉 →
      ∀x0,x1. x0 ≍ x1 →
      ∀x2. x0 ≍ x2 → x1 ≍❪X❫ x2.
/3 width=4 by cls_pe_trans, cls_pe_sym/
qed-.

lemma cls_pe_canc_dx (X):
      X ϵ¹ ℂ𝟬𝗉 →
      ∀x0,x1. x1 ≍ x0 →
      ∀x2. x2 ≍ x0 → x1 ≍❪X❫ x2.
/3 width=5 by cls_pe_trans, cls_pe_sym/
qed-.
