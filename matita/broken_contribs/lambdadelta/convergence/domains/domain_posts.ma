(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/subset1.ma".
include "convergence/domains/domain_struct.ma".
include "convergence/notation/functions/category_d0_p_0.ma".

(* ABSTRACT DOMAIN **********************************************************)

(* Postulates ***************************************************************)

record domain_postulates (X:𝔻𝟬𝗌): Prop ≝
{ dom_E_refl (x):
  x ϵ X → x ≍𝘀 x
; dom_E_sym:
  ∀x1. x1 ϵ X → ∀x2. x2 ϵ X →
  x1 ≍𝘀 x2 → x2 ≍𝘀 x1
; dom_E_trans (x0):
  x0 ϵ X → ∀x1. x1 ϵ X → x1 ≍𝘀 x0 →
  ∀x2. x2 ϵ X → x0 ≍𝘀 x2 → x1 ≍𝘀 x2
}.

interpretation
  "postulates (domain)"
  'CategoryD0_p = (domain_postulates).

(* Corollaries **************************************************************)

lemma dom_E_canc_sx (X):
      X 𝛆 𝔻𝟬𝗽 →
      ∀x0. x0 ϵ X →
      ∀x1. x1 ϵ X → x0 ≍𝘀 x1 →
      ∀x2. x2 ϵ X → x0 ≍𝘀 x2 → x1 ≍𝘀 x2.
/3 width=4 by dom_E_trans, dom_E_sym/
qed-.

lemma dom_E_canc_dx (X):
      X 𝛆 𝔻𝟬𝗽 →
      ∀x0. x0 ϵ X →
      ∀x1. x1 ϵ X → x1 ≍𝘀 x0 →
      ∀x2. x2 ϵ X → x2 ≍𝘀 x0 → x1 ≍𝘀 x2.
/3 width=5 by dom_E_trans, dom_E_sym/
qed-.
