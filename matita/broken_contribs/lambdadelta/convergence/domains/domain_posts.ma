(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/subset1.ma".
include "convergence/domains/domain_struct.ma".
include "convergence/notation/functions/category_d0_p_0.ma".

(* ABSTRACT DOMAIN **********************************************************)

(* Postulates ***************************************************************)

record domain_postulates (D:𝔻𝟬𝗌): Prop ≝
{ dom_E_refl (d):
  d ∈ D → d ≍𝘀 d
; dom_E_sym:
  ∀d1. d1 ∈ D → ∀d2. d2 ∈ D →
  d1 ≍𝘀 d2 → d2 ≍𝘀 d1
; dom_E_trans (d0):
  d0 ∈ D → ∀d1. d1 ∈ D → d1 ≍𝘀 d0 →
  ∀d2. d2 ∈ D → d0 ≍𝘀 d2 → d1 ≍𝘀 d2
}.

interpretation
  "postulates (domain)"
  'CategoryD0_p = (domain_postulates).

(* Corollaries **************************************************************)

lemma dom_E_canc_sx (D):
      D 𝛆 𝔻𝟬𝗽 →
      ∀d0. d0 ∈ D →
      ∀d1. d1 ∈ D → d0 ≍𝘀 d1 →
      ∀d2. d2 ∈ D → d0 ≍𝘀 d2 → d1 ≍𝘀 d2.
/3 width=4 by dom_E_trans, dom_E_sym/
qed-.

lemma dom_E_canc_dx (D):
      D 𝛆 𝔻𝟬𝗽 →
      ∀d0. d0 ∈ D →
      ∀d1. d1 ∈ D → d1 ≍𝘀 d0 →
      ∀d2. d2 ∈ D → d2 ≍𝘀 d0 → d1 ≍𝘀 d2.
/3 width=5 by dom_E_trans, dom_E_sym/
qed-.
