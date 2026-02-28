(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/domain.ma".
include "convergence/notation/relations/equivalent_3.ma".
include "convergence/notation/relations/not_equivalent_3.ma".
include "convergence/notation/relations/neg_equivalent_3.ma".

(* ABSTRACT DOMAIN **********************************************************)

(* Equivalence **************************************************************)

definition dom_eq (X:𝔻𝟬): relation2 X X ≝
           λx1,x2. ∧∧ x1 ϵ X & x2 ϵ X & x1 ≍𝘀 x2
.

interpretation
  "equivalence (domain)"
  'Equivalent X x1 x2 = (dom_eq X x1 x2).

interpretation
  "negated equivalence (domain)"
  'NotEquivalent X x1 x2 = (negation (dom_eq X x1 x2)).

interpretation
  "negated equivalence alternative (domain)"
  'NegEquivalent X x1 x2 = (negation (dom_eq X x1 x2)).

(* Corollaries **************************************************************)

lemma dom_eq_refl (X:𝔻𝟬) (x):
      x ϵ X → x ≍ x.
/3 width=1 by dom_E_refl, and3_intro/
qed.

lemma dom_eq_sym (X) (x1) (x2):
      x1 ≍ x2 → x2 ≍❪X❫ x1.
#X #x1 #x2 * #Hx1 #Hx2 #Hx12
/3 width=1 by dom_E_sym, and3_intro/
qed-.

lemma dom_eq_trans (X) (x0):
      ∀x1. x1 ≍ x0 → ∀x2. x0 ≍ x2 → x1 ≍❪X❫ x2.
#X #x0 #x1 * #Hx1 #Hx0 #Hx10 #x2 * #_ #Hx2 #Hx02
/3 width=4 by dom_E_trans, and3_intro/
qed-.

lemma dom_eq_canc_sx (X) (x0):
      ∀x1. x0 ≍ x1 → ∀x2. x0 ≍ x2 → x1 ≍❪X❫ x2.
#X #x0 #x1 * #Hx0 #Hx1 #Hx01 #x2 * #_ #Hx2 #Hx02
/3 width=4 by dom_E_canc_sx, and3_intro/
qed-.

lemma dom_eq_canc_dx (X) (x0):
      ∀x1. x1 ≍ x0 → ∀x2. x2 ≍ x0 → x1 ≍❪X❫ x2.
#X #x0 #x1 * #Hx1 #Hx0 #Hx10 #x2 * #Hx2 #_ #Hx20
/3 width=4 by dom_E_canc_dx, and3_intro/
qed-.
