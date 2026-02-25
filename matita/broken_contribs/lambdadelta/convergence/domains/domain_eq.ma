(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/domains/domain.ma".
include "convergence/notation/relations/equivalent_3.ma".
include "convergence/notation/relations/not_equivalent_3.ma".
include "convergence/notation/relations/neg_equivalent_3.ma".

(* ABSTRACT DOMAIN **********************************************************)

(* Equivalence **************************************************************)

definition dom_eq (D:𝔻𝟬): relation2 D D ≝
           λd1,d2. ∧∧ d1 ∈ D & d2 ∈ D & d1 ≍𝘀 d2
.

interpretation
  "equivalence (domain)"
  'Equivalent D d1 d2 = (dom_eq D d1 d2).

interpretation
  "negated equivalence (domain)"
  'NotEquivalent D d1 d2 = (negation (dom_eq D d1 d2)).

interpretation
  "negated equivalence alternative (domain)"
  'NegEquivalent D d1 d2 = (negation (dom_eq D d1 d2)).

(* Corollaries **************************************************************)

lemma dom_eq_refl (D:𝔻𝟬) (d):
      d ∈ D → d ≍ d.
/3 width=1 by dom_E_refl, and3_intro/
qed.

lemma dom_eq_sym (D) (d1) (d2):
      d1 ≍ d2 → d2 ≍❪D❫ d1.
#D #d1 #d2 * #Hd1 #Hd2 #Hd12
/3 width=1 by dom_E_sym, and3_intro/
qed-.

lemma dom_eq_trans (D) (d0):
      ∀d1. d1 ≍ d0 → ∀d2. d0 ≍ d2 → d1 ≍❪D❫ d2.
#D #d0 #d1 * #Hd1 #Hd0 #Hd10 #d2 * #_ #Hd2 #Hd02
/3 width=4 by dom_E_trans, and3_intro/
qed-.

lemma dom_eq_canc_sx (D) (d0):
      ∀d1. d0 ≍ d1 → ∀d2. d0 ≍ d2 → d1 ≍❪D❫ d2.
#D #d0 #d1 * #Hd0 #Hd1 #Hd01 #d2 * #_ #Hd2 #Hd02
/3 width=4 by dom_E_canc_sx, and3_intro/
qed-.

lemma dom_eq_canc_dx (D) (d0):
      ∀d1. d1 ≍ d0 → ∀d2. d2 ≍ d0 → d1 ≍❪D❫ d2.
#D #d0 #d1 * #Hd1 #Hd0 #Hd10 #d2 * #Hd2 #_ #Hd20
/3 width=4 by dom_E_canc_dx, and3_intro/
qed-.
