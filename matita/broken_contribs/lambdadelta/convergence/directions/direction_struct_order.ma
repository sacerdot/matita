(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_le.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/relations/sqimageeq_3.ma".
include "convergence/notation/relations/not_sqimageeq_3.ma".
include "convergence/notation/relations/neg_sqimageeq_3.ma".

(* ORDER FOR DIRECTION ******************************************************)

(* Note: D1 is not finer than D2 *)
(* Note: if D1 is a filter then D2 is by def a base for D1 *)
definition dir_le (X) (D1:𝔻𝗌 X) (D2:𝔻𝗌 X): Prop ≝
           ∀u1. u1 ϵ D1 → ∃∃u2. u2 ϵ D2 & u2 ⊆ u1
.

interpretation
  "order (direction)"
  'SqImageEq X D1 D2 = (dir_le X D1 D2).

interpretation
  "negated order (direction)"
  'NotSqImageEq X D1 D2 = (negation (dir_le X D1 D2)).

interpretation
  "negated order alternative (direction)"
  'NegSqImageEq X D1 D2 = (negation (dir_le X D1 D2)).

(* Corollaries **************************************************************)

lemma dir_le_refl (X) (D:𝔻𝗌 X):
      D ⊑ D.
/2 width=3 by ex2_intro/
qed.

theorem dir_le_trans (X) (D0:𝔻𝗌 X):
        ∀D1. D1 ⊑ D0 → ∀D2. D0 ⊑ D2 → D1 ⊑ D2.
#X #D0 #D1 #HD10 #D2 #HD02 #u1 #Hu1
elim (HD10 … Hu1) -HD10 #u0 #Hu0 #Hu01
elim (HD02 … Hu0) -HD02 #u2 #Hu2 #Hu20
/3 width=5 by subset_le_trans, ex2_intro/
qed-.
