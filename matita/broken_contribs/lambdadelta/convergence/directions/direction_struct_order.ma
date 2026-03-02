(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_le.ma".
include "convergence/directions/direction_struct.ma".
include "convergence/notation/relations/sqimageeq_3.ma".
include "convergence/notation/relations/not_sqimageeq_3.ma".
include "convergence/notation/relations/neg_sqimageeq_3.ma".

(* ORDER FOR DIRECTION ******************************************************)

(* Note: D1 is not finer than D2 ********************************************)
definition dir_le (X) (D1:𝔻𝗌 X) (D2:𝔻𝗌 X): Prop ≝
           ∀i1. ∃i2. D2＠❨i2❩ ⊆ D1＠❨i1❩ 
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
/2 width=2 by ex_intro/
qed.

theorem dir_le_trans (X) (D0:𝔻𝗌 X):
        ∀D1. D1 ⊑ D0 → ∀D2. D0 ⊑ D2 → D1 ⊑ D2.
#X #D0 #D1 #HD10 #D2 #HD02 #i1
elim (HD10 i1) -HD10 #i0 #HD01
elim (HD02 i0) -HD02 #i2 #HD20
/3 width=5 by subset_le_trans, ex_intro/
qed-.
