(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/dir_le_s.ma".
include "convergence/notation/functions/function_b_s_2.ma".

(* BASE FOR DIRECTION *******************************************************)

(* Note: if D is a filter then B is by def a base for D *)
definition dir_base_s (X) (D:𝔻𝗌 X): 𝒫❨𝔻𝗌 X❩ ≝
           { B | ∧∧ B ⊆ D & D ⊑ B }
.

interpretation
  "base (direction)"
  'FunctionB_s X D = (dir_base_s X D).

(* Corollaries **************************************************************)

lemma dir_base_s_refl (X) (D:𝔻𝗌 X):
      D ϵ 𝗕𝗌❨D❩.
/3 width=1 by conj, dir_le_refl/
qed.

theorem dir_base_s_trans (X) (B2:𝔻𝗌 X):
        ∀B1. B1 ϵ 𝗕𝗌❨B2❩ → ∀D. B2 ϵ 𝗕𝗌❨D❩ → B1 ϵ 𝗕𝗌❨D❩.
#X #B2 #B1 * #HB12 #HB21 #D * #H1D #H2D
/3 width=5 by dir_le_trans, subset_le_trans, conj/
qed-.
