(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_ol.ma".
include "convergence/directions/direction_struct.ma".

(* OVERLAP FOR DIRECTION ****************************************************)

definition dir_ol (X) (D1:𝔻𝗌 X) (D2:𝔻𝗌 X): Prop ≝
           ∀i1,i2. D1＠❨i1❩ ≬ D2＠❨i2❩
.

interpretation
  "overlap (direction)"
  'Between X D1 D2 = (dir_ol X D1 D2).

interpretation
  "negated overlap (direction)"
  'NotBetween X D1 D2 = (negation (dir_ol X D1 D2)).

(* Corollaries **************************************************************)

lemma dir_ol_sym (X) (D1:𝔻𝗌 X) (D2:𝔻𝗌 X):
      D2 ≬ D1 → D1 ≬ D2.
/2 width=1 by subset_ol_sym/
qed-.
