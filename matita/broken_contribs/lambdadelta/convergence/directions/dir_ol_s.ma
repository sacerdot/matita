(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_ol.ma".
include "convergence/directions/dir_s.ma".
include "convergence/notation/relations/white_heart_3.ma".
include "convergence/notation/relations/neg_white_heart_3.ma".

(* OVERLAP FOR DIRECTION ****************************************************)

definition dir_ol (X) (D1:𝔻𝗌 X) (D2:𝔻𝗌 X): Prop ≝
           ∀u1,u2. u1 ϵ D1 → u2 ϵ D2 → u1 ≬ u2
.

interpretation
  "overlap (direction)"
  'WhiteHeart X D1 D2 = (dir_ol X D1 D2).

interpretation
  "negated overlap (direction)"
  'NegWhiteHeart X D1 D2 = (negation (dir_ol X D1 D2)).

(* Corollaries **************************************************************)

lemma dir_ol_sym (X) (D1:𝔻𝗌 X) (D2:𝔻𝗌 X):
      D2 ♡ D1 → D1 ♡ D2.
/3 width=1 by subset_ol_sym/
qed-.
