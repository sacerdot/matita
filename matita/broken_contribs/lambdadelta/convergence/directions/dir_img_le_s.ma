(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_ext_le.ma".
include "convergence/directions/dir_le_s.ma".
include "convergence/directions/dir_img_s.ma".

(* IMAGE FOR DIRECTION ******************************************************)

(* Constructions with dir_le ************************************************)

lemma dir_le_img_bi (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D1:𝔻𝗌 X) (D2:𝔻𝗌 X):
      D1 ⊑ D2 → f＠𝗌❨D1❩ ⊑ f＠𝗌❨D2❩.
#X #Y #f #D1 #D2 #HD12 #v1 * #u1 #Hu1 * #_ #Huv1
elim (HD12 … Hu1) -D1 #u2 #Hu2 #Hu21
lapply (subset_le_trans … (subset_le_ext_f1_bi … Hu21) … Huv1) -u1 #H0
/3 width=3 by dir_img_s_in, ex2_intro/
qed.
