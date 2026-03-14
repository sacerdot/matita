(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction_struct_center.ma".
include "convergence/directions/direction_struct_order.ma".

(* ORDER FOR DIRECTION ******************************************************)

(* Destructions with ctr ****************************************************)

lemma dir_le_des_ctr (X) (D1:𝔻𝗌 X) (D2:𝔻𝗌 X):
      D1 ⊑ D2 → (𝗖𝘁𝗿 D2) ⊆ (𝗖𝘁𝗿 D1).
#X #D1 #D2 #HD12
@dir_ctr_ge #u1 #Hu1
elim (HD12 … Hu1) -HD12 #u2 #Hu2 #Hu21
@(subset_le_trans ????? Hu21) -D1 -u1
/2 width=1 by dir_ctr_le/
qed-.
