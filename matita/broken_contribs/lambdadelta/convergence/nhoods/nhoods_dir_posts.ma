(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/direction_posts.ma".
include "convergence/nhoods/nhoods_posts.ma".
include "convergence/nhoods/nhoods_dir_struct.ma".

(* DIRECTION FOR NHOODS *****************************************************)

(* Postulates ***************************************************************)

(* Note: a nhood filter is a direction *)
lemma nhs_dir_p (X) (F:𝔽𝗌 X) (x:X):
      F ϵ 𝔽𝗉 → 𝝙𝗌[F]❨x❩ ϵ 𝔻𝗉.
#X #F #x #HF
@mk_direction_postulates
[ /2 width=3 by nhs_e_bw/
| /2 width=1 by nhs_i/
| /3 width=4 by nhs_d, subsets_inh_in/
| #u1 #u2 #Hu1 #Hu2 (**) (* auto fails *)
  @(ex2_intro ????? (subset_le_refl …))
  /2 width=1 by nhs_a/
]
qed.
