(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "convergence/directions/dir_p.ma".
include "convergence/nhoods/nhs_p.ma".
include "convergence/nhoods/nhs_dir_s.ma".

(* DIRECTION FOR NHOODS *****************************************************)

(* Postulates ***************************************************************)

(* Note: a nhood filter is a direction *)
lemma nhs_dir_p (X) (F:𝔽𝗌 X) (x:X):
      F ϵ 𝔽𝗉 → 𝝙𝗌[F]❨x❩ ϵ 𝔻𝗉.
#X #F #x #HF
@mk_dir_P
[ /2 width=3 by nhs_pe_bw/
| /2 width=1 by nhs_pi/
| /3 width=4 by nhs_pd, subsets_inh_in/
| #u1 #u2 #Hu1 #Hu2 (**) (* auto fails *)
  @(ex2_intro ????? (subset_le_refl …))
  /2 width=1 by nhs_pa/
]
qed-.
