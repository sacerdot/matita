(* This file is part of the HELM digital library (http://helm.cs.unibo.it)
   and is distributed under the GNU General Public License (GPL) version 2.
*)

include "ground/subsets/subset_ext_le.ma".
include "convergence/directions/dir_p.ma".
include "convergence/directions/dir_img_s.ma".

(* IMAGE FOR DIRECTION ******************************************************)

(* Postulates ***************************************************************)

lemma dir_img_p (X:ℂ𝟬𝗌) (Y:ℂ𝟬𝗌) (f:X→Y) (D:𝔻𝗌 X):
      D ϵ 𝔻𝗉 → f＠𝗌❨D❩ ϵ 𝔻𝗉.
#X #Y #f #D #HD
@mk_dir_P
[ #v1 #v2 #Hv12 * #u #Hu #H0
  lapply (subset_eq_trans … Hv12 … H0) -v2 #H0
  /2 width=3 by ex2_intro/
| elim (subsets_inh_inv_in … @ dir_pi … HD) #u #Hu
  /3 width=2 by dir_img_s_in, subsets_inh_in/
| #v * #u #Hu #H0
  elim (subsets_inh_inv_in … @ dir_pd … HD … Hu) #x #Hx
  lapply (subset_in_eq_repl_back ??? (subset_in_ext_f1_dx ????? Hx) … H0) -Hx -H0
  /2 width=2 by subsets_inh_in/
| #v1 #v2 * #u1 #Hu1 * #_ #Huv1 * #u2 #Hu2 * #_ #Huv2
  elim (dir_pa_alt … HD … Hu1 Hu2) -Hu1 -Hu2 #u0 #Hu0 #Hu01 #Hu02
  lapply (subset_le_trans … (subset_le_ext_f1_bi … Hu01) … Huv1) -Hu01 -Huv1 #H01
  lapply (subset_le_trans … (subset_le_ext_f1_bi … Hu02) … Huv2) -Hu02 -Huv2 #H02
  /3 width=4 by dir_img_s_in, subset_le_and_dx, ex2_intro/
]
qed-.
