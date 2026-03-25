(**************************************************************************)
(*       ___                                                              *)
(*      ||M||                                                             *)
(*      ||A||       A project by Andrea Asperti                           *)
(*      ||T||                                                             *)
(*      ||I||       Developers:                                           *)
(*      ||T||         The HELM team.                                      *)
(*      ||A||         http://helm.cs.unibo.it                             *)
(*      \   /                                                             *)
(*       \ /        This file is distributed under the terms of the       *)
(*        v         GNU General Public License Version 2                  *)
(*                                                                        *)
(**************************************************************************)

include "ground/subsets/subset_le.ma".
include "ground/subsets/subset_listed_1.ma".
include "ground/subsets/subset_listed_2.ma".
include "delayed_updating/syntax/path_root_eq.ma".
include "delayed_updating/reduction/prototerm_x_redex_main.ma".
include "delayed_updating/reduction/path_dbf_residuals.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Constructions with subset_le *********************************************)

lemma path_dbfr_neq_le (s) (r):
      s ⧸= r → ❴s❵ ⊆ (s /𝐝𝐛𝐟 r).
#s #r #Hs #y #Hy
>(subset_in_inv_single ??? Hy) -y
/2 width=1 by path_dbfr_neq/
qed.

lemma path_dbfr_neq_ge (s) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → p◖𝗦 ⧸≚ s →
      (s /𝐝𝐛𝐟 r) ⊆ ❴s❵.
#s #r #p #b #q #n #Hr #Hs #x * *
[ #_ #H0 destruct //
| #p0 #b0 #q0 #q1 #n0 #H0r #_ #H0s #H0 destruct
  elim (pxr_inj … Hr H0r) -r #H1 #H2 #H3 #H4 destruct
  elim Hs -Hs -b0 -q0 -n0
  /2 width=1 by path_req_mk_le/
]
qed.

lemma path_dbfr_side_le (x) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → x ϵ 𝐏 →
      let s ≝ p◖𝗦●x in
      ❴s,𝐫❨p,⓪b,q,⁤↑(♭b+n)❩●x❵ ⊆ (s /𝐝𝐛𝐟 r).
#x #r #p #b #q #n #Hr #Hx #y #H0
elim (subset_in_inv_pair ???? H0) -H0 #H0 destruct
[ lapply (pxr_des_eq … Hr) -Hr #H0 destruct
  @path_dbfr_neq_le [| // ]
  @(path_neq_p_beta ???? (𝐞))
| /2 width=1 by path_dbfr_side/
]
qed.

lemma path_dbfr_side_ge (x) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ →
      let s ≝ p◖𝗦●x in
      (s /𝐝𝐛𝐟 r) ⊆ ❴s,𝐫❨p,⓪b,q,⁤↑(♭b+n)❩●x❵.
#x #r #p #b #q #n #Hr #y * *
[ #_ #H0 destruct //
| #p0 #b0 #q0 #x0 #n0 #Hr0 #_ #H0 #H1 destruct
  elim (pxr_inj … Hr Hr0) #H1 #H2 #H3 #H4 destruct -r
  lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0 destruct //
]
qed.

(* Inversions with subset_le ************************************************)

lemma path_dbfr_le_refl (r):
      (r /𝐝𝐛𝐟 r) ⊆ Ⓕ.
#r #s #Hs
elim (path_dbfr_inv_refl … Hs)
qed.
