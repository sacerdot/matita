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

include "ground/subsets/subset_eq.ma".
include "ground/subsets/subset_listed_le.ma".
include "delayed_updating/reduction/path_dbf_residuals_le.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Constructions with subset_eq *********************************************)

lemma path_dbfr_refl (r):
      Ⓕ ⇔ (r /𝐝𝐛𝐟 r).
/3 width=4 by path_dbfr_le_refl, subset_empty_le_sx, conj/
qed.

lemma path_dbfr_neq_eq (s) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → s ⧸= r → p◖𝗦 ⧸≚ s →
      ❴s❵ ⇔ (s /𝐝𝐛𝐟 r).
/3 width=8 by path_dbfr_neq_ge, path_dbfr_neq_le, conj/
qed.

lemma path_dbfr_side_eq (x) (s) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → x ϵ 𝐏 → s = p◖𝗦●x →
      ❴s,𝐫❨p,⓪b,q,⁤↑(♭b+n)❩●x❵ ⇔ (s /𝐝𝐛𝐟 r).
/3 width=5 by path_dbfr_side_ge, path_dbfr_side_le, conj/
qed.

lemma path_dbfr_side_sx (r1) (p1) (p2) (b1) (b2) (q1) (q2) (n2) (n1) (x1) (x2):
      r1 ϵ 𝐑❨p1,b1,q1,n1❩ →
      p1◖𝗦 ⧸≚ 𝐫❨p2,b2,q2,n2❩ → p2◖𝗦●x1 = r1 →
      ❴𝐫❨p2,b2,q2,n2❩●x2❵ ⇔ (𝐫❨p2,b2,q2,n2❩●x2) /𝐝𝐛𝐟 r1.
#r1 #p1 #p2 #b1 #b2 #q1 #q2 #n1 #n2 #x1 #x2 #Hr1 #Hnr2 #H0
@(path_dbfr_neq_eq … Hr1)
[ <H0 /3 width=7 by path_neq_p_beta, sym_eq/
| /3 width=3 by path_req_des_append_bi_dx/
]
qed.
