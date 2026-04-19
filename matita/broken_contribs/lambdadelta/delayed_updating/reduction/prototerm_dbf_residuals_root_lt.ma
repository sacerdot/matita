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

include "delayed_updating/syntax/path_root_lt.ma".
include "delayed_updating/reduction/prototerm_dbf_residuals.ma".

(* RESIDUALS OF A SUBSET OF DBF-REDEX POINTERS ******************************)

(* Destructions with rlt ****************************************************)

lemma term_in_dbfr_des_rlt (u) (r) (x):
      x ϵ u /𝐝𝐛𝐟 r → ∨∨ x ϵ u | ⓪r ⊏ ⓪x.
#x #u #r * #s #Hs * *
[ #_ #H0 destruct
  /2 width=1 by or_introl/
| #p #b #q1 #q2 #n #Hr #Hq2 #H1 #H2 destruct
  <path_clear_append <(path_clear_beta_b … (⁤↑n))
  lapply (pxr_des_eq … Hr) -Hr #H0 destruct
  /4 width=3 by path_clear_ppc, path_rlt_mk, or_intror/
]
qed-.
