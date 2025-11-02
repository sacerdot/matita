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

include "ground/subsets/subset_listed_1.ma".
include "ground/subsets/subset_listed_2.ma".
include "delayed_updating/syntax/path_clear_proper.ma".
include "delayed_updating/reduction/prototerm_reducible_le.ma".
include "delayed_updating/reduction/path_dbf_residuals.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Constructions with subset_le *********************************************)

lemma path_dbfr_le_repl (t1) (t2) (s) (r):
      t1 ⊆ t2 → (s /𝐝𝐛𝐟{t1} r) ⊆ (s /𝐝𝐛𝐟{t2} r).
#t1 #t2 #s #r #Ht12 #x * *
[ #Hnsr #H0 destruct
  /2 width=1 by path_dbfr_neq/
| #p #b #q #q0 #n #Hr #Hq0 #Hs #Hx destruct
  /3 width=6 by path_dbfr_side, xprc_le_repl/
]
qed.

lemma path_dbfr_neq_le (t) (s) (r):
      s ⧸= r → ❴s❵ ⊆ (s /𝐝𝐛𝐟{t} r).
#t #s #r #Hs #x #Hx
>(subset_in_inv_single ??? Hx) -x
/2 width=1 by path_dbfr_neq/
qed.

lemma path_dbfr_side_le (t) (x) (r) (p) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → x ϵ 𝐏 →
      let s ≝ (⓪p)◖𝗦●(⓪x) in
      ❴s,r●⓪x❵ ⊆ (s /𝐝𝐛𝐟{t} r).
#t #x #r #p #b #q #n #Hr #Hx #y #H0
elim (subset_in_inv_pair ???? H0) -H0 #H0 destruct
[ lapply (xprc_des_r … Hr) -Hr #H0 destruct
  @path_dbfr_neq_le [| // ] <path_clear_beta
  @(path_neq_p_beta ???? (𝐞))
| /3 width=4 by path_dbfr_side, path_clear_ppc/
]
qed.

(* Inversions with subset_le ************************************************)

lemma path_dbfr_le_refl (t) (r):
      (r /𝐝𝐛𝐟{t} r) ⊆ Ⓕ.
#t #r #s #Hs
elim (path_dbfr_inv_refl … Hs)
qed.
