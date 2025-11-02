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

include "ground/xoa/ex_4_5.ma".
include "ground/subsets/subset_listed.ma".
include "delayed_updating/syntax/path_proper.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/notation/functions/slash_dbf_3.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Note: residuals of s with resprct to r ϵ 𝐑❨t❩ *)
definition path_dbfr (t) (r) (s): 𝒫❨ℙ❩ ≝
           {y | ∨∨ ∧∧ s ⧸= r & s = y
                 | ∃∃p,b,q,x,n. r ϵ 𝐑❨t,p,b,q,n❩ &
                                x ϵ 𝐏 & (⓪p)◖𝗦●x = s & r●x = y
           }.

interpretation
  "residuals of a dbf-redex pointer (path)"
  'SlashDBF t s r = (path_dbfr t r s).

(* Basic constructions ******************************************************)

lemma path_dbfr_neq (t) (r) (s):
      s ⧸= r → s ϵ s /𝐝𝐛𝐟{t} r.
/4 width=1 by or_introl, conj/
qed.

lemma path_dbfr_side (t) (r) (p) (x) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ → x ϵ 𝐏 →
      r●x ϵ ((⓪p)◖𝗦●x) /𝐝𝐛𝐟{t} r.
/3 width=9 by ex4_5_intro, or_intror/
qed.

(* UPDATE *)
lemma path_dbfr_side_old (t) (p) (x) (b) (q) (n):
      ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ → 𝐫❨p,b,q,⁤↑n❩ ϵ t → x ϵ 𝐏 →
      (⓪𝐫❨p,b,q,⁤↑n❩)●x ϵ ((⓪p)◖𝗦●x) /𝐝𝐛𝐟{t} ⓪𝐫❨p,b,q,⁤↑n❩.
/3 width=4 by path_dbfr_side, xprc_mk/
qed.

(* Basic inversions *********************************************************)

lemma path_dbfr_inv_refl (t) (r) (s):
      s ⧸ϵ r /𝐝𝐛𝐟{t} r.
#t #r #s * *
[ #H0 #_ -s elim H0 -H0 //
| #p #b #q #x #n #Hr #_ #H0 #_ destruct
  lapply (xprc_des_r … Hr) -Hr <path_clear_beta #H0
  @(path_neq_p_beta … (𝐞) … (sym_eq … H0))
]
qed-.

lemma path_dbfr_inv_refl_dx (t) (r) (s):
      r ⧸ϵ s /𝐝𝐛𝐟{t} r.
#t #r #s * *
[ /2 width=1 by/
| #p #b #q #x #n #_ #Hx #_ #H0 -t -s -p -b -q -n
  lapply (eq_inv_list_append_dx_dx_refl … (sym_eq … H0)) -H0 #H0 destruct
  /2 width=1 by ppc_inv_empty/
]
qed-.
