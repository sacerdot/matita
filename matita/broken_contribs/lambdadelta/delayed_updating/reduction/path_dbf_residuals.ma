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

include "ground/xoa/ex_3_5.ma".
include "ground/subsets/subset_listed.ma".
include "delayed_updating/reduction/prototerm_reducible.ma".
include "delayed_updating/notation/functions/slash_dbf_3.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

definition path_dbfr (t) (r) (s0): 𝒫❨ℙ❩ ≝
           {s | ∨∨ ∧∧ s0 ⧸= r & s0 = s
                 | ∃∃p,b,q,q0,n. r ϵ 𝐑❨t,p,b,q,n❩ &
                                 (⓪p)●𝗦◗q0 = s0 & r◖𝗱𝟎●q0 = s
           }.

interpretation
  "residuals of a dbf-redex pointer (path)"
  'SlashDBF t s r = (path_dbfr t r s).

(* Basic constructions ******************************************************)

lemma path_dbfr_neq (t) (r) (s):
      s ⧸= r → s ϵ s /𝐝𝐛𝐟{t} r.
/4 width=1 by or_introl, conj/
qed.

lemma path_dbfr_side (t) (r) (p) (q0) (b) (q) (n):
      r ϵ 𝐑❨t,p,b,q,n❩ →
      r◖𝗱𝟎●q0 ϵ ((⓪p)●𝗦◗q0) /𝐝𝐛𝐟{t} r.
/3 width=8 by ex3_5_intro, or_intror/
qed.

(* UPDATE *)
lemma path_dbfr_side_old (t) (p) (q0) (b) (q) (n):
      ⊗b ϵ 𝐁 → q ϵ 𝐂❨n❩ → (p●𝗔◗b●𝗟◗q)◖𝗱(⁤↑n) ϵ t →
      ⓪(p●𝗔◗b●𝗟◗q)◖𝗱𝟎●q0 ϵ ((⓪p)●𝗦◗q0) /𝐝𝐛𝐟{t} ⓪(p●𝗔◗b●𝗟◗q).
/3 width=4 by path_dbfr_side, xprc_mk/
qed.

(* Basic inversions *********************************************************)

lemma path_dbfr_inv_refl (t) (r) (s):
      s ⧸ϵ r /𝐝𝐛𝐟{t} r.
#t #r #s * *
[ #H0 #_ -s elim H0 -H0 //
| #p #b #q #q0 #n #Hr #H0 #_ destruct
  lapply (xprc_des_r … Hr) -Hr
  <path_clear_append <path_clear_A_sn #H0
  lapply (eq_inv_list_append_dx_bi … H0) -H0 #H0
  elim (eq_inv_list_rcons_bi ????? H0) -H0 #_ #H0 destruct
]
qed-.

lemma path_dbfr_inv_refl_dx (t) (r) (s):
      r ⧸ϵ s /𝐝𝐛𝐟{t} r.
#t #r #s * *
[ /2 width=1 by/
| #p #b #q #q0 #n #_ #_ -t -s -p -b -q -n
  >list_append_rcons_sn #H0
  lapply (eq_inv_list_append_dx_dx_refl … (sym_eq … H0)) -H0 #H0
  lapply (eq_inv_list_empty_rcons ??? H0) -H0 //
]
qed-.
