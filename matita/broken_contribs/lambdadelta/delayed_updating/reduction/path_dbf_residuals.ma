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
include "delayed_updating/syntax/path_depth.ma".
include "delayed_updating/syntax/path_clear_proper.ma".
include "delayed_updating/syntax/path_beta_clear.ma".
include "delayed_updating/reduction/prototerm_x_redex.ma".
include "delayed_updating/notation/functions/slash_dbf_2.ma".

(* RESIDUALS OF A DBF-REDEX POINTER *****************************************)

(* Note: residuals of s with respect to r *)
(* Note: we are asuming s and r are redexes of a preterm *)
definition path_dbfr (r) (s): 𝒫❨ℙ❩ ≝
           {y | ∨∨ ∧∧ s ⧸= r & s = y
                 | ∃∃p,b,q,x,n. r ϵ 𝐑❨p,b,q,n❩ &
                                x ϵ 𝐏 & p◖𝗦●x = s &
                                (𝐫❨p,⓪b,q,⁤↑(♭b+n)❩●x = y)
           }.

interpretation
  "residuals of a dbf-redex pointer (path)"
  'SlashDBF s r = (path_dbfr r s).

(* Basic const tructions ******************************************************)

lemma path_dbfr_neq (r) (s):
      s ⧸= r → s ϵ s /𝐝𝐛𝐟 r.
/4 width=1 by or_introl, conj/
qed.

lemma path_dbfr_side (r) (p) (x) (b) (q) (n):
      r ϵ 𝐑❨p,b,q,n❩ → x ϵ 𝐏 →
      (𝐫❨p,⓪b,q,⁤↑(♭b+n)❩●x) ϵ (p◖𝗦●x) /𝐝𝐛𝐟 r.
/3 width=9 by ex4_5_intro, or_intror/
qed.

(* Basic inversions *********************************************************)

lemma path_dbfr_inv_refl (r) (s):
      s ⧸ϵ r /𝐝𝐛𝐟 r.
#r #s * *
[ /2 width=1 by/
| #p #b #q #x #n #Hr #_ #H0 #_ destruct
  lapply (pxr_des_eq … Hr) -Hr #H0
  @(path_neq_p_beta … (𝐞) … (sym_eq … H0))
]
qed-.

lemma path_dbfr_inv_refl_dx (r) (s):
      r ⧸ϵ s /𝐝𝐛𝐟 r.
#r #s * *
[ /2 width=1 by/
| #p #b #q #x #n #Hr #Hx #_ #H0 -s
  lapply (pxr_des_eq … Hr) -Hr #Hr destruct
  lapply (eq_f … path_clear … Hr) -Hr
  <path_clear_append <(path_clear_beta_b … (⁤↑n)) #H0
  lapply (eq_inv_list_append_dx_dx_refl … H0) -p -b -q -n #H0
  /3 width=3 by path_clear_ppc, ppc_inv_empty/
]
qed-.
