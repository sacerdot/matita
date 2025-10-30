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

include "delayed_updating/substitution/lift_rmap.ma".
include "delayed_updating/syntax/path_closed_clear.ma".
include "ground/relocation/fb/fbr_rconss_ctls.ma".
include "ground/relocation/fb/fbr_rconss_xapp.ma".

(* LIFT MAP FOR PATH ********************************************************)

(* Destructions with cpp ****************************************************)

lemma lift_rmap_closed_des_gen (f) (q) (n):
      q ϵ 𝐂❨n❩ → ⫯*[n]f = 🠢[q]f.
#f #q #n #Hq elim Hq -q -n //
#q #n #_ #IH
<fbr_rconss_succ //
qed-.

lemma ctls_lift_rmap_closed (f) (q) (n):
      q ϵ 𝐂❨n❩ →
      f = ⫰*[n]🠢[q]f.
#f #q #n #Hq
<(lift_rmap_closed_des_gen … Hq) -q //
qed-.

lemma ctls_succ_plus_lift_rmap_append_clear_L_closed_dx (f) (b) (q) (n):
      q ϵ 𝐂❨n❩ → f = ⫰*[⁤↑(♭b+n)]🠢[⓪b●𝗟◗q]f.
#f #b #q #n #Hq
>nplus_succ_dx
/4 width=1 by ctls_lift_rmap_closed, pcc_append_bi, pcc_L_sx/
qed-.

lemma lift_rmap_closed_xapp_le (f) (q) (n) (m):
      q ϵ 𝐂❨n❩ → m ≤ n → m = (🠢[q]f)＠❨m❩.
#f #q #n #m #Hq #Hmn
<(lift_rmap_closed_des_gen … Hq) -q
/2 width=1 by fbr_xapp_pushs_le/
qed-.

lemma lift_rmap_append_L_closed_dx_xapp_succ (f) (p) (q) (n):
      q ϵ 𝐂❨n❩ → (⁤↑n) = (🠢[p●𝗟◗q]f)＠❨⁤↑n❩.
#f #p #q #n #Hq
<lift_rmap_append <lift_rmap_closed_xapp_le
/2 width=3 by pcc_L_sx, nle_refl/
qed-.

lemma lift_rmap_append_clear_L_closed_dx_xapp_succ_plus (f) (b) (q) (n):
      q ϵ 𝐂❨n❩ → (⁤↑(♭b+n)) = (🠢[⓪b●𝗟◗q]f)＠❨⁤↑(♭b+n)❩.
#f #b #q #n #Hq
@lift_rmap_closed_xapp_le
[1,2: /3 width=3 by pcc_append_bi, pcc_L_sx/
| //
]
qed-.
