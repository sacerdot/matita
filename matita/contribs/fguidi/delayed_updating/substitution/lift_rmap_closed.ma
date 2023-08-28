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
include "delayed_updating/syntax/path_closed.ma".

(* LIFT MAP FOR PATH ********************************************************)

(* Destructions with cpp ****************************************************)

(* TODO
lemma lift_rmap_unfold_d_dx (f) (p) (k) (h):
      (🠢[p]f)＠⧣❨h+k❩-(🠢[p]f)＠⧣❨k❩ = (🠢[p◖𝗱k]f)＠⧣❨h❩.
// qed.
*)

lemma ctls_plus_lift_rmap_closed (f) (q) (n):
      q ϵ 𝐂❨n❩ →
      ∀m. ⫰*[m]f = ⫰*[m+n]🠢[q]f.
#f #q #n #Hq elim Hq -q -n //
#q #n #k #_ #IH #m
<lift_rmap_d_dx >fbr_ctls_plus //
qed.

lemma ctls_lift_rmap_closed (f) (q) (n):
      q ϵ 𝐂❨n❩ →
      f = ⫰*[n]🠢[q]f.
#f #q #n #H0
/2 width=1 by ctls_plus_lift_rmap_closed/
qed-.

lemma ctls_succ_lift_rmap_append_L_closed_dx (f) (p) (q) (n):
      q ϵ 𝐂❨n❩ →
      (🠢[p]f) = ⫰*[⁤↑n]🠢[p●𝗟◗q]f.
#f #p #q #n #Hq
/3 width=1 by ctls_lift_rmap_closed, pcc_L_sn/
qed-.
