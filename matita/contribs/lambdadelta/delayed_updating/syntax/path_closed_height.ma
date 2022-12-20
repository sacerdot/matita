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

include "delayed_updating/syntax/path_closed.ma".
include "delayed_updating/syntax/path_height.ma".
include "delayed_updating/syntax/path_depth.ma".

(* CLOSED CONDITION FOR PATH ************************************************)

(* Destructions with height and depth ***************************************)

lemma path_closed_des_depth (o) (e) (q) (n):
      q ϵ 𝐂❨o,n,e❩ → ♯q + n = ♭q + e.
#o #e #q #n #Hq elim Hq -q -n //
#q #n #_ #IH
<nplus_succ_dx <nplus_succ_sn //
qed-.

lemma path_closed_des_succ_zero_depth (o) (q) (n):
      q ϵ 𝐂❨o,↑n,𝟎❩ → ♭q = ↑↓♭q.
#o #q #n #Hq
>(nplus_zero_dx (♭q))
<(path_closed_des_depth … Hq) -Hq
<nplus_succ_dx <npred_succ //
qed-.
