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

include "ground/relocation/fb/fbr_ctls_xapp.ma".
include "ground/relocation/fb/fbr_ctls_plus.ma".
include "ground/relocation/fb/fbr_after.ma".

(* ITERATED COARSE TAIL FOR FINITE RELOCATION MAPS WITH BOOLEANS ************)

(* Constructions with fbr_after *********************************************)

lemma fbr_ctl_after (g) (f):
      (⫰*[⁤(f＠⧣❨𝟏❩)]g)•(⫰f) = ⫰(g•f).
#g elim g -g //
* #g #IH
[ #f <fbr_after_next_sx <fbr_ctl_next <IH -IH //
| * [| * #f <fbr_after_push_rcons ]
  [ <fbr_dapp_id <fbr_after_id_dx //
  | <fbr_ctl_next <fbr_ctl_next <fbr_dapp_next_dx >npsucc_pos //
  | <fbr_ctl_push <fbr_ctl_push <fbr_dapp_push_dx_unit //
  ]
]
qed.

lemma fbr_ctls_after (n) (g) (f):
      (⫰*[f＠❨n❩]g)•(⫰*[n]f) = ⫰*[n](g•f).
#n @(nat_ind_succ … n) -n //
#n #IH #g #f
<fbr_ctls_succ_swap <fbr_ctls_succ_swap <fbr_ctl_after <IH -IH
>fbr_ctls_plus >nplus_unit_dx <fbr_xapp_plus <nplus_comm //
qed.
