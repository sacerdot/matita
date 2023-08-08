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

include "ground/relocation/fb/fbr_minus.ma".
include "ground/relocation/fb/fbr_coafter.ma".
include "ground/relocation/fb/fbr_after.ma".

(* SUBTRACTION FOR FINITE RELOCATION MAPS WITH BOOLEANS *********************)

(* Constructions with fbr_coafter and fbr_after *****************************)

lemma fbr_minus_coafter_dx_refl_sn (g) (f):
      g = g-(g~•f).
#g elim g -g //
* #g #IH #f
[ <fbr_coafter_next_sn <fbr_minus_next_push <IH -IH //
| cases f -f // #b #f
  <fbr_coafter_push_rcons <fbr_minus_push_rcons <IH -IH //
]
qed.

theorem fbr_after_minus_dx (g) (f) (r):
        (g•f)-(g~•r) = g•(f-r).
#g elim g -g //
* #g #IH #f #r
[ <fbr_after_next_sn <fbr_after_next_sn <fbr_coafter_next_sn
  <fbr_minus_next_push //
| cases f -f // #bf #f <fbr_after_push_rcons
  cases r -r // #br #r
  <fbr_bext_rcons_bi <fbr_bext_rcons_bi <fbr_after_push_rcons //
]
qed.
