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

include "ground/relocation/fb/fbr_coafter.ma".
include "ground/relocation/fb/fbr_after.ma".

(* CO-COMPOSITION FOR FINITE RELOCATION MAPS WITH BOOLEANS ******************)

(* Main constructions with fbr_after ****************************************)

theorem fbr_coafter_after_sx (h) (g) (f):
        h~•(g~•f) = (h•g)~•f.
#h elim h -h //
* #h #IH
[ #g #f
  <fbr_coafter_next_sx <fbr_coafter_next_sx //
| * // * #g * // [|*: #bf #f ]
  <fbr_coafter_push_rcons <fbr_after_push_rcons //
  <fbr_coafter_next_sx <IH -IH //
]
qed.
