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

include "ground/relocation/fu/fur_height_nexts.ma".
include "ground/relocation/fu/fur_after.ma".

(* HEIGHT FOR FINITE RELOCATION MAPS FOR UNWIND *****************************)

(* Constructions with fur_after *********************************************)

lemma fur_height_after_aux (h) (f) (g):
      (∀f. ♯g+♯f = ♯(h g f)) →
      ♯g+♯f = ♯(g•[h]f).
#h #f elim f -f //
* [| #k ] #f #IH #g #Hh
[ <fur_after_aux_p_dx //
| <fur_after_aux_j_dx <fur_height_j_dx <fur_height_j_dx
  <nplus_succ_dx <IH -IH //
]
qed.

lemma fur_height_after (g) (f):
      ♯g+♯f = ♯(g•f).
#g elim g -g //
* [| #k ] #g #IH #f
[ /2 width=1 by fur_height_after_aux/
| <fur_after_j_sn <fur_height_j_dx <IH -IH
  <fur_height_nexts //
]
qed.
