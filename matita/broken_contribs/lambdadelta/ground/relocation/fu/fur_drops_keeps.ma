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

include "ground/relocation/fu/fur_drops.ma".
include "ground/relocation/fu/fur_keeps.ma".

(* ITERATED DROP FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Constructions with fur_keeps *********************************************)

lemma fur_map_unfold_keeps_drops (f) (n):
      (⇩*[n]f)●(⇧*[n]f) = f.
#f elim f -f //
* [| #k ] #f #IH #n
[ cases n //
  #p <(IH (↓p)) in ⊢ (???%); -IH //
| <(IH (n+k)) in ⊢ (???%); -IH //
]
qed.
