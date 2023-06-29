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

include "ground/relocation/fu/fur_drops_lapp.ma".
include "ground/relocation/fu/fur_nexts_dapp.ma".
include "ground/relocation/fu/fur_lapp_eq.ma".

(* ITERATED DROP FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Constructions with fur_nexts *********************************************)

lemma fur_map_unfold_drops_zero (f):
      ↑*[f＠§❨𝟎❩]⇩*[𝟎]f ≐ f.
#f elim f -f
[| * [| #k ] #f #IH ] //
qed.

lemma pippo (f):
      ∃∃g. ↑*[f＠§❨𝟎❩]𝐢  ≐ g & (⇩*[𝟎]f)●g = f.