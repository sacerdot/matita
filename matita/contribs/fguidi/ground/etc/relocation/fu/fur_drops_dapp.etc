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
include "ground/relocation/fu/fur_dapp.ma".

(* ITERATED DROP FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Constructions with fur_dapp **********************************************)

lemma fur_dapp_drops_unit (f) (n):
      (𝟏) = (⇩*[n]f)＠⧣❨𝟏❩.
#f elim f -f //
* [| #k ] #f #IH //
* //
qed.
