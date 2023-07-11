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

include "ground/relocation/fu/fur_tails_xapp.ma".
include "ground/relocation/fu/fur_nexts_dapp.ma".
include "ground/relocation/fu/fur_eq.ma".

(* ITERATED TAIL FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Constructions with fur_nexts *********************************************)

lemma fur_nexts_xapp_tails (f) (n):
      (⮤*[n]f) ≐ ↑*[f＠❨n❩]⫰*[n]f.
// qed.
