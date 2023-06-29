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

include "ground/relocation/fu/fur_pushs_dapp.ma".
include "ground/relocation/fu/fur_nexts.ma".

(* ITERATED NEXT FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Inversions with fur_dapp *************************************************)

lemma fur_dapp_nexts (f) (n) (p):
      f＠⧣❨p❩+n = (↑*[n]f)＠⧣❨p❩.
#f #n #p
<fur_dapp_j_dx //
qed.