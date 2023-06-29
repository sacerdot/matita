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

include "ground/relocation/fu/fur_after.ma".
include "ground/relocation/fu/fur_nexts_dapp.ma".

(* COMPOSITION FOR FINITE RELOCATION MAPS FOR UNWIND ************************)

(* Constructions with fur_dapp **********************************************)

lemma fur_dapp_after_aux (h) (f) (g) (p):
      (∀f,p. g＠⧣❨f＠⧣❨p❩❩ = (h g f)＠⧣❨p❩) →
      (⫯g)＠⧣❨f＠⧣❨p❩❩ = (g•[h]f)＠⧣❨p❩.
#h #f elim f -f //
* [| #k ] #f #IH #g #p #Hh
[ -IH <fur_after_aux_p_dx
  cases p -p [| #p ] //
  <fur_dapp_p_dx_succ <fur_dapp_p_dx_succ //
| <fur_after_aux_j_dx <fur_dapp_j_dx <fur_dapp_j_dx
  <IH -IH //
]
qed.

lemma fur_dapp_after (g) (f) (p):
      g＠⧣❨f＠⧣❨p❩❩ = (g•f)＠⧣❨p❩.
#g elim g -g //
* [| #k ] #g #IH #f #p
[ /2 width=1 by fur_dapp_after_aux/
| <fur_after_j_sn <fur_dapp_j_dx
  <IH -IH //
]
qed.
