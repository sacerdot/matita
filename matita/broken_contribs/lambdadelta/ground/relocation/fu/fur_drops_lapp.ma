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
include "ground/relocation/fu/fur_lapp.ma".

(* ITERATED DROP FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Constructions with fur_lapp **********************************************)

lemma fur_dapp_plus_lapp_dx (f) (n) (p):
      (⇩*[n]f)＠⧣❨p❩+f＠§❨n❩ = f＠⧣❨p+n❩.
#f elim f -f //
* [| #k ] #f #IH
[ * [| #q ] // #p
  <fur_drops_pos_p_dx <fur_lapp_p_dx_pos
  >(npsucc_pnpred q) in ⊢ (???%); <nrplus_succ_dx in ⊢ (???%);
  <fur_dapp_p_dx_succ
  <IH -IH <nrplus_succ_dx //
| #n #p
  <fur_drops_j_dx <fur_lapp_j_dx <fur_dapp_j_dx
  >nrplus_plus_assoc <IH -IH //
]
qed.
