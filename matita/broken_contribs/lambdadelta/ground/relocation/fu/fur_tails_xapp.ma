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

include "ground/relocation/fu/fur_tails.ma".
include "ground/relocation/fu/fur_xapp.ma".
include "ground/arith/nat_minus_plus.ma".

(* ITERATED TAIL FOR FINITE RELOCATION MAPS FOR UNWIND **********************)

(* Constructions with fur_xapp **********************************************)

lemma fur_dapp_plus_xapp_dx (f) (n) (p):
      (⫰*[n]f)＠⧣❨p❩+f＠❨n❩ = f＠⧣❨p+n❩.
#f * //
elim f -f //
* [| #k ] #f #IH #q #p
[ <fur_tails_pos_p_dx
  cases q -q [| #q ]
  [ <fur_tails_zero //
  | >npsucc_pos <nrplus_succ_dx
    <fur_dapp_p_dx_succ <IH -IH //
  ]
| <fur_tails_pos_j_dx <fur_dapp_j_dx >nrplus_plus_assoc <nplus_pos_sn
   <IH -IH <fur_xapp_j_dx_succ //
]
qed.

lemma fur_xapp_plus (f) (m) (n):
      (⫰*[n]f)＠❨m❩+f＠❨n❩ = f＠❨m+n❩.
#f * //
qed.

lemma fur_xapp_tails (f) (m) (n):
      f＠❨m+n❩-f＠❨n❩ = (⫰*[n]f)＠❨m❩.
// qed.
