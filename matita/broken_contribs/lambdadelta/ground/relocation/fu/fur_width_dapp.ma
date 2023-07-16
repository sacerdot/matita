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

include "ground/relocation/fu/fur_width.ma".
include "ground/relocation/fu/fur_depth.ma".
include "ground/relocation/fu/fur_dapp.ma".
include "ground/arith/nat_le_rplus.ma".
include "ground/arith/nat_plus_rplus.ma".

(* WIDTH FOR FINITE RELOCATION MAPS FOR UNWIND ******************************)

(* Constructions with fur_depth and fur_dapp ********************************)

lemma fur_dapp_depth_gt (f) (p):
      ↑♭f ≤ p → p+↕f = f＠⧣❨p❩.
#f elim f -f //
* [| #k ] #f #IH
[ * [ -IH #H0 | #p #Hp ]
  [ elim (ple_inv_succ_unit … H0)
  | lapply (ple_inv_succ_bi … Hp) -Hp #Hp
    <nrplus_succ_sn <fur_dapp_p_dx_succ <IH -IH //
  ]
| #p #Hp
  <fur_dapp_j_dx <IH -IH
  /2 width=1 by ple_nrplus_dx_dx/
]
qed-.
