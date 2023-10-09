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

include "ground/relocation/fb/fbr_dapp.ma".
include "ground/arith/nat_ppred_psucc.ma".
include "ground/notation/functions/atsection_2.ma".

(* LEVEL APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ***************)

interpretation
  "level application (finite relocation maps with booleans)"
  'AtSection f n = (pnpred (fbr_dapp f (npsucc n))).

(* Basic constructions ******************************************************)

lemma fbr_dapp_succ_lapp (f) (n):
      ↑(f＠§❨n❩) = f＠⧣❨↑n❩.
// qed.

lemma fbr_dapp_lapp (f) (n):
      ↑(f＠§❨↓n❩) = f＠⧣❨n❩.
// qed.

lemma fbr_lapp_pred_dapp (f) (n):
      ↓(f＠⧣❨n❩) = f＠§❨↓n❩.
// qed.

lemma fbr_lapp_id (n):
      n = 𝐢＠§❨n❩.
// qed.

lemma fbr_lapp_push_dx_zero (f):
      (𝟎) = (⫯f)＠§❨𝟎❩.
// qed.

lemma fbr_lapp_push_dx_succ (f) (n):
      (⁤↑(f＠§❨n❩)) = (⫯f)＠§❨⁤↑n❩.
#f #n
<fbr_dapp_push_dx_succ <nsucc_pnpred_swap //
qed.

lemma fbr_lapp_push_dx_pos (f) (p):
      (⁤↑(f＠§❨↓p❩)) = (⫯f)＠§❨⁤p❩.
#f #p
<npsucc_pos <npsucc_pnpred <npsucc_pnpred //
qed.

lemma fbr_lapp_next_dx (f) (n):
      (⁤↑(f＠§❨n❩)) = (↑f)＠§❨n❩.
// qed.
