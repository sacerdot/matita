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

include "ground/relocation/fu/fur_dapp.ma".
include "ground/arith/nat_plus_rplus.ma".
include "ground/arith/nat_ppred_succ.ma".
include "ground/notation/functions/atsection_2.ma".

(* LEVEL APPLICATION FOR FINITE RELOCATION MAPS FOR UNWIND ******************)

interpretation
  "level application (finite relocation maps for unwind)"
  'AtSection f n = (pnpred (fur_dapp f (npsucc n))).

(* Basic constructions ******************************************************)

lemma fur_dapp_succ_lapp (f) (n):
      ↑(f＠§❨n❩) = f＠⧣❨↑n❩.
// qed.

lemma fur_dapp_lapp (f) (n):
      ↑(f＠§❨↓n❩) = f＠⧣❨n❩.
// qed.

lemma fur_lapp_pred_dapp (f) (n):
      ↓(f＠⧣❨n❩) = f＠§❨↓n❩.
// qed.

lemma fur_lapp_id (n):
      n = 𝐢＠§❨n❩.
// qed.

lemma fur_lapp_p_dx_zero (f):
      (𝟎) = (⫯f)＠§❨𝟎❩.
// qed.

lemma fur_lapp_p_dx_succ (f) (n):
      (⁤↑(f＠§❨n❩)) = (⫯f)＠§❨⁤↑n❩.
#f #n
<fur_dapp_p_dx_succ <nsucc_pnpred_swap //
qed.

lemma fur_lapp_p_dx_pos (f) (p):
      (⁤↑(f＠§❨↓p❩)) = (⫯f)＠§❨⁤p❩.
#f #p
<npsucc_pos <npsucc_pnpred <npsucc_pnpred //
qed.

lemma fur_lapp_j_dx (f) (n) (m):
      f＠§❨m+n❩ = (⮤*[n]f)＠§❨m❩.
// qed.
