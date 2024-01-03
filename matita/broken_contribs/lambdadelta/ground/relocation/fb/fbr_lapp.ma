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
include "ground/arith/nat_pred_succ.ma".
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

(* Basic inversions *********************************************************)

lemma eq_inv_zero_fbr_lapp_push (f) (m):
      (𝟎) = ⫯f＠§❨m❩ → 𝟎 = m.
#f #m
elim (nat_split_zero_pos m) #Hm destruct //
>Hm in ⊢ (%→?); <fbr_lapp_push_dx_pos #H0 destruct
qed-.

lemma eq_inv_succ_fbr_lapp_push (f) (n) (m):
      (⁤↑n) = ⫯f＠§❨m❩ →
      ∧∧ n = f＠§❨⫰m❩ & m ϵ 𝐏.
#f #n #m
elim (nat_split_zero_pos m) #H2m destruct
[ <fbr_lapp_push_dx_zero #H0 destruct
| >H2m in ⊢ (%→?); <fbr_lapp_push_dx_succ #H0
  lapply (eq_inv_nsucc_bi … H0) -H0 #H1m
  /2 width=1 by conj/
]
qed-.
