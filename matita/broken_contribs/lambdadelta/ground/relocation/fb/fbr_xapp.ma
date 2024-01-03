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
include "ground/notation/functions/at_2.ma".

(* EXTENDED DEPTH APPLICATION FOR FINITE RELOCATION MAPS WITH BOOLEANS ******)

definition fbr_xapp (f) (n): ℕ ≝
           nsplit … (𝟎) (λp.(⁤(f＠⧣❨p❩))) n.

interpretation
  "extended depth application (finite relocation maps for unwind)"
  'At f n = (fbr_xapp f n).

(* Basic constructions ******************************************************)

lemma fbr_xapp_zero (f):
      (𝟎) = f＠❨𝟎❩.
// qed.

lemma fbr_xapp_pos (f) (p):
      (⁤(f＠⧣❨p❩)) = f＠❨⁤p❩.
// qed.

(* Advanced constructions ***************************************************)

lemma fbr_xapp_id (n):
      n = 𝐢＠❨n❩.
* //
qed.

lemma fbr_xapp_push_unit (f):
      (⁤𝟏) = (⫯f)＠❨⁤𝟏❩.
// qed.

lemma fbr_xapp_push_succ (f) (n):
      (⁤↑(f＠❨n❩)) = (⫯f)＠❨⁤↑n❩.
#f * //
qed.

lemma fbr_xapp_next_pos (f) (p):
      (⁤↑(f＠❨⁤p❩)) = (↑f)＠❨⁤p❩.
// qed.

(* Basic inversions *********************************************************)

lemma eq_inv_unit_fbr_xapp_push (f) (m):
      (⁤𝟏) = ⫯f＠❨m❩ → (⁤𝟏) = m.
#f #m
elim (nat_split_zero_pos m) #Hm destruct //
>Hm in ⊢ (%→?); <fbr_xapp_pos #H0
lapply (eq_inv_npos_bi … H0) -H0 #H0
>(eq_inv_unit_fbr_dapp_push … H0) -H0 //
qed-.

(* Basic destructions *******************************************************)

lemma eq_des_succ_fbr_xapp (f) (n) (m):
      (⁤↑n) = f＠❨m❩ → m ϵ 𝐏.
#f #n #m #Hm
elim (nat_split_zero_pos m) #H0 // destruct
<fbr_xapp_zero in Hm; #H0 destruct
qed-.
