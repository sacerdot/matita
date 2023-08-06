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
include "ground/arith/nat_psucc.ma".
include "ground/arith/nat_split.ma".
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

lemma fbr_xapp_push_unit (f):
      (⁤𝟏) = (⫯f)＠❨⁤𝟏❩.
// qed.

lemma fbr_xapp_push_succ (f) (p):
      (⁤↑(f＠❨⁤p❩)) = (⫯f)＠❨⁤↑p❩.
// qed.

lemma fbr_next_pos (f) (p):
      (⁤↑(f＠❨⁤p❩)) = (↑f)＠❨⁤p❩.
// qed.
