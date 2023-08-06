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
include "ground/arith/nat_split.ma".
include "ground/notation/functions/at_2.ma".

(* EXTENDED DEPTH APPLICATION FOR FINITE RELOCATION MAPS FOR UNWIND *********)

definition fur_xapp (f) (n): ℕ ≝
           nsplit … (𝟎) (λp.(⁤f＠⧣❨p❩)) n
.

interpretation
  "extended depth application (finite relocation maps for unwind)"
  'At f n = (fur_xapp f n).

(* Basic constructions ******************************************************)

lemma fur_xapp_zero (f):
      (𝟎) = f＠❨𝟎❩.
// qed.

lemma fur_xapp_pos (f) (p):
      (⁤f＠⧣❨p❩) = f＠❨⁤p❩.
// qed.

lemma fur_xapp_j_dx_pos (f) (k) (p):
      f＠❨⁤(p+k)❩ = (⮤*[k]f)＠❨⁤p❩.
// qed.

lemma fur_xapp_j_dx_succ (f) (k) (n:ℕ):
      f＠❨⁤↑(n+k)❩ = (⮤*[k]f)＠❨⁤↑n❩.
#f #k #n
<fur_xapp_j_dx_pos //
qed.
