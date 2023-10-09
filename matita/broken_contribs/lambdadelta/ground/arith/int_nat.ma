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

include "ground/notation/functions/zeroplus_1.ma".
include "ground/arith/nat.ma".
include "ground/arith/int.ma".

(* NATURAL INTEGERS *********************************************************)

definition znat (n): ℤ ≝
match n with
[ nzero   ⇒ 𝟎
| npos  p ⇒ (⁤p)
].

interpretation
  "naturals (integers)"
  'ZeroPlus n = (znat n).

(* Basic constructions ******************************************************)

lemma znat_zero:
      (𝟎) = ⊕𝟎.
// qed.

lemma znat_pos (p):
      (⁤p) = ⊕(⁤p).
// qed.
