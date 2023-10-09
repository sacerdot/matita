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

include "ground/notation/functions/hyphen_1.ma".
include "ground/arith/int_split.ma".

(* OPPOSITE FOR INTEGERS ****************************************************)

definition zopp: ℤ → ℤ ≝
           zsplit … zpos (𝟎) zneg.

interpretation
  "opposite (integers)"
  'Hyphen z = (zopp z).

(* Basic constructions ******************************************************)

lemma zopp_neg (p): (⁤p) = -−p.
// qed.

lemma zopp_zero: (𝟎) = -𝟎.
// qed.

lemma zopp_pos (p): −p = -⁤p.
// qed.

(* Advanced constructions ***************************************************)

lemma zopp_opp (z): z = --z.
* //
qed.
