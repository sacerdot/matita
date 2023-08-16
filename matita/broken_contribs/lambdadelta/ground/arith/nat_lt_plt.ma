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

include "ground/arith/nat_lt.ma".
include "ground/arith/nat_le_ple.ma".
include "ground/arith/pnat_lt.ma".

(* STRICT ORDER FOR NON-NEGATIVE INTEGERS ***********************************)

(* Constructions with plt ***************************************************)

lemma nlt_pos_bi (p1) (p2):
      p1 < p2 → (⁤p1) < (⁤p2).
/2 width=1 by nle_pos_bi/
qed.

lemma nlt_zero_pos (p):
      (𝟎) < (⁤p).
/2 width=1 by nle_pos_bi/
qed.
