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

include "ground/arith/int_le_plus.ma".
include "ground/arith/int_lt.ma".

(* STRICT ORDER FOR INTEGERS ************************************************)

(* Constructions with zplus *************************************************)

lemma zlt_plus_dx_bi (z) (z1) (z2):
      z1 < z2 → z1 + z < z2 + z.
/3 width=1 by zle_plus_dx_bi/
qed.

lemma zlt_minus_zero (z1) (z2):
      z1 < z2 → z1-z2 < 𝟎.
/2 width=1 by zlt_plus_dx_bi/
qed.

lemma zlt_zero_minus (z1) (z2):
      z1 < z2 → 𝟎 < z2-z1.
#z1 #z2 #Hz
lapply (zlt_plus_dx_bi (-z1) … Hz) -Hz //
qed.
