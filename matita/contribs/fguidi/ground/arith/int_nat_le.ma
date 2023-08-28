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

include "ground/arith/int_nat.ma".
include "ground/arith/int_le.ma".

(* NATURAL INTEGERS *********************************************************)

(* Constractions with zle ***************************************************)

lemma zle_zero_nat (n):
      (𝟎) ≤ ⊕n.
* //
qed.